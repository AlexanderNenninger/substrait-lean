"""The parser reads a call's options as the plan states them (#1484).

`Write.roundtrips` (the CLI's own check) shows `parse (write r) = r`: the
writer loses nothing. It says nothing about whether `parse` reads the input
JSON faithfully, and a name-level comparison of a plan with its written form
is noise, since the writer rewrites calls (`gt` to `lt`, `is_not_null` to
`not(is_null)`, `between` to `not`/`lt`). What the JSON side can check without
a second parser is each option: for a call of every function that reads
options, and every option value Substrait's YAMLs or the model name, the checker
either refuses the plan or writes the value back; a value the parser reads as
another one shows as a collapse, two values written alike while a third is
written apart.
"""

import collections
import json
import subprocess

from sverify._checker import checker_path
from sverify._unsupported import UnsupportedError
from sverify.engine import written_plan
from sverify.ibis_substrait import to_substrait
from sverify_dev.coverage import CASES

CALLS = ("scalarFunction", "aggregateFunction", "windowFunction")


def walk(x):
    if isinstance(x, dict):
        yield x
        for v in x.values():
            yield from walk(v)
    elif isinstance(x, list):
        for v in x:
            yield from walk(v)


def names(plan: dict) -> dict[int, str]:
    return {
        e["extensionFunction"]["functionAnchor"]: e["extensionFunction"]["name"].split(":")[0]
        for e in plan.get("extensions", [])
        if "extensionFunction" in e
    }


def calls(plan: dict) -> list[tuple[str, dict]]:
    """Every call of the plan, with its function's name."""
    by_anchor = names(plan)
    return [
        (by_anchor.get(f["functionReference"], "?"), f)
        for node in walk(plan.get("relations"))
        for key in CALLS
        if (f := node.get(key)) is not None
    ]


def stated(plan: dict) -> collections.Counter:
    """The options the plan's calls state: (function, option, preference) counts."""
    return collections.Counter(
        (name, o["name"], tuple(o.get("preference", [])))
        for name, f in calls(plan)
        for o in f.get("options", [])
    )


def checker_options() -> tuple[dict[str, set[str]], dict[str, set[str]]]:
    """The options each function reads (any of its constructors), and the
    values each option has (the model's and the YAMLs')."""
    exe = str(checker_path())
    functions = json.loads(
        subprocess.run([exe, "--functions"], capture_output=True, text=True, check=True).stdout
    )
    options = json.loads(
        subprocess.run([exe, "--options"], capture_output=True, text=True, check=True).stdout
    )["options"]
    # Options with no Substrait name are sverify's own: a plan cannot state them.
    options = [o for o in options if o["substrait"] is not None]
    ident = {o["id"]: o for o in options}
    reads: dict[str, set[str]] = collections.defaultdict(set)
    for fn in functions:
        for opt in fn["options"]:
            if opt in ident:
                reads[fn["name"]].add(ident[opt]["substrait"])
    values = {
        o["substrait"]: set(o["core"]) | {e[0] for e in o["extra"]} | set(o["yaml"])
        for o in options
    }
    return reads, values


def base_calls() -> dict[tuple[str, str], tuple[dict, int]]:
    """One call of each function and output kind, from the plans of the
    coverage cases, with the plan the checker writes for it."""
    found: dict[tuple[str, str], tuple[dict, int]] = {}
    for case in CASES:
        try:
            plan = json.loads(written_plan(json.dumps(to_substrait(case.build()))))
        except Exception:  # noqa: BLE001 - a case the producer or the checker refuses
            continue
        for index, (name, f) in enumerate(calls(plan)):
            kind = next(iter(f.get("outputType", {"?": 0})))
            found.setdefault((name, kind), (plan, index))
    return found


def collapses(written: dict[str, str], default: str) -> list[list[str]]:
    """The accepted values the checker writes alike while it writes another
    apart, and the values written as the base call when more than one is: the
    parser reads them as one value. `default` is the base call as written (it
    may state the option itself), which at most one value can stand for."""
    groups = collections.defaultdict(list)
    for value, text in written.items():
        groups[text].append(value)
    out = [vs for vs in groups.values() if len(vs) > 1] if len(groups) > 1 else []
    as_default = [v for v, text in written.items() if text == default]
    return out + ([as_default] if len(as_default) > 1 and as_default not in out else [])


#: Triples (function, output kind, option) whose option changes nothing: the
#: choice of `on_domain_error` for an integer `power` is `any` (`Options.lean`,
#: group `int.pow`; the producer states no output type on it, kind `?`), so
#: every value is accepted and written as the base call. The float `power` is
#: not in the set: there the option matters.
NO_EFFECT = {("power", "?", "on_domain_error")}


def test_a_collapse_is_two_values_written_alike_beside_another():
    assert collapses({"A": "x", "B": "x", "C": "y"}, "z") == [["A", "B"]]
    assert collapses({"A": "x", "B": "y", "C": "z"}, "w") == []
    # An option the call does not read: every value is written alike.
    assert collapses({"A": "x", "B": "x"}, "w") == []
    # Two values read as the default, with two values only.
    assert collapses({"A": "d", "B": "d"}, "d") == [["A", "B"]]
    assert collapses({"A": "d", "B": "y"}, "d") == []


def with_option(plan: dict, index: int, option: str, value: str) -> dict:
    """The plan with its `index`-th call stating `option` as `[value]`."""
    out = json.loads(json.dumps(plan))
    f = calls(out)[index][1]
    f["options"] = [o for o in f.get("options", []) if o["name"] != option] + [
        {"name": option, "preference": [value]}
    ]
    return out


def test_every_option_value_is_refused_or_written_back():
    """What it checks: of the values of an option a call reads, those the
    checker accepts are written as different plans, at most one of them as the
    plan without the option (the default), and a value the written plan states
    is stated as itself. What it cannot see: an option with one accepted value
    (the others refused: most options, 44 of 65 triples of function, kind and
    option), an option the writer drops while the plan differs from the default
    (the writer rewrites some calls, `divide` with `NULL` for one), and a value
    the parser reads as another in a way the written plan does not show."""
    reads, values = checker_options()
    wrong, accepted = [], 0
    calls_ = base_calls()
    # The coverage cases reach most of the functions that read options.
    assert len({n for n, _ in calls_} & set(reads)) >= 30
    for (name, kind), (plan, index) in sorted(calls_.items()):
        default = json.dumps(json.loads(written_plan(json.dumps(plan))), sort_keys=True)
        for option in sorted(reads.get(name, ())):
            written: dict[str, str] = {}
            for value in sorted(values.get(option, ())):
                try:
                    out = written_plan(json.dumps(with_option(plan, index, option, value)))
                except UnsupportedError:
                    continue
                accepted += 1
                written[value] = json.dumps(json.loads(out), sort_keys=True)
                # A value the plan states is written back as itself.
                for (_, o, pref), _ in (stated(json.loads(out)) - stated(plan)).items():
                    if o == option and pref != (value,):
                        wrong.append(f"{name}({kind}) {option}={value} is written as {pref}")
            if (name, kind, option) not in NO_EFFECT:
                wrong += [
                    f"{name}({kind}) {option}: {vs} are written alike"
                    for vs in collapses(written, default)
                ]
    assert accepted
    assert not wrong, "\n".join(wrong)
