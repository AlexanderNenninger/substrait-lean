"""How a verified plan reaches an engine (#444, decisions D10, D13 and D14
of `docs/core-semantics.md`).

A plan runs on the engine `E` by one of four routes, tried in this order:

1. `"native"`: it was verified under `Profile.E` (`verify(semantics=E)`).
2. `"reference"`: it was verified under the reference, and runs through
   the translation from the reference to `E` (`TRANSLATIONS`).
3. `"transfer"`: it was verified under another profile `P`, and for every
   option the proof depends on (`Report.depends`), `E`'s choices are within
   `P`'s: the proof holds under `Profile.E` as it is (`Rel.AllowedP_mono`,
   option by option). A table lookup, `transfer`.
4. `"recheck"`: the checker proves the contract again under `Profile.E`.

Otherwise the plan is refused on `E`, with the reason. A function `E` does
not run (`sverify._support`, #271) refuses the plan on every route.
`choose` picks the route; `sv.Report.run(con, engine, route="auto")` runs
by it, checks the preconditions on the data first (`Report.check_inputs`),
and records the route in `Report.routes`. An explicit route
(`route="transfer"`) is taken or refused, never replaced by another.

Each route carries the plan's class on `E` (#568): `refines`,
`refines_up_to` an observation, `approx`, `shim` or `refused`, the worst
over the options the proof depends on, from the class, `q` and shim columns
of `E`'s choices (D15). An option `E` realizes only up to its observation
`q` needs a postcondition whose observation `q` refines (`sv.equivalent`,
D18), or the row's shim; otherwise the plan is refused there.

A routed run also reads the engine's settings (DuckDB's
`current_setting`, Polars's engine affinity) and compares them with those
the profile's facts were probed under (`check_settings`): a setting a
choice-table row depends on refuses the run (`EngineSettingsError`),
another warns (`EngineSettingsWarning`).

Each engine profile records the engine versions its facts were probed at
(`PROFILES`, D14). A run on another version warns
(`EngineVersionWarning`); a run on another major version is refused
(`EngineVersionError`) until the probes are re-run.

A plan whose result is not determined up to row order
(`Report.deterministic`) is reported by default, and refused where a rerun
must give the same result: `choose(..., deterministic=True)`, for
incremental refreshes and idempotent sinks (D10).
"""

from __future__ import annotations

import functools
import json
import warnings
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Any, Literal

from sverify import _plan_read

if TYPE_CHECKING:
    from sverify.contracts import Report
    from sverify.observation import Observation

RouteKind = Literal["native", "reference", "transfer", "recheck"]
Class = Literal["refines", "refines_up_to", "approx", "shim", "refused"]
Evidence = Literal["proved", "tested"]
#: The classes, best first (#568): a plan takes the worst of its options'.
CLASSES: tuple[Class, ...] = ("refines", "refines_up_to", "approx", "shim", "refused")
#: The routes, in the order `choose` tries them.
ROUTES: tuple[RouteKind, ...] = ("native", "reference", "transfer", "recheck")


@dataclass(frozen=True)
class EngineProfile:
    """An engine's profile, as far as routes need it."""

    engine: str
    versions: tuple[str, ...]
    """The engine versions the profile's facts were probed at
    (`characterization/<engine>/facts/`)."""


#: The engine profiles, where the checker reports none (`substrait-check
#: --options`, "profiles"). The versions are the facts' `engine_version`.
PROFILES: Mapping[str, EngineProfile] = {
    "duckdb": EngineProfile("duckdb", ("2.0.0",)),
    "polars": EngineProfile("polars", ("2.1.0",)),
}

#: The translation from the reference to each engine, with what makes it
#: sound.
TRANSLATIONS: Mapping[str, str] = {
    "duckdb": "proved once: the DuckDB lowering (Lowering.lower_correct) and its writer",
    "polars": "sverify.polars_engine's shims to the reference, tested against Rel.eval",
    "datafusion": "the SQL writer's shims to the reference, tested against Rel.eval",
    "spark": "the Spark SQL writer's shims to the reference, tested against Rel.eval",
}


class EngineVersionWarning(UserWarning):
    """The engine's version is not one its profile's facts were probed at,
    but the major version is the same (D14)."""


class EngineVersionError(RuntimeError):
    """The engine's major version differs from the one its profile's facts
    were probed at: re-run the probes (`characterization/<engine>/`) first
    (D14)."""


class EngineSettingsWarning(UserWarning):
    """An engine setting differs from its profile's, where only behaviour
    sverify does not rely on changes."""


class EngineSettingsError(RuntimeError):
    """An engine setting a profile's choices depend on differs from the
    value its facts were probed under: restore it, or re-run the probes
    under it."""


class RouteError(ValueError):
    """No route takes the plan to the engine; `route` says why."""

    def __init__(self, route: Route):
        super().__init__(f"refused on {route.engine}: {route.reason}")
        self.route = route


@dataclass(frozen=True)
class Route:
    """How a plan reaches an engine (`choose`), or why it does not."""

    engine: str
    kind: RouteKind | None
    """The route taken; None when the plan is refused."""
    profile: str
    """The profile the proof the run relies on is under: the engine's own
    for `"native"`, `"transfer"` and `"recheck"`, `"reference"` for
    `"reference"`; for a refusal, the profile the plan was verified under."""
    reason: str
    """Why this route, or why none."""
    deterministic: bool = True
    """Whether the plan's result is determined up to row order
    (`Report.deterministic`)."""
    warnings: tuple[str, ...] = ()
    """What the run should know: another engine version, an open choice in
    the output."""
    failures: tuple[dict, ...] = field(default=(), compare=False)
    """For a failed transfer check: the options where the engine's choices
    are not within the profile's, as `{"group", "option", "from", "to",
    "facts"}`."""
    cls: Class | None = None
    """The plan's class on the engine (#568, "Classes of an engine's
    functions" in `docs/core-semantics.md`): the worst over the options the
    proof depends on, `"refused"` for a refusal. None where the checker's
    tables give no class for those options."""
    evidence: Evidence | None = None
    """`"proved"` where every option's class is proved in Lean, `"tested"`
    where one rests on a test or a probe; None where the tables say nothing."""
    shims: tuple[str, ...] = ()
    """The shims the translation writes for this plan, by option."""

    @property
    def refused(self) -> bool:
        return self.kind is None

    def __str__(self) -> str:
        head = "refused" if self.kind is None else self.kind
        out = f"{head}: {self.reason}"
        if self.cls is not None and self.kind is not None:
            out += f" [{self.cls}" + (f", {self.evidence}" if self.evidence else "") + "]"
        if not self.deterministic:
            out += " (the result is not determined up to row order)"
        return out


# -- engine versions (D14) ----------------------------------------------------


def installed_version(engine: str) -> str | None:
    """The version of `engine` this process runs, None if it has no profile
    or is not installed."""
    try:
        if engine == "duckdb":
            import duckdb

            return duckdb.__version__
        if engine == "polars":
            import polars

            return polars.__version__
    except ImportError:
        return None
    return None


def _major(v: str) -> str:
    return v.removeprefix("py-").removeprefix("v").split(".")[0]


def check_version(engine: str, version: str | None = None) -> str | None:
    """Check `engine`'s version (the installed one by default) against its
    profile's (D14).

    Returns:
        A warning when the version differs within the major version, also
        issued as an `EngineVersionWarning`; None when it is one the facts
        were probed at, or the engine has no profile.

    Raises:
        EngineVersionError: The major version differs.
    """
    prof = profiles().get(engine)
    if prof is None or not prof.versions:
        return None
    version = version or installed_version(engine)
    if version is None or version in prof.versions:
        return None
    probed = ", ".join(prof.versions)
    if all(_major(version) != _major(v) for v in prof.versions):
        raise EngineVersionError(
            f"{engine} {version} is another major version than Profile.{engine}'s facts, "
            f"probed at {probed}: re-run the probes (characterization/{engine}/) first"
        )
    msg = (
        f"{engine} {version} is not a version Profile.{engine}'s facts were probed at "
        f"({probed}); they may no longer hold"
    )
    warnings.warn(msg, EngineVersionWarning, stacklevel=3)
    return msg


def check_settings(engine: str, values: Mapping[str, Any] | None = None) -> list[str]:
    """Check the settings of `engine` the next run will see (or `values`)
    against those its profile's facts were probed under
    (`sverify._engine_settings`).

    Returns:
        A warning per setting that differs where nothing sverify relies on
        changes, also issued as an `EngineSettingsWarning`.

    Raises:
        EngineSettingsError: A setting a choice-table row depends on
            differs; the message names it.
    """
    from sverify import _engine_settings

    found = _engine_settings.differences(engine, values)
    refused = [_engine_settings.describe(engine, s, v) for s, v in found if s.action == "refuse"]
    if refused:
        raise EngineSettingsError(
            "; ".join(refused) + ": restore the setting, or re-run the probes under it"
        )
    notes = [_engine_settings.describe(engine, s, v) for s, v in found]
    for n in notes:
        warnings.warn(n, EngineSettingsWarning, stacklevel=3)
    return notes


# -- the choices tables -------------------------------------------------------


def _table(flag: str) -> Any:
    """A table the checker prints (`substrait-check --options`); None when
    this checker has no such flag."""
    import subprocess

    from sverify.engine import checker_path

    try:
        out = subprocess.run(
            [str(checker_path()), flag], capture_output=True, text=True, check=True, timeout=60
        ).stdout
        return json.loads(out)
    except (OSError, subprocess.SubprocessError, json.JSONDecodeError):
        return None


@functools.cache
def _options_json() -> dict:
    found = _table("--options")
    return found if isinstance(found, dict) else {}


@functools.cache
def _functions_json() -> list[dict]:
    found = _table("--functions")
    return found if isinstance(found, list) else []


def profiles() -> dict[str, EngineProfile]:
    """The engine profiles: the checker's (`--options`, "profiles") over
    `PROFILES`."""
    out = dict(PROFILES)
    for name, p in (_options_json().get("profiles") or {}).items():
        if isinstance(p, dict) and p.get("engine"):
            out[name] = EngineProfile(p["engine"], tuple(p.get("versions") or ()))
    return out


Allowed = frozenset[str] | None
"""The behaviours a profile allows at an option; None: every behaviour."""


def _allowed(choice: Mapping[str, Any]) -> Allowed:
    kind = choice.get("kind")
    if kind == "any":
        return None
    if kind == "asked":
        # A plan that states no preference gets the default; a stated one is
        # the same in both profiles where both support it.
        return frozenset(choice.get("default") or ())
    return frozenset(choice.get("behaviours") or ())


def choices(profile: str) -> dict[tuple[str | None, str], tuple[Allowed, tuple[str, ...]]] | None:
    """A profile's choices by (group, option), each with the facts behind
    it; None when the checker has no table for the profile."""
    rows = (_options_json().get("choices") or {}).get(profile)
    if rows is None:
        return None
    return {
        (r.get("group"), r["option"]): (_allowed(r["choice"]), tuple(r.get("facts") or ()))
        for r in rows
    }


def _lookup(
    table: Mapping[tuple[str | None, str], tuple[Allowed, tuple[str, ...]]],
    group: str | None,
    option: str,
) -> tuple[Allowed, tuple[str, ...]]:
    """The choice at (group, option): the group's row wins over the row for
    every group; without either, the core's, which allows everything."""
    return table.get((group, option)) or table.get((None, option)) or (None, ())


def _groups_of(name: str) -> set[str]:
    """The groups a plan function belongs to, from Lean's function table:
    the double's row for a signature over doubles, else the others."""
    base = _plan_read.base_name(name)
    sig = name.split(":", 1)[1] if ":" in name else ""
    rows = [r for r in _functions_json() if r.get("name") == base]
    fp = "fp" in sig
    narrowed = [r for r in rows if (r.get("reads") == "float") == fp]
    return {r["group"] for r in (narrowed or rows) if r.get("group")}


#: The options of relations, by the relation that meets them.
_RELATION_OPTIONS = {"sort": ("null_order",)}


def plan_options(plan: Any) -> list[dict]:
    """Every option a plan may depend on: those of the groups of the
    functions it calls, and those of its relations. The conservative
    dependency set where the checker reports none."""
    groups_json = _options_json().get("groups") or {}
    fns = _plan_read.function_names(plan)
    out: list[dict] = []
    seen: set[tuple[str | None, str]] = set()

    def add(group: str | None, option: str) -> None:
        if (group, option) not in seen:
            seen.add((group, option))
            out.append({"group": group, "option": option})

    for name in fns.values():
        for g in sorted(_groups_of(name)):
            for o in groups_json.get(g, []):
                add(g, o)

    def walk(node: Any) -> None:
        if isinstance(node, dict):
            for rel, opts in _RELATION_OPTIONS.items():
                if rel in node and isinstance(node[rel], dict):
                    for o in opts:
                        add(None, o)
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)

    walk(plan.get("relations", []) if isinstance(plan, dict) else plan)
    return out


def transfer(source: str, target: str, depends: Sequence[Mapping[str, Any]]) -> list[dict] | None:
    """The option-wise transfer check: does a proof under `source` that
    depends on `depends` hold under `target`?

    Returns:
        The options where `target`'s choices are not within `source`'s, as
        `{"group", "option", "from", "to", "facts"}` (empty: the proof
        transfers); None when the checker has no table for one of the
        profiles.
    """
    p, e = choices(source), choices(target)
    if p is None or e is None:
        return None
    failures = []
    for d in depends:
        g, o = d.get("group"), d["option"]
        a_p, _ = _lookup(p, g, o)
        a_e, facts = _lookup(e, g, o)
        if a_p is None or (a_e is not None and a_e <= a_p):
            continue
        failures.append(
            {
                "group": g,
                "option": o,
                "from": sorted(a_p),
                "to": None if a_e is None else sorted(a_e),
                "facts": list(facts),
            }
        )
    return failures


def _failure_text(f: Mapping[str, Any], source: str, target: str) -> str:
    where = f"{f['group']}'s {f['option']}" if f.get("group") else f["option"]
    to = "any behaviour" if f["to"] is None else ", ".join(f["to"])
    facts = f" ({', '.join(f['facts'])})" if f.get("facts") else ""
    return f"{where}: Profile.{source} gives {', '.join(f['from'])}, {target} gives {to}{facts}"


def lean_transfer(source: str, target: str, depends: Sequence[Mapping[str, Any]]) -> dict | None:
    """The checker's own transfer check (`substrait-check --transfer`), which
    is authoritative (D1): `{"ok": bool, "failures": [...]}`; None where the
    checker has none. `transfer` is the same lookup, done here for speed; a
    test keeps the two in agreement."""
    import subprocess

    from sverify.engine import checker_path

    request = json.dumps({"from": source, "to": target, "depends": list(depends)})
    try:
        out = subprocess.run(
            [str(checker_path()), "--transfer"],
            input=request,
            capture_output=True,
            text=True,
            check=True,
            timeout=60,
        ).stdout
        found = json.loads(out)
    except (OSError, subprocess.SubprocessError, json.JSONDecodeError):
        return None
    if not isinstance(found, dict) or "ok" not in found:
        return None
    failures = found.get("failures")
    if failures is None:
        failures = [found["failure"]] if found.get("failure") else []
    return {"ok": bool(found["ok"]), "failures": failures}


def row(profile: str, group: str | None, option: str) -> dict | None:
    """A profile's row of the choices table at (group, option), the
    group's row over the one for every group; None where it has neither."""
    rows = (_options_json().get("choices") or {}).get(profile) or []
    by_key = {(r.get("group"), r.get("option")): r for r in rows}
    return by_key.get((group, option)) or by_key.get((None, option))


def _where(group: str | None, option: str) -> str:
    return f"{group}'s {option}" if group else option


_KINDS = ("abs", "rel", "ulps")


def _bounds(eps: Mapping[str, Any]) -> dict[str, tuple[float, bool]]:
    """A column's `ε` as `{kind: (value, proved)}`. Each kind is a number or
    `{"value", "proved"}`; `"proved"` beside them is a bool for all of them
    or a mapping per kind. A bound is proved only where Lean marks it so: a
    missing mark means it rests on a test."""
    flag = eps.get("proved", False)
    out: dict[str, tuple[float, bool]] = {}
    for kind in _KINDS:
        v = eps.get(kind)
        if v is None:
            continue
        proved = bool(flag.get(kind, False)) if isinstance(flag, Mapping) else bool(flag)
        if isinstance(v, Mapping):
            proved = bool(v.get("proved", proved))
            v = v.get("value")
            if v is None:
                continue
        out[kind] = (float(v), proved)
    return out


def _plan_bound(
    q: Mapping[str, Any],
    observed: Observation,
    epsilon: Mapping[str, Mapping[str, Any]] | None,
) -> tuple[dict[str, Any], list[str], bool]:
    """`q` without a plan-dependent float bound (`{"floats": {"bound":
    "plan"}}`), the problems with that bound, and whether the bound that
    meets the postcondition rests on an unproved bound.

    The contract's result gives each double output column's `ε`
    (`Report.epsilon`): bounds of several kinds, each of which holds on its
    own. The postcondition's tolerance (`sv.within`) is met when one of
    them is no larger than the stated bound of the same kind (#568's
    propagation, B1)."""
    from sverify.observation import Within

    floats = q.get("floats")
    if not (isinstance(floats, Mapping) and floats.get("bound") == "plan"):
        return dict(q), [], False
    rest = {k: v for k, v in q.items() if k != "floats"}
    if epsilon is None:
        return rest, ["the checker gave no per-plan bound (ε) on the doubles"], False
    stated = observed.floats
    problems = []
    unproved = False
    for col, eps in epsilon.items():
        bounds = _bounds(eps)
        if not any(v for v, _ in bounds.values()):
            continue
        shown = ", ".join(
            f"{k}={v:g}" + ("" if proved else " (not proved)") for k, (v, proved) in bounds.items()
        )
        met = [
            proved
            for k, (v, proved) in bounds.items()
            if isinstance(stated, Within)
            and getattr(stated, k) is not None
            and v <= getattr(stated, k)
        ]
        if not met:
            want = "exact doubles" if not isinstance(stated, Within) else str(stated)
            problems.append(
                f"{col} is within {shown} of the reference, and the postcondition asks {want}"
            )
        elif not any(met):
            unproved = True
    return rest, problems, unproved


def realization(
    engine: str,
    depends: Sequence[Mapping[str, Any]],
    observed: Observation,
    epsilon: Mapping[str, Mapping[str, float]] | None = None,
) -> tuple[Class | None, Evidence | None, tuple[str, ...], list[str]]:
    """How `engine` realizes the reference's choices on the options a plan
    depends on, from the class, `q` and shim columns of its choices rows
    (D15), with the observation the postcondition names (D18, check 1).

    An option whose class is `refines_up_to` or `approx` holds on the engine
    only up to the row's observation `q`: where `q` does not refine the
    postcondition's, the row's shim makes it canonical (class `shim`), or
    the plan is refused there.

    Returns:
        The worst class (None where no row gives one), the evidence, the
        shims written, and the problems that refuse the plan.

    A row whose `q` bounds the doubles per plan (`{"floats": {"bound":
    "plan"}}`, Polars's `sum_order`) is checked against `epsilon`, the
    contract's per-column `ε`.
    """
    from sverify.observation import from_json

    classes: list[Class] = []
    evidence: list[str] = []
    shims: list[str] = []
    problems: list[str] = []
    for d in depends:
        g, o = d.get("group"), d["option"]
        r = row(engine, g, o)
        if r is None or r.get("class") is None:
            continue
        cls: Class = r["class"]
        facts = f" ({', '.join(r['facts'])})" if r.get("facts") else ""
        if cls == "refused":
            problems.append(f"{_where(g, o)} is refused on {engine}{facts}")
        elif cls in ("refines_up_to", "approx") and r.get("q") is not None:
            rest, bounded, untested = _plan_bound(r["q"], observed, epsilon)
            if untested:
                # The bound that meets the tolerance is not proved in Lean.
                r = {**r, "evidence": "tested"}
            q = from_json(rest)
            missed = q.coarser_than(observed)
            if (missed or bounded) and r.get("shim"):
                cls = "shim"
            elif missed:
                problems.append(
                    f"{_where(g, o)}: {engine} agrees with the reference only up to {q}, and "
                    f"the postcondition observes its {', '.join(missed)} ({observed}); state "
                    f"{', '.join(missed)} in sv.equivalent(...) or shim it{facts}"
                )
            problems += [f"{_where(g, o)}: {p}{facts}" for p in bounded if not r.get("shim")]
        if cls == "shim" and r.get("shim"):
            shims.append(f"{_where(g, o)}: {r['shim']}")
        classes.append(cls)
        if r.get("evidence"):
            evidence.append(r["evidence"])
    worst = max(classes, key=CLASSES.index) if classes else None
    ev: Evidence | None = None
    if evidence and len(evidence) == len(classes):
        ev = "tested" if "tested" in evidence else "proved"
    elif evidence:
        ev = "tested"
    return worst, ev, tuple(shims), problems


# -- the re-check -------------------------------------------------------------


def recheck(report: Report, profile: str) -> tuple[bool | None, str]:
    """Prove the report's contract again under `profile`.

    Returns:
        Whether it was proved (None: the checker cannot check under that
        profile), and why in words.
    """
    from sverify.engine import run_checker

    if report.contract is None:
        return None, "the report keeps no contract to check again"
    try:
        code, out, err = run_checker(
            ("--contract",), json.dumps({**report.contract, "profile": profile})
        )
    except Exception as e:  # noqa: BLE001
        return None, f"the checker failed: {e}"
    if code not in (0, 4):
        return None, f"the checker failed: {err.strip()}"
    res = json.loads(out)
    if res.get("profile") != profile:
        return None, f"the checker has no Profile.{profile} to check under yet"
    unproved = [e["name"] for e in res.get("ensures", []) if not e.get("proved")]
    unproved += ["a key" for k in res.get("keys", []) if not k.get("proved")]
    errors = [f"{i['kind']}: {i['expr']}" for i in res.get("issues", []) if i.get("error")]
    if unproved or errors:
        return False, "under Profile.{}: {}".format(
            profile,
            "; ".join([f"not proved: {u}" for u in unproved] + [f"may fail: {e}" for e in errors]),
        )
    return True, f"proved again under Profile.{profile}"


# -- choosing the route (D13) -------------------------------------------------


def engine_name(engine: Any) -> str:
    """An engine's name: a string as given, lower case; any other object
    (a Spark session) is Spark."""
    return engine.lower() if isinstance(engine, str) else "spark"


def _sorted_root(plan: Mapping[str, Any]) -> bool:
    """Whether the plan's result comes out of a sort."""
    for r in plan.get("relations", []):
        rel = (r.get("root") or {}).get("input") or r.get("rel") or {}
        while "project" in rel and "sort" not in rel:
            rel = rel["project"].get("input") or {}
        if "sort" in rel or "fetch" in rel and "sort" in (rel["fetch"].get("input") or {}):
            return True
    return False


def choose(
    report: Report,
    engine: Any,
    route: RouteKind | Literal["auto"] = "auto",
    *,
    deterministic: bool = False,
    version: str | None = None,
) -> Route:
    """The route by which the plan `report` checked reaches `engine` (D13).

    Args:
        report: A report of `sv.verify` (or a transform's `last_report`).
        engine: The engine's name, or a Spark session.
        route: `"auto"` (the default) tries `"native"`, `"reference"`,
            `"transfer"` and `"recheck"` in turn; a route by name is taken or
            refused.
        deterministic: Refuse a plan whose result is not determined up to
            row order, as incremental refreshes and idempotent sinks need
            (D10). By default the route only reports it.
        version: The engine's version; the installed one by default.

    Returns:
        The `Route`, with the plan's class on the engine; refused
        (`Route.refused`) with the reason when no route applies.

    Raises:
        EngineVersionError: The engine's major version is not its profile's.
        EngineSettingsError: A setting the engine's profile depends on
            differs from its facts' (`check_settings`).
        ValueError: `route` is unknown.
    """
    from sverify import _support

    if route != "auto" and route not in ROUTES:
        raise ValueError(f"route must be 'auto' or one of {', '.join(ROUTES)}, not {route!r}")
    e = engine_name(engine)
    notes: list[str] = []
    if w := check_version(e, version):
        notes.append(w)
    notes += check_settings(e)
    source = report.semantics
    det = report.deterministic

    def refuse(reason: str, failures: Sequence[dict] = ()) -> Route:
        return Route(e, None, source, reason, det, tuple(notes), tuple(failures), "refused")

    if not report.proved:
        return refuse(f"the plan is not verified under Profile.{source}")
    if not det:
        hint = "an open choice (ties in an ORDER BY) leaves the result undetermined up to row order"
        if deterministic:
            return refuse(f"{hint}, and a rerun must give the same result")
        notes.append(hint)
    plan = json.loads(report.plan) if report.plan else {}
    if report.observation.rows == "sequence" and not _sorted_root(plan):
        return refuse(
            "the postcondition observes the rows as a sequence, and the plan's result is not sorted"
        )
    try:
        _support.check(plan, e)
    except ValueError as err:
        return refuse(str(err))
    depends = report.depends if report.depends is not None else plan_options(plan)

    def taken(kind: RouteKind, profile: str, reason: str) -> Route:
        if kind != "reference":
            # Verified under the engine's own profile, or transferred to it by
            # monotonicity: every outcome is one the proof covers.
            return Route(e, kind, profile, reason, det, tuple(notes), cls="refines")
        cls, ev, shims, problems = realization(e, depends, report.observation, report.epsilon)
        if problems:
            return refuse("; ".join(problems))
        return Route(e, kind, profile, reason, det, tuple(notes), (), cls, ev, shims)

    tried = ROUTES if route == "auto" else (route,)
    why_not: list[str] = []
    failures: list[dict] = []
    for kind in tried:
        if kind == "native":
            if source == e:
                return taken("native", e, f"verified under Profile.{e}")
            why_not.append(f"not verified under Profile.{e}")
        elif kind == "reference":
            if source == "reference" and e in TRANSLATIONS:
                return taken(
                    "reference",
                    "reference",
                    f"verified under the reference; the translation to {e} is {TRANSLATIONS[e]}",
                )
            why_not.append(
                "not verified under the reference"
                if source != "reference"
                else f"no translation from the reference to {e}"
            )
        elif kind == "transfer":
            if source in ("reference", e):
                why_not.append(f"no transfer from Profile.{source} needed")
                continue
            found = transfer(source, e, depends)
            if found is None:
                why_not.append(
                    f"no choices table for Profile.{source} or Profile.{e} to check a transfer"
                )
            elif not found:
                which = (
                    "" if report.depends is not None else " (every option of the plan's functions)"
                )
                return taken(
                    "transfer",
                    e,
                    f"verified under Profile.{source}; {e}'s choices are within its choices "
                    f"on every option the proof depends on{which}",
                )
            else:
                failures = found
                why_not.append(
                    "the transfer check fails on "
                    + "; ".join(_failure_text(f, source, e) for f in found)
                )
        elif kind == "recheck":
            ok, why = recheck(report, e)
            if ok:
                return taken("recheck", e, why)
            why_not.append(f"no re-check: {why}" if ok is None else why)
    return refuse("; ".join(why_not), failures)
