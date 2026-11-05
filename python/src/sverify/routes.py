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

Each route carries the plan's class on `E` (#568): `exact` (every result
`E` gives is one the reference allows), `observed` (equal to one up to an
observation, `Route.observation`: rows as a multiset, a tolerance on
doubles, …), `shim` or `refused`, the worst over the options the proof
depends on, from the class, observation and shim columns of `E`'s choices
(D15). An option `E` realizes only up to its observation needs a
postcondition whose observation it refines (`sv.equivalent`, D18), or the
row's shim; otherwise the plan is refused there.

A routed run also reads the engine's settings (DuckDB's
`current_setting`, Polars's engine affinity) and compares them with those
the profile's facts were probed under (`check_settings`): a setting a
choice-table row the plan depends on reads refuses the run
(`EngineSettingsError`), unless the plan states the behaviour (a sort's
NULLS LAST); another warns (`EngineSettingsWarning`).

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
from dataclasses import dataclass, field, replace
from typing import TYPE_CHECKING, Any, Literal, NamedTuple

from sverify import _plan_read
from sverify.observation import Observation, Within

if TYPE_CHECKING:
    from sverify.contracts import Report

RouteKind = Literal["native", "reference", "transfer", "recheck"]
#: A route taken, or `"unverified"`: a plan that is not proved, run with
#: `unverified=True`.
Taken = Literal["native", "reference", "transfer", "recheck", "unverified"]
Class = Literal["exact", "observed", "shim", "refused"]
Evidence = Literal["proved", "tested"]
#: The classes, best first (#568): a plan takes the worst of its options'.
CLASSES: tuple[Class, ...] = ("exact", "observed", "shim", "refused")
#: The checker's class names (`substrait-check --options`) as `Class`es:
#: `refines_up_to` an observation and `approx` (a tolerance, which is an
#: observation of doubles) are both `observed`.
_CLASS_NAMES: Mapping[str, Class] = {
    "refines": "exact",
    "exact": "exact",
    "refines_up_to": "observed",
    "approx": "observed",
    "observed": "observed",
    "shim": "shim",
    "refused": "refused",
}


def row_class(r: Mapping[str, Any]) -> Class | None:
    """A choices row's class, by this module's names."""
    c = r.get("class")
    return None if c is None else _CLASS_NAMES[c]


def row_observation(r: Mapping[str, Any]) -> Mapping[str, Any] | None:
    """A choices row's observation, as the checker writes it (`"observation"`,
    or `"q"` from a checker before the rename)."""
    return r.get("observation", r.get("q"))


def row_rerun(r: Mapping[str, Any]) -> Mapping[str, Any] | None:
    """A choices row's run-to-run variation, as an observation
    (`"rerun_observation"`, or `"rerun"` from a checker before the rename)."""
    return r.get("rerun_observation", r.get("rerun"))


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


class UnverifiedRunWarning(UserWarning):
    """A plan that is not proved runs, because the caller passed
    `unverified=True`: nothing the report says holds of its result."""


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
    value its facts were probed under, and the plan relies on it: restore it
    (the message says how), or re-run the probes under it."""


class RouteError(ValueError):
    """No route takes the plan to the engine; `route` says why."""

    def __init__(self, route: Route):
        super().__init__(f"refused on {route.engine}: {route.reason}")
        self.route = route


@dataclass(frozen=True)
class Route:
    """How a plan reaches an engine (`choose`), or why it does not."""

    engine: str
    kind: Taken | None
    """The route taken; `"unverified"` for a plan that is not proved, run
    with `unverified=True`; None when the plan is refused."""
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
    functions" in `docs/core-semantics.md`): `"exact"`, `"observed"` (equal
    to a result the reference allows up to `observation`), `"shim"`, or
    `"refused"` for a refusal; the worst over the options the proof depends
    on. None where the checker's tables give no class for those options."""
    evidence: Evidence | None = None
    """`"proved"` where every option's class is proved in Lean, `"tested"`
    where one rests on a test or a probe; None where the tables say nothing."""
    shims: tuple[str, ...] = ()
    """The shims the translation writes for this plan, by option."""
    reproducible: Observation | None = None
    """What a rerun had to reproduce (D20), where the caller
    required one; the route was refused unless the engine's run-to-run
    variation refines it."""
    rerun_evidence: Evidence | None = None
    """`"proved"` where every option's run-to-run variation is in the
    tables and proved, `"tested"` where one is missing (read as exact) or
    rests on an unproved bound; None without `reproducible`."""
    fallbacks: tuple[str, ...] = ()
    """On Polars, the nodes of the plan's streaming plan that run on the
    in-memory engine (`polars_engine.fallback_nodes`), recorded by
    `Report.run`: the in-memory engine's facts hold for those."""
    observation: Observation | None = None
    """For an `"observed"` route: the observation up to which the engine's
    result equals one the reference allows, the coarsest over the options
    the proof depends on (rows as a multiset, a tolerance on doubles from
    the plan's bound, …). None for the other classes."""
    bound_proved: bool | None = None
    """Whether the tolerance in `observation` rests on a bound Lean proves
    (`Report.epsilon`); False where it rests on a test; None without one."""
    suggested: dict[str, list[str]] = field(default_factory=dict, compare=False)
    """For a refusal, what to declare to make the plan verify, as condition
    labels per input table: an `sv.unique(...)` that determines a result
    with ties, an `sv.max_rows(n)` under which the plan's bound meets a
    tolerance (#655)."""

    @property
    def refused(self) -> bool:
        return self.kind is None

    def __str__(self) -> str:
        head = "refused" if self.kind is None else self.kind
        out = f"{head}: {self.reason}"
        if self.cls is not None and self.kind is not None:
            seen = f" {self.observation}" if self.observation is not None else ""
            out += f" [{self.cls}{seen}" + (f", {self.evidence}" if self.evidence else "") + "]"
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
            f"probed at {probed}: install a {_major(prof.versions[0])}.x release of {engine}; "
            f"running {version} needs its facts probed again (characterization/{engine}/)"
        )
    msg = (
        f"{engine} {version} is not a version Profile.{engine}'s facts were probed at "
        f"({probed}); they may no longer hold"
    )
    warnings.warn(msg, EngineVersionWarning, stacklevel=3)
    return msg


def check_settings(
    engine: str,
    values: Mapping[str, Any] | None = None,
    depends: Sequence[Mapping[str, Any]] | None = None,
) -> list[str]:
    """Check the settings of `engine` the next run will see (or `values`)
    against those its profile's facts were probed under
    (`sverify._engine_settings`).

    Args:
        engine: The engine's name.
        values: The settings to check; the engine's current ones by default.
        depends: The options the plan depends on (`Report.depends`); None
            when unknown, which relies on every setting.

    Returns:
        A warning per setting that differs where the plan relies on nothing
        it changes, also issued as an `EngineSettingsWarning`.

    Raises:
        EngineSettingsError: A setting differs that a choice-table row the
            plan depends on reads; the message says how to restore it.
    """
    from sverify import _engine_settings as es

    found = es.differences(engine, values)
    deps = None if depends is None else [dict(d) for d in depends]
    refused = [(s, v) for s, v in found if s.action == "refuse" and es.relies(s, deps)]
    if refused:
        raise EngineSettingsError(
            "; ".join(
                f"{es.describe(engine, s, v)}, which this plan relies on: restore it "
                f"with `{es.restore(engine, s)}`"
                for s, v in refused
            )
        )
    notes = [
        es.describe(engine, s, v)
        + ("" if s.action == "warn" else "; this plan does not rely on it")
        for s, v in found
    ]
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
    return f"{where}: {source} gives {', '.join(f['from'])}, {target} gives {to}{facts}"


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
    against: str = "of the reference, and the postcondition asks",
    fix: str = (
        "state sv.equivalent(floats={tol}) or looser in ensures, "
        "or sv.equivalent({plan}) for the plan's own bound"
    ),
    held: Mapping[str, str] | None = None,
) -> tuple[dict[str, Any], list[str], bool]:
    """An observation without a plan-dependent float bound (`{"floats": {"bound":
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
        if held and col in held:
            # A postcondition reads the column: it is proved of the
            # reference's exact value, which the engine's is only near.
            shown = ", ".join(f"{k}={v:g}" for k, (v, _) in bounds.items())
            problems.append(
                f"the postcondition {held[col]} reads {col}, which is within {shown} "
                f"{against.split(',')[0]}: write it as sv.approx({held[col]}), or state "
                f"sv.equivalent(floats={_smallest(bounds)}) in ensures"
            )
            continue
        shown = ", ".join(
            f"{k}={v:g}" + ("" if proved else " (tested)") for k, (v, proved) in bounds.items()
        )
        met = [
            proved
            for k, (v, proved) in bounds.items()
            if stated == "plan"
            or isinstance(stated, Within)
            and getattr(stated, k) is not None
            and v <= getattr(stated, k)
        ]
        if not met:
            want = "exact doubles" if not isinstance(stated, Within) else str(stated)
            tol = _smallest(bounds)
            problems.append(
                f"{col} is within {shown} {against} {want}: "
                + fix.format(tol=tol, plan='floats="plan"')
            )
        elif not any(met):
            unproved = True
    return rest, problems, unproved


def _unbounded(eps: Mapping[str, Any]) -> bool:
    """The checker names the column's bounds, and none is finite."""
    return any(k in eps for k in _KINDS) and not _bounds(eps)


def _resolve(observed: Observation, epsilon: Mapping[str, Mapping[str, Any]] | None) -> Observation:
    """`observed` with `floats="plan"` replaced by the plan's bound: per
    kind of bound, the smallest of the double columns' `ε` (every column
    meets it), exact where no column has one. Unchanged where the checker
    gave no `ε`."""
    from sverify.observation import Within

    if observed.floats != "plan" or epsilon is None:
        return observed
    if any(_unbounded(e) for e in epsilon.values()):
        # A column without a bound: the plan's bound is unknown.
        return observed
    found = [_bounds(e) for e in epsilon.values()]
    found = [b for b in found if any(v for v, _ in b.values())]
    if not found:
        return replace(observed, floats="exact")
    kinds = [k for k in _KINDS if all(k in b for b in found)]
    if not kinds:
        return observed
    least = {k: min(b[k][0] for b in found) for k in kinds}
    return replace(
        observed,
        floats=Within(
            least.get("abs"),
            least.get("rel"),
            None if "ulps" not in least else int(least["ulps"]),
        ),
    )


def _smallest(bounds: Mapping[str, tuple[float, bool]]) -> str:
    """The smallest round tolerance a column's `ε` meets, as code."""
    kind = "rel" if "rel" in bounds else next(iter(bounds))
    v = bounds[kind][0]
    # One significant digit, rounded up, so that the bound stays met.
    smallest = float(f"{v:.0e}")
    if smallest < v:
        smallest = float(f"{v * 1.5:.0e}")
    return f"sv.within({kind}={smallest:g})"


def _gives_as_stated(choice: Mapping[str, Any] | None, dep: Mapping[str, Any]) -> bool:
    """Does an engine whose choice is `choice` give the behaviours the plan
    states at `dep` as stated? Only where every read there states one
    (`"stated"`), and the choice delivers the first preference it supports."""
    bs = dep.get("behaviours") or []
    if not dep.get("stated") or not bs or not choice:
        return False
    return choice.get("kind") in ("asked", "oneOf") and all(
        b in (choice.get("behaviours") or []) for b in bs
    )


def realization(
    engine: str,
    depends: Sequence[Mapping[str, Any]],
    observed: Observation,
    epsilon: Mapping[str, Mapping[str, float]] | None = None,
    held: Mapping[str, str] | None = None,
    rows_exact: bool | None = None,
) -> Realized:
    """How `engine` realizes the reference's choices on the options a plan
    depends on, from the class, observation and shim columns of its choices rows
    (D15), with the observation the postcondition names (D18, check 1).

    An option whose class is `"observed"` holds on the engine only up to
    the row's observation: where that does not refine the
    postcondition's, the row's shim makes it canonical (class `shim`), or
    the plan is refused there.

    Returns:
        The worst class (None where no row gives one), the evidence, the
        shims written, the problems that refuse the plan, and, for an
        observed plan, the observation and whether its tolerance is proved.

    A row whose observation bounds the doubles per plan (`{"floats": {"bound":
    "plan"}}`, Polars's `sum_order`) is checked against `epsilon`, the
    contract's per-column `ε`. Where the engine's doubles may differ and
    `rows_exact` is False, a filter, key or sort on them may keep other rows
    than the reference's (#568's threshold rule): the plan is refused there.
    """
    from sverify.observation import from_json

    classes: list[Class] = []
    evidence: list[str] = []
    shims: list[str] = []
    problems: list[str] = []
    seen: list[Observation] = []
    proved: list[bool] = []
    for d in depends:
        g, o = d.get("group"), d["option"]
        r = row(engine, g, o)
        cls = None if r is None else row_class(r)
        if r is None or cls is None:
            continue
        if r.get("shim") and _gives_as_stated(r.get("choice"), d):
            # The plan states the behaviour, and the engine gives it as
            # stated: the shim is for the reference's default (#444, 3b).
            cls = "exact"
        facts = f" ({', '.join(r['facts'])})" if r.get("facts") else ""
        obs = row_observation(r)
        if cls == "refused":
            problems.append(f"{_where(g, o)} is refused on {engine}{facts}")
        elif cls == "observed" and obs is not None:
            rest, bounded, untested = _plan_bound(obs, observed, epsilon, held=held)
            if untested:
                # The bound that meets the tolerance is not proved in Lean.
                r = {**r, "evidence": "tested"}
            q = from_json(rest)
            gives = _with_bound(q, obs, epsilon)
            seen.append(gives)
            if isinstance(gives.floats, Within):
                proved.append(not untested and _all_proved(epsilon))
            missed = q.coarser_than(_resolve(observed, epsilon))
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
    if rows_exact is False and any(x.floats != "exact" for x in seen):
        problems.append(
            f"a filter, grouping key or sort on a double may keep other rows on {engine} than "
            "the reference: its threshold lies within the doubles' bound of their range; "
            "state a precondition that keeps the values away from it, or compare exact columns"
        )
    worst = max(classes, key=CLASSES.index) if classes else None
    ev: Evidence | None = None
    if evidence and len(evidence) == len(classes):
        ev = "tested" if "tested" in evidence else "proved"
    elif evidence:
        ev = "tested"
    gives = None
    if worst == "observed" and seen:
        gives = seen[0]
        for x in seen[1:]:
            gives = _coarsest(gives, x)
    return Realized(worst, ev, tuple(shims), problems, gives, all(proved) if proved else None)


class Realized(NamedTuple):
    """How an engine realizes a plan's options (`realization`)."""

    cls: Class | None
    evidence: Evidence | None
    shims: tuple[str, ...]
    problems: list[str]
    observation: Observation | None = None
    bound_proved: bool | None = None


def _with_bound(
    q: Observation, raw: Mapping[str, Any], epsilon: Mapping[str, Any] | None
) -> Observation:
    """A row's observation with a per-plan bound on doubles written out as
    the tolerance the plan's `ε` gives (the largest over its columns)."""
    from sverify.observation import Within

    floats = raw.get("floats")
    if not (isinstance(floats, Mapping) and floats.get("bound") == "plan"):
        return q
    found = [_bounds(e) for e in (epsilon or {}).values()]
    found = [b for b in found if any(v for v, _ in b.values())]
    kinds = [k for k in _KINDS if found and all(k in b for b in found)]
    if not kinds:
        return replace(q, floats="plan")
    most = {k: max(b[k][0] for b in found) for k in kinds}
    ulps = None if "ulps" not in most else int(most["ulps"])
    return replace(q, floats=Within(most.get("abs"), most.get("rel"), ulps))


def _all_proved(epsilon: Mapping[str, Any] | None) -> bool:
    return bool(epsilon) and all(
        all(p for _, p in _bounds(e).values()) for e in (epsilon or {}).values()
    )


def _coarsest(a: Observation, b: Observation) -> Observation:
    """The coarser of two observations on each component."""
    from sverify.observation import _COMPONENTS

    out = {}
    for name, levels in _COMPONENTS:
        x, y = getattr(a, name), getattr(b, name)
        if name == "floats":
            out[name] = y if replace(a, floats=x).coarser_than(replace(a, floats=y)) == [] else x
        else:
            out[name] = max(x, y, key=levels.index)
    return Observation(**out)


def observed(report: Report) -> tuple[Observation, dict[str, str]]:
    """What a run checks the engine's result against: the observation
    `ensures` names, or else rows as a multiset, doubles within the plan's
    bound (`Report.epsilon`) and other values exact (`PLAN_BOUND`), with
    the double columns a postcondition reads held to their exact value
    (by column, the postcondition's label): a condition proved of the
    reference's value need not hold of a value near it."""
    from sverify.observation import PLAN_BOUND

    if report.stated:
        return report.observation, {}
    held: dict[str, str] = {}
    doubles = [c for c, t in report.output.items() if getattr(t, "is_floating", bool)()]
    for c in report.ensures:
        if c.approx or not c.proved:
            continue
        for col in doubles if c.reads is None else c.reads:
            if col in doubles:
                held.setdefault(col, c.label)
    return PLAN_BOUND, held


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


def max_rows_fix(report: Report, engine: str, required: Observation | None) -> dict[str, list[str]]:
    """The `sv.max_rows(N)` under which the plan's bound on its doubles
    (`Report.epsilon`) meets the tolerance `required` states, by the input
    table that has a row cap now: the bound grows linearly with the rows,
    so `N` is the cap scaled by the tightest ratio of tolerance to bound
    (#655). Empty where there is no stated tolerance, no single capped
    input, or the bound already meets it; `sv.max_rows(0)` where no cap
    does."""
    from sverify.contracts import MaxRows

    if required is None or not isinstance(required.floats, Within) or not report.epsilon:
        return {}
    caps = {t: c.n for t, cs in report.conditions.items() for c in cs if isinstance(c, MaxRows)}
    if len(caps) != 1:
        return {}
    ((table, n0),) = caps.items()
    ratio = None
    for eps in report.epsilon.values():
        bounds = _bounds(eps)
        met = False
        best = 0.0
        for k, (v, _p) in bounds.items():
            tol = getattr(required.floats, k)
            if tol is None or not v:
                continue
            if v <= tol:
                met = True
            best = max(best, tol / v)
        if met or not bounds or not any(v for v, _ in bounds.values()):
            continue
        ratio = best if ratio is None else min(ratio, best)
    if ratio is None:
        return {}
    n = int(n0 * ratio)
    return {table: [f"max_rows({n})"]}


def _cap_text(found: Mapping[str, list[str]]) -> str:
    """The sentence for a row cap `max_rows_fix` found."""
    for t, labs in found.items():
        for lab in labs:
            if lab.startswith("max_rows("):
                n = int(lab[len("max_rows(") : -1])
                if n < 1:
                    return f"; no row cap on {t} makes the plan's bound meet the tolerance"
                return f"; or declare sv.max_rows({n:_}) on {t}, under which the bound meets it"
    return ""


def ties_fix(report: Report) -> str:
    """How to make the report's result determined up to row order: the
    `sv.unique(...)` it needs (`Report.ties`), or `TIES`."""
    if not report.ties:
        return TIES

    def code(lab: str) -> str:
        cols = lab.removeprefix("unique(").removesuffix(")").split(", ")
        return f"sv.unique({', '.join(repr(c) for c in cols)})"

    parts = [f"{', '.join(map(code, labs))} on {t}" for t, labs in report.ties.items()]
    return "declare " + " and ".join(parts) + " in requires, so no rows tie in the ORDER BY"


#: How to make a result determined up to row order.
TIES = (
    "declare `unique(...)` on the partition (or grouping) and order columns of the input, "
    "or give first(), last() and windows a total order"
)


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


def reproducibility(
    report: Report,
    engine: str,
    required: Observation,
    depends: Sequence[Mapping[str, Any]] | None = None,
) -> tuple[list[str], Evidence]:
    """Whether a rerun of the plan on `engine` reproduces its result up to
    `required` (what a rerun must reproduce, D20).

    The result must be determined up to row order (`Report.deterministic`):
    an open choice in it (ties in an ORDER BY, a LIMIT without one) fails
    every requirement. Then, on each option the plan depends on, the
    engine's run-to-run variation (the `"rerun_observation"` column of its
    choices, `"rerun"` from an older checker, component
    levels as in an observation, `{}` where it is exact; `{"floats": {"bound":
    "plan"}}` for a summation order that varies between runs, bounded by the
    plan's `ε`) must refine `required`. The evidence is the row's
    `"rerun_evidence"`: "tested" unless it says "proved". A row without the
    column is read as exact, on the evidence of a test.

    Returns:
        The problems (empty: reproduced), and the evidence.
    """
    from sverify.observation import from_json

    problems: list[str] = []
    if not report.deterministic:
        problems.append(
            "the result is not determined up to row order (ties in an ORDER BY, or a LIMIT "
            "without one), so no rerun is sure to reproduce it"
        )
    if depends is None:
        depends = (
            report.depends
            if report.depends is not None
            else plan_options(json.loads(report.plan) if report.plan else {})
        )
    tested = False
    for d in depends:
        g, o = d.get("group"), d["option"]
        r = row(engine, g, o)
        varied = None if r is None else row_rerun(r)
        if r is None or varied is None:
            tested = True
            continue
        rest, bounded, unproved = _plan_bound(
            varied,
            required,
            report.epsilon,
            "between runs, and a rerun must reproduce",
            "pass reproducible=sv.equivalent(floats={tol}) or looser, "
            "or sv.equivalent({plan}) (the sinks' default) for the plan's own bound",
        )
        # The row's own evidence for its variation (`{}` where it is known
        # exact); the class's evidence says nothing about reruns.
        tested = tested or unproved or r.get("rerun_evidence") != "proved"
        varies = from_json(rest)
        missed = varies.coarser_than(_resolve(required, report.epsilon))
        if missed:
            unknown = (
                "; the checker gives no bound on the plan's doubles: bound the inputs "
                "(a range, and sv.max_rows) or pass "
                "reproducible=sv.equivalent(floats=sv.within(...))"
                if "floats" in missed and _resolve(required, report.epsilon).floats == "plan"
                else ""
            )
            problems.append(
                f"{_where(g, o)}: two runs on {engine} agree only up to {varies}, and a rerun "
                f"must reproduce its {', '.join(missed)} ({required}){unknown}"
            )
        problems += [f"{_where(g, o)}: {p}" for p in bounded]
    return problems, "tested" if tested else "proved"


def verified(report: Report) -> bool:
    """Whether a run may take the plan: it is proved (`Report.proved`), or
    its only unproved postconditions are checked on the output data
    (`on_unproved="runtime"`)."""
    if report.proved:
        return True
    return (
        not report.errors
        and not report.transfer
        and not report.needed
        and all(c.portable or c.checked for c in report.ensures)
    )


def not_verified(report: Report) -> str:
    """Why a plan is not verified, in the user's terms: each runtime error
    that may happen and each postcondition that is not proved, with where
    the report keeps them, and how to run it anyway."""
    parts = [f"may fail: {i}" for i in report.errors]
    see = ["report.errors"] if report.errors else []
    for c in report.ensures:
        if c.portable or c.checked:
            continue
        if not c.proved:
            parts.append(f"ensures {c.label} is not proved: {c.why}")
        else:
            from sverify import observation as _observation

            parts.append(f"ensures {c.label} {_observation.why(c.ignores)}")
        if "report.unproved" not in see:
            see.append("report.unproved")
    parts += [f"needs {n}" for n in report.needs_lines()]
    if report.needed:
        see.append("report.needed")
    if report.transfer:
        parts.append(
            "the reference's proof does not carry over to Substrait's semantics on "
            + ", ".join(_where(f.get("group"), f["option"]) for f in report.transfer)
        )
        see.append("report.transfer")
    where = f" (see {', '.join(see)})" if see else ""
    return (
        "not verified: "
        + "; ".join(parts or ["the report is not proved"])
        + where
        + "; run(..., unverified=True) runs it anyway"
    )


def unverified(report: Report, engine: Any) -> Route:
    """The route of a plan that is not proved, run with `unverified=True`:
    no proof reaches the engine, and the reason says what was not proved."""
    e = engine_name(engine)
    reason = not_verified(report).removesuffix("; run(..., unverified=True) runs it anyway")
    return Route(e, "unverified", report.semantics, reason, report.deterministic)


def choose(
    report: Report,
    engine: Any,
    route: RouteKind | Literal["auto"] = "auto",
    *,
    deterministic: bool = False,
    version: str | None = None,
    reproducible: Observation | None = None,
) -> Route:
    """The route by which the plan `report` checked reaches `engine` (D13).

    Args:
        report: A report of `sv.verify` (or a transform's `last_report`).
        engine: The engine's name, or a Spark session.
        route: `"auto"` (the default) tries `"native"`, `"reference"`,
            `"transfer"` and `"recheck"` in turn; a route by name is taken or
            refused.
        deterministic: Require a rerun to reproduce the result exactly, rows
            as a multiset: `reproducible=sv.equivalent()` (D10).
        reproducible: What a rerun must reproduce (D20), as an
            idempotent sink needs: the engine's run-to-run variation must
            refine it (`reproducibility`), or the route is refused. None
            (the default) reports determinism and checks nothing.
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
    plan = json.loads(report.plan) if report.plan else {}
    depends = report.depends if report.depends is not None else plan_options(plan)
    notes += check_settings(e, depends=depends)
    source = report.semantics
    det = report.deterministic

    def refuse(reason: str, failures: Sequence[dict] = ()) -> Route:
        return Route(e, None, source, reason, det, tuple(notes), tuple(failures), "refused")

    if not verified(report):
        return refuse(not_verified(report))
    if deterministic and reproducible is None:
        from sverify.observation import Observation as _Observation

        reproducible = _Observation()
    rerun_evidence: Evidence | None = None
    if reproducible is not None:
        problems, rerun_evidence = reproducibility(report, e, reproducible)
        if problems:
            ties = "" if det else f"; {ties_fix(report)}"
            cap = max_rows_fix(report, e, reproducible)
            return replace(
                refuse(
                    "a rerun must give the same result: "
                    + "; ".join(problems)
                    + ties
                    + _cap_text(cap)
                ),
                suggested={**report.ties, **cap},
                reproducible=reproducible,
                rerun_evidence=rerun_evidence,
            )
    if not det:
        notes.append(
            "an open choice (ties in an ORDER BY) leaves the result undetermined up to row order"
        )
    if report.observation.rows == "sequence" and not _sorted_root(plan):
        return refuse(
            "the postcondition observes the rows as a sequence, and the plan's result is not sorted"
        )
    try:
        _support.check(plan, e)
    except ValueError as err:
        return refuse(str(err))

    def taken(kind: RouteKind, profile: str, reason: str) -> Route:
        if kind != "reference":
            # Verified under the engine's own profile, or transferred to it by
            # monotonicity: every outcome is one the proof covers.
            return Route(
                e,
                kind,
                profile,
                reason,
                det,
                tuple(notes),
                cls="exact",
                reproducible=reproducible,
                rerun_evidence=rerun_evidence,
            )
        seen, held = observed(report)
        got = realization(e, depends, seen, report.epsilon, held, (report.rows_exact or {}).get(e))
        if got.problems:
            cap = max_rows_fix(report, e, seen)
            return replace(refuse("; ".join(got.problems) + _cap_text(cap)), suggested=cap)
        return Route(
            e,
            kind,
            profile,
            reason,
            det,
            tuple(notes),
            (),
            got.cls,
            got.evidence,
            got.shims,
            reproducible,
            rerun_evidence,
            observation=got.observation,
            bound_proved=got.bound_proved,
        )

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
    if route == "auto" and source not in ("reference", e) and e in TRANSLATIONS:
        # Lead with what the user can do: the reference reaches every engine.
        lead = (
            f"verify with semantics='reference' to run on {e} (the plan was verified with "
            f"semantics={source!r}, whose proof does not carry over to {e})"
        )
        return refuse(f"{lead}; details: " + "; ".join(why_not), failures)
    return refuse("; ".join(why_not), failures)
