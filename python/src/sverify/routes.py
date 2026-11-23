"""How a verified plan reaches an engine: determinism, choosing the route
and engine versions, as `docs/core-semantics.md` states them.

A plan runs on the engine `E` by one of four routes, tried in this order:

1. `"native"`: it was verified under `Profile.E` (`verify(semantics=E)`).
2. `"translated"`: it was verified under the reference, and runs through
   the translation from the reference to `E` (`_engines.translations()`).
3. `"transfer"`: it was verified under another profile `P`, and at every
   option the plan reads, `E`'s choices are within `P`'s: the proof holds
   under `Profile.E` as it is. The checker decides it (`transferB`, proved
   sound by `Rel.transfer_of_transferB`) in its verdict on `E`.
4. `"recheck"`: the checker proves the contract again under `Profile.E`.

Otherwise the plan is refused on `E`, with the reason. A function `E` does
not run (`sverify._support`) refuses the plan on every route.
`choose` picks the route; `sv.Report.run(con, engine, route="auto")` runs
by it, checks the preconditions on the data first (`Report.check_inputs`),
and records the route in `Report.routes`. An explicit route
(`route="transfer"`) is taken or refused, never replaced by another.

Each route carries the plan's class on `E`: `exact` (every result
`E` gives is one the reference allows), `observed` (equal to one up to an
observation, `Route.lenses`: rows as a multiset, a tolerance on
doubles, …), `shim` or `refused`, the worst over the options the proof
depends on. The checker gives it, with its evidence, in its verdict on `E`
(`"engines"`, `SubstraitLean/Realize.lean`), from the class, observation and
shim columns of `E`'s choices. An option `E` realizes only up to its
observation needs a postcondition whose observation it refines
(`sv.equivalent`), or the row's shim; otherwise the plan is refused
there (`realization`).

A routed run also reads the engine's settings (DuckDB's
`current_setting`, Polars's engine affinity) and compares them with those
the profile's facts were probed under (`check_settings`): a setting a
choice-table row the plan depends on reads refuses the run
(`EngineSettingsError`), unless the plan states the behaviour (a sort's
NULLS LAST); another warns (`EngineSettingsWarning`).

Each engine profile records the engine versions its facts were probed at
(the checker's `--options`, "profiles"), and one range around them (D70):
the minor releases that hold a probed version. A run on an unprobed version
in the range warns (`EngineVersionWarning`) and records the version on its
route (`Route.unprobed_version`); outside the range it is refused
(`EngineVersionError`) until the probes are re-run, unless the caller runs
it with `unverified=True`.

A plan whose result is not determined up to row order
(`Report.deterministic`) runs natively, with the engine's own order of the
ties: the reference allows every order, and the proofs hold for each.
Where a rerun must give the same result (`choose(..., reproducible=...)`,
an incremental refresh or a sink's `reproducible=`), determinism is a
certificate (D24, D48): such a plan is refused, and the refusal names each
place where ties stay open. A plan that only picks a member of a class of
doubles is determined, and is refused only under an observation that reads
the members.
"""

from __future__ import annotations

import functools
import json
import math
import re
import warnings
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field, replace
from decimal import Decimal
from typing import TYPE_CHECKING, Any, Literal, NamedTuple

from sverify._engines import translations
from sverify._unsupported import SverifyError, SverifyWarning
from sverify.observation import Lenses, Within

if TYPE_CHECKING:
    from sverify.report import Report

RouteKind = Literal["native", "translated", "transfer", "recheck"]
#: A route taken, or `"unverified"`: a plan that is not proved, run with
#: `unverified=True`.
Taken = Literal["native", "translated", "transfer", "recheck", "unverified"]
#: Which routes run the checker's plan to run (`Report._plan_to_run`, #1787,
#: ruling 129): the translated and transfer routes rest on the reference
#: report, whose rewrite the checker proved to refine the plan as written. A
#: native or re-checked run rests on a check under the engine's profile, and an
#: unverified run runs what the user wrote: they run the plan as written.
RUNS_REWRITE: dict[str, bool] = {
    "translated": True,
    "transfer": True,
    "native": False,
    "recheck": False,
    "unverified": False,
}


def runs_rewrite(kind: str | None) -> bool:
    """Does a run on the route `kind` take the checker's plan to run?"""
    return RUNS_REWRITE.get(kind or "", False)


Class = Literal["exact", "observed", "shim", "refused"]
Evidence = Literal["proved", "tested"]
#: The classes, best first (#568): a plan takes the worst of its options'.
CLASSES: tuple[Class, ...] = ("exact", "observed", "shim", "refused")


def row_rerun(r: Mapping[str, Any]) -> Mapping[str, Any] | None:
    """A choices row's run-to-run variation, as an observation
    (`"rerun_observation"`, or `"rerun"` from a checker before the rename)."""
    return r.get("rerun_observation", r.get("rerun"))


#: The routes, in the order `choose` tries them.
ROUTES: tuple[RouteKind, ...] = ("native", "translated", "transfer", "recheck")


@dataclass(frozen=True)
class EngineProfile:
    """An engine's profile, as far as routes need it."""

    engine: str
    versions: tuple[str, ...]
    """The engine versions the profile's facts were probed at
    (`engines/<engine>/facts/`)."""


def shim_text(name: str) -> str:
    """What the shim `name` does, as a route line says it."""
    from sverify import profiles as plugged

    for p in plugged.plugins().values():
        if name in p.shim_text:
            return p.shim_text[name]
    return name.replace("_", " ")


#: How a route line names a route without a class (#687).
_KIND_TEXT: Mapping[str, str] = {
    "translated": "verified under portable semantics",
    "native": "verified under the engine's own semantics",
    "transfer": "verified under another engine's semantics, which carries over",
    "recheck": "verified again under the engine's own semantics",
    "unverified": "unverified",
}

#: How a route line names what an observation ignores (#687).
_IGNORES: Mapping[str, str] = {
    "zeros": "-0.0 as 0.0",
    "elements": "list elements in any order",
}


def _short(x: float) -> str:
    """A bound to two significant digits: `2e-07` for 1.998e-07."""
    return f"{float(f'{x:.2g}'):g}"


def observed_text(obs: Lenses) -> str:
    """What an observed route's results agree with the reference up to, in
    words: "doubles within abs=2e-07, rows in any order"."""
    parts = []
    # Rows are compared as a multiset unless the plan sorts them, for every
    # class: a route line leaves them out.
    for name in [n for n in obs.ignored() if n != "rows"]:
        v = getattr(obs, name)
        if name == "floats":
            if isinstance(v, Within):
                bounds = ", ".join(
                    f"{k}={_short(b) if k != 'ulps' else b}"
                    for k in ("abs", "rel", "ulps")
                    if (b := getattr(v, k)) is not None
                )
                parts.append(f"doubles within {bounds}")
            else:
                parts.append("doubles within the plan's bound")
        else:
            parts.append(_IGNORES.get(name, f"{name} {v}"))
    return ", ".join(parts) or "equal"


class UnverifiedRunWarning(SverifyWarning):
    """A plan runs unverified, because the caller passed `unverified=True`
    for a plan that is not proved or an engine version outside its
    profile's range, or the transform says `on_unproved="warn"`: nothing
    the report says holds of its result."""


class EngineVersionWarning(SverifyWarning):
    """The engine's version is not one its profile's facts were probed at,
    but in the profile's range (D70): the run assumes it computes what the
    probed version does."""


class EngineVersionError(SverifyError, RuntimeError):
    """The engine's version is outside its profile's range, the minor
    releases its facts were probed at (D70): install a version in the range,
    re-run the probes (`engines/<engine>/facts/`) first, or run with
    `unverified=True`."""

    code = "engine_version"


class EngineSettingsWarning(SverifyWarning):
    """An engine setting differs from its profile's, where only behaviour
    sverify does not rely on changes."""


class EngineSettingsError(SverifyError, RuntimeError):
    """An engine setting a profile's choices depend on differs from the
    value its facts were probed under, and the plan relies on it: restore it
    (the message says how), or re-run the probes under it."""

    code = "engine_settings"


class RouteError(SverifyError, ValueError):
    """No route takes the plan to the engine; `route` says why.

    Attributes:
        route: The refused route, with its `reason`.
    """

    code = "route_refused"

    def __init__(self, route: Route):
        super().__init__(f"refused on {route.engine}: {route.why}")
        self.route = route


@dataclass(frozen=True)
class Route:
    """How a plan reaches an engine (`choose`), or why it does not."""

    engine: str
    """The engine, by name."""
    taken: Taken | None
    """The route taken; `"unverified"` for a plan that is not proved, run
    with `unverified=True`; None when the plan is refused."""
    profile: str
    """The profile the proof the run relies on is under: the engine's own
    for `"native"`, `"transfer"` and `"recheck"`, `"portable"` for
    `"translated"`; for a refusal, the profile the plan was verified under."""
    why: str
    """Why this route, or why none, in words: `Postcondition.reason` is a code, `why` is words."""
    deterministic: bool = True
    """Whether the plan's result is determined up to row order
    (`Report.deterministic`)."""
    warnings: tuple[str, ...] = ()
    """What the run should know: a setting that differs, an open choice in
    the output."""
    failures: tuple[dict, ...] = field(default=(), compare=False)
    """For a failed transfer check: the options where the engine's choices
    are not within the profile's, as `{"group", "option", "from", "to",
    "facts"}`."""
    cls: Class | None = None
    """The plan's class on the engine ("Classes of an engine's functions" in
    `docs/core-semantics.md`): `"exact"`, `"observed"` (equal
    to a result the reference allows up to `observation`), `"shim"`, or
    `"refused"` for a refusal; the worst over the options the proof depends
    on; `"exact"` where the tables give no class for those options (the
    translation's tests stand for them). None only for a run with
    `unverified=True`, which no proof reaches."""
    evidence: Evidence | None = None
    """`"proved"` where every option's class is proved in Lean, `"tested"`
    where one rests on anything else: a test, a probe, a row without
    evidence. None where no class applies (a refusal, an unverified run)."""
    shims: tuple[str, ...] = ()
    """The shims the translation writes for this plan, by option."""
    reproducible: Lenses | None = None
    """What a rerun had to reproduce, where the caller
    required one; the route was refused unless the engine's run-to-run
    variation refines it."""
    rerun_evidence: Evidence | None = None
    """`"proved"` where every option's run-to-run variation is in the
    tables and proved, `"tested"` where one is missing (read as exact) or
    rests on an unproved bound; None without `reproducible`."""
    fallbacks: tuple[str, ...] = ()
    """On Polars, the nodes of the plan's streaming plan that run on the
    in-memory engine (`sverify_polars.engine.fallback_nodes`), recorded by
    `Report.run`: the in-memory engine's facts hold for those."""
    lenses: Lenses | None = None
    """For an `"observed"` route: the observation up to which the engine's
    result equals one the reference allows, the coarsest over the options
    the proof depends on (rows as a multiset, a tolerance on doubles from
    the plan's bound, …). None for the other classes."""
    bound_proved: bool | None = None
    """Whether the tolerance in `observation` rests on a bound Lean proves
    (`Report._epsilon`); False where it rests on a test; None without one."""
    suggested: dict[str, list[str]] = field(default_factory=dict, compare=False)
    """For a refusal, what to declare to make the plan verify, as condition
    labels per input table: an `sv.unique(...)` that determines a result
    with ties, an `sv.max_rows(n)` under which the plan's bound meets a
    tolerance."""
    engine_facts: tuple[str, ...] = ()
    """The engine facts behind the choices the class rests on
    (`engines/<engine>/facts/`)."""
    theorems: tuple[str, ...] = ()
    """The Lean theorems that prove those choices, where they are proved."""
    probed_version: str | None = None
    """The engine version the facts were probed at."""
    unprobed_version: str | None = None
    """The engine version the run is on where it is in the profile's range
    but not probed (D70): the proof stands, and the engine step assumes this
    version computes what the probed one does. None on a probed version."""
    issues: tuple[int, ...] = ()
    """The issues that track the tested choices (`"issue"` of a tested row)."""
    theorem_facts: tuple[str, ...] = ()
    """The facts the theorems rest on, where they prove the engine's model
    (`Rel.polars_sound` of `Polars.impl`): those facts say the engine is it."""
    settings: tuple[tuple[str, Any], ...] = ()
    """The engine settings the route was checked under, by name, as read
    from the session the run uses (`check_settings`): the settings its
    profile's facts assume. Empty where the engine has none to read, and on
    Spark before sverify's own session starts, which is read back when it
    does (`sverify_spark.engine.check_pinned`)."""

    @property
    def refused(self) -> bool:
        """Whether no route takes the plan to the engine (`kind` is None)."""
        return self.taken is None

    def __str__(self) -> str:
        """The class first, then what it means for this plan and the
        evidence: "shim (integer division …); evidence tested". The
        long form is `reason`."""
        if self.taken is None:
            return f"refused: {self.why}"
        if self.taken == "unverified":
            return f"unverified: {self.why}"
        out = self.cls or _KIND_TEXT.get(self.taken, self.taken)
        if self.cls == "shim" and self.shims:
            what = dict.fromkeys(shim_text(n) for n in (x.split(": ", 1)[-1] for x in self.shims))
            out += f" ({'; '.join(what)})"
        if self.cls == "observed" and self.lenses is not None:
            out += f": {observed_text(self.lenses)}"
        if self.evidence:
            out += "; evidence " + evidence_text(self, self.engine)
        if self.cls and self.taken != "translated":
            # How the proof reaches the engine, where it is not the
            # translation from the reference.
            out += f"; {self.taken}: {self.why}"
        if not self.deterministic:
            out += "; the result is not determined up to row order"
        return out


# -- engine versions (D14) ----------------------------------------------------


def installed_version(engine: str) -> str | None:
    """The version of `engine` this process runs, None if it has no profile
    or is not installed."""
    from sverify import profiles as plugged

    p = plugged.find(engine)
    if p is None or p.installed_version is None:
        return None
    try:
        return p.installed_version()
    except ImportError:
        return None


def session_version(engine: Any) -> str | None:
    """The engine version of a session of the caller's (a Spark session's
    `version`), None for an engine given by name: that one is installed
    (`installed_version`)."""
    v = None if isinstance(engine, str) else getattr(engine, "version", None)
    return v if isinstance(v, str) else None


def probed_version(engine: str) -> str | None:
    """The engine version `engine`'s facts were probed at (its profile's
    first), None for an engine without a profile."""
    prof = profiles().get(engine)
    return prof.versions[0] if prof is not None and prof.versions else None


def evidence_text(x: Route | Realized, engine: str) -> str:
    """The evidence of a route's class (or a realization's) in words: the
    theorems for a proof, and where they prove the engine's model, the facts
    that say the engine is that model; the engine version, the facts
    and the issues that track them for a test."""
    if x.evidence == "proved":
        out = "proved" + (f" by {', '.join(x.theorems)}" if x.theorems else "")
        if x.theorem_facts:
            out += f" on {engine}'s model (facts {', '.join(x.theorem_facts)})"
    else:
        out = "tested"
        if x.probed_version:
            out += f" at {x.probed_version}"
        cited = [f"facts {', '.join(x.engine_facts)}"] if x.engine_facts else []
        cited += [f"#{i}" for i in x.issues]
        if cited:
            out += f" ({'; '.join(cited)})"
    if unprobed := getattr(x, "unprobed_version", None):
        # D70: the engine step assumes this version computes what the probed one does.
        out += f"; this run is on {unprobed}, unprobed"
    return out


def _release(v: str) -> tuple[int, int, int] | None:
    """A version's (major, minor, patch): `(2, 0, 1)` for "2.0.1", "v2.0.1"
    or "py-2.0.1rc1"; None where it has no major and minor. A pre-release
    reads as its release, so "2.0.0rc1" is in range and warns as unprobed."""
    m = re.match(r"(?:py-|v)?(\d+)\.(\d+)(?:\.(\d+))?", v)
    return None if m is None else (int(m[1]), int(m[2]), int(m[3] or 0))


def _version_range(versions: Sequence[str]) -> tuple[str, str] | None:
    """The range of engine versions a profile probed at `versions` covers
    (D70): the minor releases that hold a probed version, from the lowest
    probed patch up, as the bounds `(">=", "<")` of the engine package's
    dependency, `("2.0.0", "2.1")` for `("2.0.0",)`. None without versions.
    The bounds are exact for probes in one minor, as D70 fixes each engine
    at 1.0 (`test_the_package_bound_is_the_profiles_range` holds it): with
    probes at 2.0.0 and 2.2.0 they would span 2.1, which `_in_range` refuses."""
    found = sorted(r for v in versions if (r := _release(v)) is not None)
    if not found:
        return None
    major, minor = found[-1][:2]
    return ".".join(map(str, found[0])), f"{major}.{minor + 1}"


def _in_range(version: str, versions: Sequence[str]) -> bool:
    """Whether `version` is in the range of a profile probed at `versions`
    (`_version_range`): a minor release that holds a probed version, at or
    above that minor's lowest probed patch."""
    r = _release(version)
    if r is None:
        return False
    floors = [p for v in versions if (p := _release(v)) is not None and p[:2] == r[:2]]
    return bool(floors) and r >= min(floors)


def check_version(engine: str, version: str | None = None) -> str | None:
    """Check `engine`'s version (the installed one by default) against its
    profile's (D70).

    Returns:
        None on a version the facts were probed at, or for an engine without
        a profile. On an unprobed version in the profile's range
        (`_version_range`), what the run assumes, also issued as an
        `EngineVersionWarning`; `warnings.simplefilter("error",
        EngineVersionWarning)` makes it a refusal.

    Raises:
        EngineVersionError: The version is outside the range.
    """
    prof = profiles().get(engine)
    if prof is None or not prof.versions:
        return None
    version = version or installed_version(engine)
    if version is None or version in prof.versions:
        return None
    probed = ", ".join(prof.versions)
    floor, ceiling = _version_range(prof.versions) or (prof.versions[0], "")
    if not _in_range(version, prof.versions):
        raise EngineVersionError(
            f'{engine} {version} is outside the range of semantics="{engine}", '
            f"whose facts were probed at {probed}: install a version of {engine} in "
            f">={floor},<{ceiling}, "
            f"or run(..., unverified=True) to run it anyway; running {version} verified "
            f"needs its facts probed again (engines/{engine}/facts/)"
        )
    msg = (
        f'{engine} {version} is not a version the facts of semantics="{engine}" were '
        f"probed at ({probed}): the run assumes it computes what {prof.versions[0]} does, "
        f"and an unproved run relies on {version}'s own errors"
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
        depends: The options the plan depends on (`Report._depends`); None
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
    """The engine profiles: the checker's (`--options`, "profiles"), whose
    versions are those its facts were probed at, over those of the installed
    profiles from outside sverify."""
    from sverify import profiles as plugged

    out: dict[str, EngineProfile] = {}
    for e, p in plugged.plugins().items():
        if p.versions:  # a profile from outside; sverify's own are the checker's
            out[e] = EngineProfile(e, p.versions)
    for name, p in (_options_json().get("profiles") or {}).items():
        if isinstance(p, dict) and p.get("engine"):
            out[name] = EngineProfile(p["engine"], tuple(p.get("versions") or ()))
    return out


def _failure_text(f: Mapping[str, Any], source: str, target: str) -> str:
    where = f"{f['group']}'s {f['option']}" if f.get("group") else f["option"]
    to = "any behaviour" if f["to"] is None else ", ".join(f["to"])
    facts = f" ({', '.join(f['facts'])})" if f.get("facts") else ""
    return f"{where}: {source} gives {', '.join(f['from'])}, {target} gives {to}{facts}"


def lean_transfer(source: str, target: str, depends: Sequence[Mapping[str, Any]]) -> dict | None:
    """The checker's own transfer check (`substrait-check --transfer`), which
    is authoritative: `{"ok": bool, "failures": [...]}`; None where the
    checker has none. A route reads the same check from the checker's
    verdict on the engine (`"transfer"`)."""
    from sverify.engine import checker_path

    request = json.dumps({"from": source, "to": target, "depends": list(depends)}, sort_keys=True)
    out = _transfer(str(checker_path()), request)
    try:
        found = json.loads(out) if out is not None else None
    except json.JSONDecodeError:
        return None
    if not isinstance(found, dict) or "ok" not in found:
        return None
    failures = found.get("failures")
    if failures is None:
        failures = [found["failure"]] if found.get("failure") else []
    return {"ok": bool(found["ok"]), "failures": failures}


def _transfer(checker: str, request: str) -> str | None:
    """The checker's answer to a transfer request, or None where the checker
    fails. Answers are kept per process (`_answer`); a failure is not, so a
    timeout does not stick."""
    import subprocess

    try:
        return _answer(checker, request)
    except (OSError, subprocess.SubprocessError):
        return None


@functools.lru_cache(maxsize=512)
def _answer(checker: str, request: str) -> str:
    """The checker's answer: a function of the request and the checker
    alone, so each is asked once per process (an export asks it per `shims`
    mode, #862). Raises where the checker fails, which keeps it uncached."""
    import subprocess

    return subprocess.run(
        [checker, "--transfer"],
        input=request,
        capture_output=True,
        text=True,
        check=True,
        timeout=60,
    ).stdout


def row(profile: str, group: str | None, option: str) -> dict | None:
    """A profile's row of the choices table at (group, option), the
    group's row over the one for every group; None where it has neither."""
    rows = (_options_json().get("choices") or {}).get(profile) or []
    by_key = {(r.get("group"), r.get("option")): r for r in rows}
    return by_key.get((group, option)) or by_key.get((None, option))


def _where(group: str | None, option: str) -> str:
    return f"{group}'s {option}" if group else option


#: Engines whose route is not there yet, with the issue that lifts the refusal.
_PENDING = {"snowflake": 852}
_ISSUES = "https://github.com/AlexanderNenninger/substrait-lean/issues"

_KINDS = ("abs", "rel", "ulps")


class Printed(float):
    """A number as the checker printed it: the nearest double, and the text it came from
    (`json.loads(..., parse_float=Printed)`)."""

    text: str

    def __new__(cls, text: str) -> Printed:
        self = super().__new__(cls, text)
        self.text = text
        return self


def _up(value: float) -> float:
    """The least double at or above a printed bound. Each bound is an upper bound on an
    error, printed rounded up; its nearest double may lie below it, and a double `s` is
    at least the bound exactly when it is at least this one."""
    d = Decimal(getattr(value, "text", None) or repr(float(value)))
    f = float(d)
    return math.nextafter(f, math.inf) if Decimal(f) < d else f


def _bounds(eps: Mapping[str, Any]) -> dict[str, tuple[float, bool]]:
    """A column's `ε` as `{kind: (value, proved)}`, as the checker normalises
    it (`Realize.epsBounds`: `"epsilon_bounds"`, or an engine's
    `"epsilon"`, where `proved` is that engine's)."""
    return {k: (_up(b["value"]), bool(b["proved"])) for k, b in eps["bounds"].items()}


def _plan_bound(
    q: Mapping[str, Any],
    observed: Lenses,
    epsilon: Mapping[str, Mapping[str, Any]] | None,
    against: str = "of the reference, and the postcondition asks",
    fix: str = (
        "state sv.equivalent(floats={tol}) or looser in ensures, "
        "or sv.equivalent({plan}) for the plan's own bound"
    ),
) -> tuple[dict[str, Any], list[str], bool]:
    """An observation without a plan-dependent float bound (`{"floats": {"bound":
    "plan"}}`), the problems with that bound, and whether the bound that
    meets the postcondition rests on an unproved bound.

    The contract's result gives each double output column's `ε`
    (`Report._epsilon`): bounds of several kinds, each of which holds on its
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
        if eps["unbounded"]:
            # No bound on the column (a double `SUM` without a row cap, a value
            # computed from one, a window aggregate of doubles): nothing proves
            # it, and a stated tolerance is not met. `why` names what lifts it.
            # A postcondition on it runs: the checker knows only its sign
            # there (`floatBound`'s signed part), which a sum of values of one
            # sign keeps in every order but Kahan's
            # (`FloatBounds.StdModel.TreeSum.sign`), a variance by its clamp.
            unproved = True
            if isinstance(stated, Within):
                why = f" ({eps['why']})" if eps.get("why") else ""
                problems.append(
                    f"{col} has no bound on its distance to the reference{why}, and the "
                    f'postcondition asks {stated}: state sv.equivalent(floats="plan") '
                    "or drop the tolerance"
                )
            continue
        if not any(v for v, _ in bounds.values()):
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


def _resolve(observed: Lenses, epsilon: Mapping[str, Mapping[str, Any]] | None) -> Lenses:
    """`observed` with `floats="plan"` replaced by the plan's bound: per
    kind of bound, the smallest of the double columns' `ε` (every column
    meets it), exact where no column has one. Unchanged where the checker
    gave no `ε`."""
    from sverify.observation import Within

    if observed.floats != "plan" or epsilon is None:
        return observed
    if any(e["unbounded"] for e in epsilon.values()):
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


#: Why #568's threshold rule refuses a plan, as `realization` words it.
_THRESHOLD = (
    "a filter, grouping key or sort on a double may keep other rows on {engine} than "
    "the reference: its threshold lies within the doubles' bound of their range; "
    "for a constant threshold, state a precondition that keeps the values away from it; "
    "for a threshold computed from the data (a mean, a sum), compare exact columns: "
    "for a mean of integers, `x * COUNT(y) > SUM(y)`, another query: it compares the exact "
    "mean, not the rounded one, and its product must fit BIGINT: a bound on y and a row "
    "cap (`sv.max_rows`) prove it"
)


def _cited(facts: Sequence[str] | None) -> str:
    return f" ({', '.join(facts)})" if facts else ""


def verdict(report: Report, engine: str) -> Mapping[str, Any] | None:
    """The checker's verdict on the report's plan on `engine` (`"engines"`,
    `SubstraitLean/Realize.lean`); None where it gives none. An engine
    without a profile in the checker has one too (`"profile": false`): the
    translation's tests stand for the plan."""
    return (report._engines or {}).get(engine)


def realization(engine: str, verdict: Mapping[str, Any] | None, report: Report) -> Realized:
    """How `engine` realizes the plan, from the checker's verdict (`verdict`,
    `SubstraitLean/Realize.lean`): its class over the options the proof
    depends on, the evidence, the shims and what refuses it, met against the
    observation the postcondition names (`"realized"`). Where the options'
    observation does not refine the postcondition's, the row's shim makes it
    canonical (class `shim`), or the plan is refused there; a row that bounds
    the doubles per plan (Polars's `sum_order`) is met against the plan's `ε`.
    The checker gives the problems as data, and this words them.

    Returns:
        The class, the evidence, the shims written, the problems that refuse
        the plan, and, for an observed plan, the observation and whether its
        tolerance is proved; with the theorems, facts, version and issues the
        evidence cites.
    """
    from sverify.observation import from_json

    if verdict is None:
        return Realized(
            "refused",
            None,
            (),
            [f"the checker gave no verdict on {engine} for this plan: verify it again"],
        )
    got = verdict.get("realized") or verdict
    worst: Class = got["class"]
    if worst not in CLASSES:
        raise ValueError(f"the checker gave an unknown class {worst!r} on {engine}")
    shims = [f"{_where(x['group'], x['option'])}: {x['shim']}" for x in got.get("shims", ())]
    problems = [_problem(engine, p, report) for p in got.get("problems", ())]
    seen = got.get("observation")
    return Realized(
        worst,
        "proved" if got.get("evidence") == "proved" else "tested",
        tuple(shims),
        problems,
        None if seen is None else from_json(seen),
        got.get("bound_proved"),
        tuple(verdict.get("facts", ())),
        tuple(verdict.get("theorems", ())),
        verdict.get("version") or probed_version(engine),
        tuple(verdict.get("issues", ())),
        tuple(verdict.get("proved_facts", ())),
    )


def _problem(engine: str, p: Mapping[str, Any], report: Report) -> str:
    """A problem of the checker's realization (`Realize.lean`) in words."""
    from sverify.observation import Within, from_json

    code = p.get("code")
    if code == "option_refused":
        where = _where(p.get("group"), p["option"])
        return f"{where} is refused on {engine}{_cited(p.get('facts'))}"
    if code == "threshold":
        return _THRESHOLD.format(engine=engine)
    if code not in ("observation_missed", "unbounded", "held", "not_met"):
        return f"{code} on {engine}"
    where, cited, stated = _where(p["group"], p["option"]), _cited(p.get("facts")), seen_by(report)
    if code == "observation_missed":
        missed = ", ".join(p["components"])
        return (
            f"{where}: {engine} agrees with the reference only up to {from_json(p['observed'])}, "
            f"and the postcondition observes its {missed} ({stated}); state "
            f"{missed} in sv.equivalent(...) or shim it{cited}"
        )
    col = p["column"]
    if code == "unbounded":
        why = f" ({p['why']})" if p.get("why") else ""
        text = (
            f"{col} has no bound on its distance to the reference{why}, and the "
            f'postcondition asks {stated.floats}: state sv.equivalent(floats="plan") '
            "or drop the tolerance"
        )
        return f"{where}: {text}{cited}"
    bounds = {b["kind"]: (_up(b["value"]), bool(b["proved"])) for b in p["bounds"]}
    if code == "held":
        label = report.ensures[p["condition"]].label
        shown = ", ".join(f"{k}={v:g}" for k, (v, _) in bounds.items())
        text = (
            f"the postcondition {label} reads {col}, which is within {shown} of the "
            f"reference: write it as sv.approx({label}), or state "
            f"sv.equivalent(floats={_smallest(bounds)}) in ensures"
        )
        return f"{where}: {text}{cited}"
    shown = ", ".join(f"{k}={v:g}" + ("" if ok else " (tested)") for k, (v, ok) in bounds.items())
    want = str(stated.floats) if isinstance(stated.floats, Within) else "exact doubles"
    text = (
        f"{col} is within {shown} of the reference, and the postcondition asks {want}: "
        f"state sv.equivalent(floats={_smallest(bounds)}) or looser in ensures, "
        'or sv.equivalent(floats="plan") for the plan\'s own bound'
    )
    return f"{where}: {text}{cited}"


class Realized(NamedTuple):
    """How an engine realizes a plan's options (`realization`)."""

    cls: Class
    evidence: Evidence | None
    shims: tuple[str, ...]
    problems: list[str]
    observation: Lenses | None = None
    bound_proved: bool | None = None
    engine_facts: tuple[str, ...] = ()
    """The facts behind the rows of the options the plan depends on."""
    theorems: tuple[str, ...] = ()
    """The theorems that prove those rows (`"theorem"` of a proved row)."""
    probed_version: str | None = None
    """The engine version the rows' facts were probed at (`"version"`)."""
    issues: tuple[int, ...] = ()
    """The issues that track the tested rows (`"issue"`)."""
    theorem_facts: tuple[str, ...] = ()
    """The facts the proved rows' theorems rest on (`"proved_facts"`)."""


def plan_bound(epsilon: Mapping[str, Mapping[str, Any]] | None) -> Within | None:
    """The plan's bound on its doubles as one tolerance: per kind every
    column has, the largest of the columns' `ε` (`Report._epsilon`). None
    where no double column has a bound above zero, or one has none."""
    if not epsilon or any(e["unbounded"] for e in epsilon.values()):
        return None
    found = [b for b in (_bounds(e) for e in epsilon.values()) if any(v for v, _ in b.values())]
    kinds = [k for k in _KINDS if found and all(k in b for b in found)]
    if not kinds:
        return None
    most = {k: max(b[k][0] for b in found) for k in kinds}
    return Within(
        most.get("abs"), most.get("rel"), None if "ulps" not in most else int(most["ulps"])
    )


def floats_on(report: Report) -> dict[str, list[str]]:
    """For an observation that states its doubles (`floats="exact"` or a
    tolerance), per engine the reference translates to and has a choices
    table for, the problems that observation meets on the engine's doubles
    and the plan's bound (`epsilon`) does not: empty where the engine meets
    it (the checker's `"floats_added"`). Empty under any profile but the
    reference's (a native route is exact), and for a plan without doubles."""
    if report.lenses.floats == "plan" or report.semantics != "portable":
        return {}
    if not any(getattr(t, "is_floating", bool)() for t in report.output.values()):
        return {}
    out: dict[str, list[str]] = {}
    for e in translations():
        if (v := verdict(report, e)) is None or v.get("profile") is False:
            continue
        out[e] = [_problem(e, p, report) for p in v.get("floats_added", ())]
    return out


def evidence_on(report: Report) -> dict[str, Realized]:
    """Per engine the reference translates to and has a choices table for,
    how it realizes a verified plan (`realization`), with the evidence a
    translated route would carry (`translated_evidence`): what a run
    rests on, known before it. Empty for a plan that is not verified, or
    verified under another profile."""
    if report.semantics != "portable" or not verified(report):
        return {}
    out: dict[str, Realized] = {}
    for e in translations():
        if (v := verdict(report, e)) is None or v.get("profile") is False:
            continue
        got = realization(e, v, report)
        out[e] = got._replace(evidence=translated_evidence(v, got))
    return out


def translated_evidence(v: Mapping[str, Any], got: Realized) -> Evidence | None:
    """The evidence of a translated route: `got`'s, and tested where the
    checker says a translated run rests on a test (`"tested_because"`: a
    postcondition that holds on the engine's doubles by its facts, or on the
    reference's orders only)."""
    return "tested" if got.evidence == "proved" and v.get("tested_because") else got.evidence


def seen_by(report: Report) -> Lenses:
    """What a run checks the engine's result against: the report's
    observation (`ensures`'s, or else rows as a multiset, doubles within
    the plan's bound and other values exact, `PLAN_BOUND`), without the
    bound the report prints. Under the plan's bound (`floats="plan"`), the
    checker holds the double columns a postcondition reads to their exact
    value (`"held"`): a condition proved of the reference's value need not
    hold of a value near it."""
    return replace(report.lenses, bound=None)


# -- the re-check -------------------------------------------------------------


def recheck(report: Report, profile: str) -> tuple[bool | None, str]:
    """Prove the report's contract again under `profile`.

    Returns:
        Whether it was proved (None: the checker cannot check under that
        profile), and why in words.
    """
    from sverify.engine import run_checker

    if report._contract is None:
        return None, "the report keeps no contract to check again"
    try:
        code, out, err = run_checker(
            ("--contract",), json.dumps({**report._contract, "profile": profile})
        )
    except Exception as e:  # noqa: BLE001
        return None, f"the checker failed: {e}"
    if code not in (0, 4):
        return None, f"the checker failed: {err.strip()}"
    res = json.loads(out)
    if res.get("profile") != profile:
        return None, (
            f'the checker cannot check under semantics="{profile}" yet (#444); '
            "verify with semantics='portable' to reach every engine"
        )
    unproved = [e["name"] for e in res.get("ensures", []) if not e.get("proved")]
    unproved += ["a key" for k in res.get("keys", []) if not k.get("proved")]
    errors = [f"{i['kind']}: {i['expr']}" for i in res.get("issues", []) if i.get("error")]
    if unproved or errors:
        return False, 'under semantics="{}": {}'.format(
            profile,
            "; ".join([f"not proved: {u}" for u in unproved] + [f"may fail: {e}" for e in errors]),
        )
    return True, f'proved again under semantics="{profile}"'


# -- choosing the route (D13) -------------------------------------------------


def max_rows_fix(report: Report, engine: str, required: Lenses | None) -> dict[str, list[str]]:
    """The `sv.max_rows(N)` under which the plan's bound on its doubles
    (`Report._epsilon`) meets the tolerance `required` states, by the input
    table that has a row cap now: the bound grows linearly with the rows,
    so `N` is the cap scaled by the tightest ratio of tolerance to bound.
    Empty where there is no stated tolerance, no single capped input, or
    the bound already meets it; `sv.max_rows(0)` where no cap does."""
    from sverify.conditions import MaxRows

    if required is None or not isinstance(required.floats, Within) or not report._epsilon:
        return {}
    caps = {t: c.n for t, cs in report._conditions.items() for c in cs if isinstance(c, MaxRows)}
    if len(caps) != 1:
        return {}
    ((table, n0),) = caps.items()
    ratio = None
    for eps in report._epsilon.values():
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
    """How to make the report's result determined up to row order: an
    `ORDER BY` for a `LIMIT` without one, the `sv.unique(...)` it needs
    (`Report.ties`), or `TIES`."""
    unordered = any(p.op == "fetch" and "no ORDER BY" in p.what for p in report._class_places)
    if unordered and not report.ties and all(p.op == "fetch" for p in report._class_places):
        return UNORDERED_FETCH
    fix = _unique_fix(report)
    return f"{UNORDERED_FETCH}; {fix}" if unordered else fix


def _unique_fix(report: Report) -> str:
    """The `sv.unique(...)` the report's ties need (`Report.ties`), or `TIES`."""
    if not report.ties:
        return TIES

    def code(lab: str) -> str:
        cols = lab.removeprefix("unique(").removesuffix(")").split(", ")
        return f"sv.unique({', '.join(repr(c) for c in cols)})"

    parts = [f"{', '.join(map(code, labs))} on {t}" for t, labs in report.ties.items()]
    return "declare " + " and ".join(parts) + " in requires, so no rows tie in the ORDER BY"


#: How to fix the rows a LIMIT without an ORDER BY takes (#928): the
#: reference allows any of them, so a rerun may take others.
UNORDERED_FETCH = (
    "order the rows before the LIMIT, with order_by(...) on columns that sv.unique(...) "
    "makes a key, so a rerun takes the same rows"
)

#: The two ways out of a class pick under an observation that reads the
#: members (D48).
CLASS_PICKS = (
    "pass lenses that read one zero and one NaN, such as the default "
    "sv.equivalent(floats='plan') or sv.equivalent(zeros='canon'), or change the plan so "
    "it picks no double"
)

#: How to make a result determined up to row order.
TIES = (
    "declare `unique(...)` on the partition (or grouping) and order columns of the input, "
    "or give first(), last() and windows a total order"
)


def engine_name(engine: Any) -> str:
    """An engine's name: a string as given, lower case; a session, the
    engine's that recognises it (`ProfilePlugin.session`: a Spark session).

    Raises:
        ValueError: No installed engine recognises the session.
    """
    if isinstance(engine, str):
        return engine.lower()
    from sverify import profiles as plugged

    if (p := plugged.find(engine)) is None:
        raise ValueError(f"no installed engine takes {type(engine).__name__} as a session")
    return p.engine


def reproducibility(
    report: Report,
    engine: str,
    required: Lenses,
    depends: Sequence[Mapping[str, Any]] | None = None,
) -> tuple[list[str], Evidence]:
    """Whether a rerun of the plan on `engine` reproduces its result up to
    `required` (what a rerun must reproduce).

    The result must be determined up to row order and the member of each
    class of doubles (`Report.deterministic`, D48): an open choice (ties in
    an ORDER BY, a LIMIT without one) fails every requirement, and the
    problem names each place. A place that only picks a member of a class
    (`-0.0` or `0.0`, a NaN: a group key over doubles, `MIN`, `MAX`) fails a
    requirement that reads the members (`Lenses.reads_members`): the
    reference leaves the member open, and the check is the plan's, reading
    no engine fact; the problem names each pick and the two ways out. Then,
    on each option the plan depends on, the engine's run-to-run
    variation (the `"rerun_observation"` column of its
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
            "the result is not determined up to row order: the plan leaves open "
            + ("; ".join(map(str, report._class_places)) or "a place the report does not name")
            + ", so no rerun is sure to reproduce it"
        )
    elif not report._exact and required.reads_members:
        # Before `_resolve`: `"plan"` reads one zero and one NaN, also where
        # the plan has no bound and `_resolve` makes it exact (D48).
        picks = [p for p in report._tie_places if p.kind == "class"]
        problems.append(
            f"{required} reads the members of a class of doubles, and the plan picks one at "
            + ("; ".join(map(str, picks)) or "a place the report does not name")
            + f", which the reference leaves open: {CLASS_PICKS}"
        )
    if depends is None:
        depends = report._depends
    if depends is None:
        problems.append(
            "the report has no dependency report from the checker to check a rerun against: "
            "verify the plan again"
        )
        depends = ()
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
            report._epsilon,
            "between runs, and a rerun must reproduce",
            "pass reproducible=sv.equivalent(floats={tol}) or looser, "
            "or sv.equivalent({plan}) (the sinks' default) for the plan's own bound",
        )
        # The row's own evidence for its variation (`{}` where it is known
        # exact); the class's evidence says nothing about reruns.
        tested = tested or unproved or r.get("rerun_evidence") != "proved"
        varies = from_json(rest)
        missed = varies.coarser_than(_resolve(required, report._epsilon))
        if missed:
            unknown = (
                "; the checker gives no bound on the plan's doubles: bound the inputs "
                "(a range, and sv.max_rows) or pass "
                "reproducible=sv.equivalent(floats=sv.within(...))"
                if "floats" in missed and _resolve(required, report._epsilon).floats == "plan"
                else ""
            )
            problems.append(
                f"{_where(g, o)}: two runs on {engine} agree only up to {varies}, and a rerun "
                f"must reproduce its {', '.join(missed)} ({required}){unknown}"
            )
        problems += [f"{_where(g, o)}: {p}" for p in bounded]
    return problems, "tested" if tested else "proved"


def verified(report: Report) -> bool:
    """Whether a run may take the plan: it is proved (`Report.verdict`), or
    its only unproved postconditions are checked on the output data
    (`on_unproved="check"`)."""
    return report._verified


def not_verified(report: Report) -> str:
    """Why a plan is not verified, in the user's terms: each runtime error
    that may happen and each postcondition that is not proved, with where
    the report keeps them, and how to run it anyway."""
    from sverify._user_text import plain

    parts = [f"may fail: {i}" for i in report.errors]
    see = ["report.errors"] if report.errors else []
    for c in report._unmet_ensures():
        if not c.proved:
            parts.append(f"ensures {plain(c.label)} is not proved: {c.why}")
        else:
            from sverify import observation as _observation

            parts.append(f"ensures {plain(c.label)} {_observation.why(c.ignores)}")
        if "report.unproved" not in see:
            see.append("report.unproved")
    parts += [f"needs {n}" for n in report._needs_lines()]
    if report.floats_unmet:
        first = next(ps[0] for ps in report._floats_on.values() if ps)
        want = "exact doubles" if report.lenses.floats == "exact" else "tolerance on doubles"
        parts.append(f"no engine meets the lenses' {want}: {first}")
        see.append("report.details()")
    if report.needs:
        see.append("report.needs")
    if report._transfer:
        parts.append(
            "the reference's proof does not carry over to Substrait's semantics on "
            + ", ".join(_where(f.get("group"), f["option"]) for f in report._transfer)
        )
        if "report.details()" not in see:
            see.append("report.details()")
    where = f" (see {', '.join(see)})" if see else ""
    return (
        "not verified: "
        + "; ".join(parts or ["the report is not proved"])
        + where
        + "; run(..., unverified=True) runs it anyway"
    )


def unverified(report: Report, engine: Any, reason: str | None = None) -> Route:
    """The route of a plan run with `unverified=True`: no proof reaches the
    engine, and the reason says what was not proved, or (`reason`) why the
    engine's version was refused (D70)."""
    e = engine_name(engine)
    if reason is None:
        reason = not_verified(report).removesuffix("; run(..., unverified=True) runs it anyway")
    return Route(e, "unverified", report.semantics, reason, report.deterministic)


def choose(
    report: Report,
    engine: Any,
    route: RouteKind | Literal["auto"] = "auto",
    *,
    version: str | None = None,
    reproducible: Lenses | None = None,
) -> Route:
    """The route by which the plan `report` checked reaches `engine`.

    Args:
        report: A report of `sv.verify` (or a transform's `report`).
        engine: The engine's name, or a Spark session.
        route: `"auto"` (the default) tries `"native"`, `"translated"`,
            `"transfer"` and `"recheck"` in turn; a route by name is taken or
            refused.
        reproducible: What a rerun must reproduce, as an
            idempotent sink needs: the engine's run-to-run variation must
            refine it (`reproducibility`), or the route is refused. None
            (the default) reports determinism and checks nothing.
        version: The engine's version; the installed one by default.

    Returns:
        The `Route`, with the plan's class on the engine; refused
        (`Route.refused`) with the reason when no route applies.

    Raises:
        EngineVersionError: The engine's version is outside its profile's
            range (D70).
        EngineSettingsError: A setting the engine's profile depends on
            differs from its facts' (`check_settings`).
        ValueError: `route` is unknown.
    """
    from sverify import _support

    if route != "auto" and route not in ROUTES:
        raise ValueError(f"route must be 'auto' or one of {', '.join(ROUTES)}, not {route!r}")
    e = engine_name(engine)
    notes: list[str] = []
    version = version or session_version(engine) or installed_version(e)
    unprobed = version if check_version(e, version) else None
    plan = json.loads(report.internal_plan) if report.internal_plan else {}
    depends = report._depends
    from sverify import _engine_settings

    # Read once, on a caller's session (Spark's) or the one the run uses, and
    # recorded on the route (#1130).
    values = _engine_settings.current(e, None if isinstance(engine, str) else engine)
    notes += check_settings(e, values, depends=depends)
    read = tuple(sorted(values.items()))
    source = report.semantics
    det = report.deterministic

    def refuse(reason: str, failures: Sequence[dict] = ()) -> Route:
        return Route(
            e,
            None,
            source,
            reason,
            det,
            tuple(notes),
            tuple(failures),
            "refused",
            unprobed_version=unprobed,
            settings=read,
        )

    if not verified(report):
        if report.floats_unmet:
            cap = max_rows_fix(report, e, report.lenses)
            return replace(refuse(not_verified(report) + _cap_text(cap)), suggested=cap)
        return refuse(not_verified(report))
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
            "ties stay open: the engine picks their order, every proof holds for any "
            "pick, and a rerun may pick another"
        )
    if report.lenses.rows == "sequence" and not report._sequence_determined:
        return refuse(
            "the postcondition observes the rows as a sequence, and the plan does not fix their "
            "order: its result is not sorted on a key of its input"
        )
    from sverify.sql.core import _base

    try:
        _support.check(plan, e)
        _base.check_decimal_text(plan, e)
    except ValueError as err:
        return refuse(str(err))

    def taken(kind: RouteKind, profile: str, reason: str) -> Route:
        if kind != "translated":
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
                unprobed_version=unprobed,
                settings=read,
            )
        seen = seen_by(report)
        v = verdict(report, e)
        got = realization(e, v, report)
        if got.problems:
            cap = max_rows_fix(report, e, seen)
            return replace(refuse("; ".join(got.problems) + _cap_text(cap)), suggested=cap)
        gives = got.observation
        if gives is not None and gives.rows == "sequence" and not report._sequence_determined:
            # The reference leaves open the order of an unsorted result and of tied sort keys.
            gives = replace(gives, rows="multiset")
        return Route(
            e,
            kind,
            profile,
            reason,
            det,
            tuple(notes),
            (),
            got.cls,
            translated_evidence(v or {}, got),
            got.shims,
            reproducible,
            rerun_evidence,
            lenses=gives,
            bound_proved=got.bound_proved,
            engine_facts=got.engine_facts,
            theorems=got.theorems,
            probed_version=got.probed_version or probed_version(e),
            unprobed_version=unprobed,
            issues=got.issues,
            theorem_facts=got.theorem_facts,
            settings=read,
        )

    translated = translations()
    tried = ROUTES if route == "auto" else (route,)
    why_not: list[str] = []
    failures: list[dict] = []
    for kind in tried:
        if kind == "native":
            if source == e:
                return taken("native", e, f'verified under semantics="{e}"')
            why_not.append(f'not verified under semantics="{e}"')
        elif kind == "translated":
            if source == "portable" and e in translated:
                return taken(
                    "translated",
                    "portable",
                    'verified under semantics="portable"; '
                    f"the translation to {e} is {translated[e]}",
                )
            why_not.append(
                'not verified under semantics="portable"'
                if source != "portable"
                else f"no translation from portable semantics to {e}"
            )
        elif kind == "transfer":
            if source in ("portable", e):
                why_not.append(f'no transfer from semantics="{source}" needed')
                continue
            # The checker's transfer check (`transferB`, proved sound by
            # `Rel.transfer_of_transferB`), over every option the plan reads.
            checked = ((verdict(report, e) or {}).get("transfer") or {}).get(source)
            found = None if checked is None else list(checked.get("failures") or ())
            if found is None:
                why_not.append(
                    f'the checker gave no transfer check from semantics="{source}" to {e}'
                )
            elif not found:
                return taken(
                    "transfer",
                    e,
                    f'verified under semantics="{source}"; {e}\'s choices are within its '
                    "choices on every option the plan reads",
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
    if route == "auto" and source not in ("portable", e) and e in translated:
        # Lead with what the user can do: the reference reaches every engine.
        lead = (
            f"verify with semantics='portable' to run on {e} (the plan was verified with "
            f"semantics={source!r}, whose proof does not carry over to {e})"
        )
        return refuse(f"{lead}; details: " + "; ".join(why_not), failures)
    reason = "; ".join(why_not)
    if route != "auto":
        # An explicit route is taken or refused, never replaced: say how to reach `e`.
        if source != "portable" and e in translated:
            reason += f"; verify with semantics='portable' to run on {e}, or pass route=\"auto\""
        else:
            reason += '; route="auto" tries every route'
    if not failures and e in _PENDING:
        reason += f" (pending: #{_PENDING[e]}, {_ISSUES}/{_PENDING[e]})"
    return refuse(reason, failures)
