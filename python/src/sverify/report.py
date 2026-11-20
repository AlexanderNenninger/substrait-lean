"""What a proof found: `Report`, its `Issue`s and their hints, the errors
that carry a report (`VerificationError`, `UnverifiedRunError`,
`PostconditionError`), and the abstract values the checker established, as
text (`render_fact`).

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release. The
layers are in `docs/layers.md`.
"""

from __future__ import annotations

import json
import math
import re
import warnings
from collections.abc import Callable, Collection, Mapping, Sequence
from dataclasses import dataclass, field, replace
from datetime import date, datetime, timedelta
from decimal import Decimal
from enum import StrEnum
from typing import TYPE_CHECKING, Any, Literal, overload

import ibis
import ibis.expr.types as ir
import pyarrow as pa
from ibis.common.deferred import Deferred

from sverify import _decimals, _deprecated, _hooks
from sverify import observation as _observation
from sverify._checker import decode_double
from sverify._dialect import DialectDifference
from sverify._run_schema import declared_columns, int_range, null_message, range_message
from sverify._run_schema import problems as schema_problems
from sverify._unsupported import SverifyError, SverifyWarning, UnsupportedError
from sverify.black_box import Law
from sverify.engine import (
    Connection,
    Engine,
    connection_of,
    plan_json,
    read_tables,
    run_guard_free,
    run_plan,
    written_plan,
)
from sverify.observation import Observation, _deterministic_arg
from sverify.routes import RouteError

if TYPE_CHECKING:
    from sverify.routes import Route, RouteKind
from sverify.conditions import (
    DATA_CHECK,
    ROWS_SHOWN,
    ArrivesWithin,
    CheckedCondition,
    Discharged,
    Inferred,
    Key,
    MaxRows,
    PlannedCondition,
    PreconditionError,
    References,
    RelationRows,
    RowsPer,
    TableCondition,
    Unique,
    _count,
    label,
    resolve,
)

Semantics = str
"""The profile a check is under: sverify's reference semantics (the
default), DuckDB's, whose SQL also means what DuckDB computes, or an
installed engine's profile (`ProfilePlugin.profile`): Polars's or Spark's,
or Substrait's own, as its extension YAMLs state it.
`sverify.contracts.semantics_names` lists them."""


def _transfer_failure(f: Mapping[str, Any]) -> str:
    """Why the reference's proof does not carry over to Substrait at one option."""
    where = f"{f['group']}'s {f['option']}" if f.get("group") else f["option"]
    return (
        f'not proved under semantics="substrait": {where} allows '
        f"{', '.join(f['substrait'])}, the reference only {', '.join(f['reference']) or 'nothing'}"
    )


Condition = (
    Deferred
    | ir.BooleanValue
    | str
    | Unique
    | Key
    | References
    | ArrivesWithin
    | MaxRows
    | RowsPer
    | Observation
    | PlannedCondition
    | Callable[[ir.Table], ir.BooleanValue]
)


Transform = ir.Table | str


UnprovedReason = Literal[
    "observation",
    "not_a_key",
    "ties",
    "always_false",
    "may_be_false",
    "may_be_null",
    "not_proved_kind",
    "unknown",
]
"""`CheckedCondition.reason`: why a postcondition is not proved."""


@dataclass(frozen=True)
class TiePlace:
    """A place where the plan leaves its result open: a window, an ordered
    aggregate (`first`, `group_concat`, …) or a `LIMIT` whose order is not
    total on the input's keys, or a value picked from a class of doubles."""

    relation: int
    """The relation's index in the plan, in pre-order (`Report.relations`)."""
    op: str
    """The relation's operator: `window`, `aggregate` or `fetch`."""
    what: str
    """What is open there, with columns as `$i` of the relation's input."""
    kind: Literal["tie", "class", "open"] = "tie"
    """`"class"`: the place only picks a member of a class of doubles
    (`-0.0` or `0.0`, a NaN; D31), which an observation that reads one zero
    and one NaN cannot tell apart (D48); `"tie"`: the order of ties is open;
    `"open"`: what the class level leaves open, a tie or an expression that
    reads a picked value (`Report.deterministic`)."""

    def __str__(self) -> str:
        return f"the {self.op} at relation {self.relation}: {self.what}"


def black_boxes_from_json(rows: Sequence[Mapping[str, Any]] | None) -> dict[str, tuple[Law, ...]]:
    """`Report.black_boxes` from the checker's `"black_boxes"` rows
    (`[{"name", "laws"}]`, each law a list such as `["at_least", 0]`); an
    absent key, from an older checker, reads as none."""
    return {b["name"]: tuple(tuple(law) for law in b.get("laws") or ()) for b in rows or ()}


def black_boxes_json(boxes: Mapping[str, tuple[Law, ...]]) -> list[dict[str, Any]]:
    """`Report.black_boxes` as the checker writes it, for `to_json`."""
    return [{"name": n, "laws": [list(law) for law in laws]} for n, laws in boxes.items()]


def tie_places(out: Mapping[str, Any]) -> list[TiePlace]:
    """The `tie_places` of `substrait-check`'s report: the exact level's."""
    return [
        TiePlace(t["relation"], t["op"], t["what"], t.get("kind", "tie"))
        for t in out.get("tie_places", [])
    ]


def class_places(out: Mapping[str, Any]) -> list[TiePlace]:
    """The `class_places` of `substrait-check`'s report: what the class
    level leaves open (D48). A checker without them gives the exact level's."""
    if "class_places" not in out:
        return tie_places(out)
    return [TiePlace(t["relation"], t["op"], t["what"], "open") for t in out["class_places"]]


#: What a report suggests for an overflow it cannot rule out (#202).
OVERFLOW_HINT = (
    "an integer result may not fit its type (64 bits for BIGINT, or a timestamp's "
    "range), which raises. Bound the columns involved in `requires`, as a fact about "
    "your data: for example `_.amount < 1_000_000_000`, or, for an ASOF join with a "
    "tolerance, a lower bound on its time column such as `_.ts >= datetime(2000, 1, 1)`"
)


#: How a report's hint for a truncated timestamp or date starts.
TRUNC_HINT = "bound the truncated column"


def _truncates(expr: str) -> bool:
    """Whether an issue's expression (`Expr.render`) truncates a timestamp or
    a date, or bins a timestamp."""
    return any(f in expr for f in ("DATE_TRUNC_", "DAY_TRUNC_", "BUCKET_"))


#: What `str(report)` adds to "proved" when the checker's generated proofs
#: were not checked (`substrait-check --build`, `docs/trusted-base.md`).
UNCHECKED_CHECKER = " by a checker whose generated proofs are unchecked"

#: How a report explains a `SUM` that may overflow: an error like any other,
#: which the job also checks while it runs.
RUNTIME_CHECK = (
    "the job also checks it while it runs and raises if it happens; a bound on "
    "the column and on the rows of a group rules it out"
)


def _pinned(table: Any) -> bool:
    """Does every read of `table` see the same rows: an Arrow table, a table
    DuckDB holds, or a Delta or Iceberg table's files at one version?"""
    import pyarrow

    from sverify._scan import Resident, Scan

    if isinstance(table, pyarrow.Table | Resident):
        return True
    return isinstance(table, Scan) and "@v" in table.origin


class InferredWarning(SverifyWarning):
    """A precondition sverify inferred is assumed (`on_inferred="warn"`), or a
    margin check flagged groups a run kept.

    Attributes:
        report: The `Report` whose `inferred` preconditions are assumed.
    """

    def __init__(self, message: str, report: Report | None = None):
        super().__init__(message)
        self.report = report


#: How a report explains a `SUM` it assumes fits (`Report.assumed`).
SUM_ASSUMED = (
    "fits {} in every group (checked at run time: the job raises if it does not; "
    'on_inferred="off" makes it an error)'
)


#: A decimal `SUM`'s argument in Lean's notation: `DECIMAL_p_s(…)`.
_DECIMAL_ARG = re.compile(r"DECIMAL_(\d+)_(\d+)\(")


#: How a report explains an operation it assumes stays finite (#575).
FINITE_ASSUMED = (
    "stays finite on finite inputs (checked at run time: the data is checked "
    'before the run, which is refused if it overflows to ±inf; on_inferred="off" '
    "makes it an error)"
)


#: The kind of an operation on finite doubles that may give `±∞` (#575).
INFINITE = "overflow to infinity"


#: What a report suggests for an operation that may overflow to `±∞` (#575).
INFINITE_HINT = (
    "no bound on a column proves a double operation finite; unless "
    'on_inferred="off", it is assumed and checked on the data while the job runs'
)


#: The kind of a decision on an `AVG` of integers that DuckDB may take the other way
#: (#1735, D52): the query's own `avg` is within a band of the value verified.
SOURCE_THRESHOLD = "source_threshold"

#: What a report says of such a decision (ruling 104): the construct, the consequence
#: and the ways out. 12b-2 restores the comparisons of the mean with integers.
SOURCE_THRESHOLD_HINT = (
    "DuckDB's AVG of integers returns a double within a band of the value sverify verified, "
    "so on DuckDB this query may keep other rows than the verified plan, or the column has "
    "no bound. Keep the mean away from the threshold with a precondition, or compare exact "
    "columns: SUM(y) > c * COUNT(y) for an integer c"
)


#: What a report says of a constant that raises (#609, D21).
CONSTANT_HINT = (
    "this operation reads no column and raises: DuckDB evaluates it when it "
    "plans the query, so the plan raises on any data, an empty table included, "
    "and no precondition rules it out. Fix or remove the constant"
)


def _sum(issue: Issue) -> bool:
    """Whether `issue` is a `SUM` that may leave its type."""
    return issue.kind == "SUM overflow"


def _assumption(issue: Issue) -> str:
    """How a report names an assumed issue."""
    if _sum(issue):
        return f"SUM of {issue.what} {_sum_assumed(issue)}"
    return f"{issue.shown or issue.expr} {FINITE_ASSUMED}"


def _cause(issue: Issue) -> str:
    """What makes an issue happen, where its kind does not say: a domain
    error of a double SUM or addition is NaN from +inf plus -inf."""
    if issue.kind != "domain error" or issue.shown is None:
        return ""
    m = re.fullmatch(r"(?:sum|avg|mean)\((\w+)\)(?: or \w+\(\1\))*", issue.shown)
    if m:
        return (
            f" (NaN where {m[1]} holds both +inf and -inf: bound it in requires, "
            f"e.g. `_.{m[1]}.between(-1e300, 1e300)`)"
        )
    if re.search(r" [-+] ", issue.shown):
        return " (NaN from +inf minus +inf: bound the columns in requires)"
    return ""


def _sum_assumed(issue: Issue) -> str:
    """`SUM_ASSUMED` for `issue`: 64 bits for an integer `SUM`, the result's
    `DECIMAL(min(38, p + 10), s)` for a decimal one (`Measure.sumOk`, #316)."""
    if m := _DECIMAL_ARG.match(issue.expr):
        p, s = int(m[1]), int(m[2])
        sp, ss = _decimals.sum_of((p, s))
        return SUM_ASSUMED.format(f"DECIMAL({sp}, {ss})")
    return SUM_ASSUMED.format("64 bits")


@dataclass(frozen=True)
class Issue:
    """Something that may go wrong when the transformation runs
    (`Rel.mayIssues_sound` in `analysis/Sverify/Analysis/Safety.lean`)."""

    kind: str
    """"division by zero", "overflow" (an integer result that does not fit its
    declared width, `MIN / -1`, …), "cast out of range", "negative exponent",
    "domain error", "SUM overflow" (a `SUM` leaving its type: 64 bits for
    integers, the result's precision for decimals), "overflow to infinity"
    (an operation on finite doubles, or their `SUM` or `AVG`, giving
    `±∞`), or "source_threshold" (a decision on DuckDB's `AVG` of integers,
    which DuckDB may take the other way, #1735)."""
    expr: str
    """The operation, in Lean's notation (`$i` is the operation's i-th input
    column)."""
    error: bool
    """True if a proof must rule it out. Every issue is one; a "SUM overflow"
    or an "overflow to infinity" is also checked while the job runs, where
    the transformation's SQL raises too."""
    hint: str | None = None
    """For an overflow: the bound that would rule it out, as code to add to
    a contract, or why no bound on a column does (`infer_bounds`). None if
    there is nothing to suggest."""
    column: str | None = None
    """For a "SUM overflow": the column the SUM adds up, named as in its
    hint (the base table's column where it is passed on unchanged). None if
    `expr` is not a single column."""
    constant: bool = False
    """The operation reads no column and raises: DuckDB evaluates
    such a constant when it plans the query, so the plan raises on any data,
    and no precondition rules it out (`CONSTANT_HINT`)."""
    under_and_or: bool = False
    """The operation sits inside an operand of an `AND` or `OR`, which
    evaluates both operands: a guard in the other operand does
    not keep it from raising. The report suggests a `CASE` (`AND_OR_HINT`)."""
    _labels: tuple[str, ...] = field(default=(), repr=False, compare=False)
    """The preconditions that rule it out, as labels, where the inference
    found them (`infer_bounds` assumes them)."""
    shown: str | None = None
    """The operation in the user's terms: column names and the Ibis or SQL
    operator (`total // qty`, `sum(x)`); None where the plan does not say
    which columns `expr` reads."""
    needs: list[Needed] = field(default_factory=list, compare=False)
    """The preconditions that rule it out, one `Needed` each, where the
    inference found them: what `hint` says to state in `requires`, as data.
    Empty where it found none."""
    hint_needs: dict[str, list[Condition]] = field(default_factory=dict, repr=False, compare=False)
    """The preconditions per input table that `hint` proposes, as code; a
    hint is shown only where a proof with them rules the issue out
    (`_confirm_hints`)."""
    unconfirmed: str | None = field(default=None, repr=False, compare=False)
    """The hint to show instead where a proof does not confirm `hint`."""
    assumed: bool = False
    """Assumed not to happen, and checked on the data while the job runs
    (`Issue.assumed` in `SubstraitLean/Issue.lean`, as the checker reports
    it): a `SUM` that may leave its type, or an operation on finite doubles
    that may give `±∞`."""

    @property
    def suggested(self) -> dict[str, tuple[str, ...]]:
        """Deprecated: `needs`. Its labels per input table."""
        warnings.warn(
            "Issue.suggested is deprecated; read Issue.needs",
            DeprecationWarning,
            stacklevel=2,
        )
        return _labels_by_table(self.needs)

    @property
    def what(self) -> str:
        """The column, or else the expression, a report names the issue by."""
        return self.column or self.shown or self.expr

    @property
    def message(self) -> str:
        """The issue in words, as `str(report)` prints it after "may fail: ":
        its kind, the operation, what causes it where the kind does not say,
        and, for one the job also checks while it runs, that it does."""
        return f"{self}{_cause(self)}" + (f" ({RUNTIME_CHECK})" if self.assumed else "")

    @property
    def assumption(self) -> str:
        """For an issue in `Report.assumed`: what the report assumes of it, as
        `str(report)` prints it after "assumes: "."""
        return _assumption(self)

    def __str__(self) -> str:
        return f"{self.kind}: {self.shown or self.expr}"


class Verdict(StrEnum):
    """What the checker proved about a transformation: `Report.verdict`.

    A verdict is not a boolean: `bool(verdict)` raises `TypeError`, so that
    `assert report.verdict` cannot pass on `UNPROVED`. Compare with the value
    you expect.
    """

    PROVED = "proved"
    """Every postcondition holds on every run, and no run raises."""
    PROVED_WITH_CHECKS = "proved_with_checks"
    """Every run that finishes satisfies the postconditions. A run stops where
    a check of `Report.assumed` fails on the data."""
    UNPROVED = "unproved"
    """A postcondition is not proved, a run-time error is possible, a
    precondition is needed, Substrait allows more, or no engine's doubles meet
    the observation."""

    def __bool__(self) -> bool:
        raise TypeError("a Verdict is not a bool: compare it with Verdict.PROVED, ...")


@dataclass
class Report:
    """What the checker proved about a transformation, returned by `verify` and kept
    in `ContractedTransform.report`.

    `str(report)` lists each postcondition with its status, the possible
    runtime errors and warnings, and what is known about each output column;
    in a notebook the report renders as tables.
    """

    requires: dict[str, list[str]]
    """The preconditions that were assumed, as labels, per input table."""
    ensures: list[CheckedCondition]
    """Each postcondition, in the order given: its label, whether it was
    proved, what the checker established about it, and a counterexample if one was
    found."""
    facts: dict[str, str] = field(default_factory=dict)
    """What the checker established about each output column."""
    not_null: list[str] = field(default_factory=list)
    """The output columns the checker proved never NULL, from what it
    established about them (`facts`), in the output's order. A stored node
    of a proved report writes them as NOT NULL columns."""
    deterministic: bool = True
    """True when every result the reference allows is one up to row order
    and up to the member of each class of doubles (`-0.0` and `0.0`; every
    NaN; D31, D48): `check_class_determined_sound`. A `DISTINCT` or a group
    key over doubles, `MIN`, `MAX` and `QUANTILE_DISC` only pick a member of
    a class, which leaves the result determined. False when rows may tie in
    the ORDER BY of a window or of an ordered aggregate (`first`, `last`,
    `group_concat`; without an `order_by` every row ties), when a `LIMIT`
    takes rows that tie in its `ORDER BY` or has none, when an expression
    reads a picked double and can tell the members apart (`atan2`), when the
    reference leaves a value open (the median of doubles), or where the
    checker has not proved an aggregate a function of its values. The
    engine then picks, and a rerun may pick another. The postconditions are
    proved for every choice. A rerun that must reproduce the result
    (`run(reproducible=sv.equivalent())`, a refresh, a sink's
    `reproducible=`) refuses such a plan and names each place; one whose
    observation reads the members of a class (exact doubles and zeros) also
    refuses each class pick (D48)."""
    _exact: bool = field(default=True, repr=False)
    """Every result the reference allows is one up to row order, members of
    a class included (`check_deterministic_sound`): `deterministic` with no
    class pick. The SQL writers' tie-free windows read this level."""
    _class_places: list[TiePlace] = field(default_factory=list, repr=False)
    """What the class level leaves open, one entry per place; empty exactly
    when `deterministic` (`Request.classDeterminedIn_eq`)."""
    _windows_total: bool = field(default=True, repr=False)
    """False only for the window and ordered-aggregate ties of
    `deterministic`."""
    _tie_places: list[TiePlace] = field(default_factory=list, repr=False)
    """Where the plan leaves its result open, one entry per window, ordered
    aggregate, `LIMIT` or value the reference leaves open, class picks
    included (kind `"class"`); empty exactly when `_exact`
    (`Request.deterministicIn_eq`)."""
    issues: list[Issue] = field(default_factory=list)
    """Runtime errors, SUM overflows among them, the checker could not rule out; when
    empty, the transformation provably runs without them."""
    _guard_free: bool = field(default=False, repr=False)
    """The only issues are assumed ones (`SUM`s that may overflow, double
    operations that may give `±∞`, which keep their checks): on data that meets
    the preconditions, the transformation's SQL (`sverify.engines.to_sql`)
    and Polars plan give the same result with `guards=False`, without
    per-row checks (`Rel.guardFree_sound`)."""
    _unchecked: dict | None = field(default=None, repr=False)
    """The expressions that run correctly without their checks, on data that
    meets the preconditions (`Rel.evalG_marks`), as a tree parallel to the
    plan; pass it to `sverify.engines.to_sql(..., unchecked=...)` with the
    same plan, and only the other expressions keep their checks. None when
    Lean found none (a left join with a filter on its right side, for one)."""
    _optimized: dict | None = field(default=None, repr=False)
    """The transformation as a Substrait JSON plan, rewritten with the facts
    and keys of the preconditions (`Rel.optimize` in
    `SubstraitLean/Semantic.lean`): for example a `DISTINCT` over a key is
    gone. On data that meets the preconditions it gives the same rows
    (`Rel.optimize_sound`); pass it to `sverify.engines.to_sql`, or as JSON
    to `sverify.engines.run`, instead of the transformation. None if Lean
    did not return one."""
    _rewrites: list[str] = field(default_factory=list, repr=False)
    """The rewrites in `optimized`, such as "DISTINCT on a key"."""
    _run_plan: dict | None = field(default=None, repr=False)
    """The plan an engine runs on a route that rests on this report
    (`_plan_to_run`): the transformation rewritten by the rules the gate turns
    on, where every gate passes (`Request.runPlanIn` in
    `SubstraitLean/RunPlan.lean`, `check_run_plan_sound`). None where a gate
    keeps the plan as written (`_run_gate`)."""
    _run_gate: str | None = field(default=None, repr=False)
    """The gate that kept the plan as written (`"no_rewrite"`, `"profile"`,
    `"rows"`, `"issues"`, `"guard_free"`, `"near"`, `"closed"`, `"reads"`,
    `"functions"`, or `"writer"` where an engine's writer refused the
    rewrite), or None where the plan to run is the rewrite."""
    _run_unchecked: dict | None = field(default=None, repr=False)
    """`_unchecked` for `_run_plan`: the marks of its expressions."""
    _run_gates: dict[str, str] = field(default_factory=dict, repr=False, compare=False)
    """Per engine (or `"to_sql"`), why its last run took the plan as written
    where the checker gave a rewrite (`_run_gate` is None): `"route"` (a route
    that does not rest on this report), `"unchecked"` (the run did not check
    the preconditions on its data, or `to_sql` without `optimize=True`),
    `"optimize"` (`run(optimize=False)`) or `"writer"` (the engine's writer
    refused the rewrite). A run's own gate, apart from
    the checker's (ruling 150, C2)."""
    _inferred: dict[str, list[Condition]] = field(default_factory=dict, repr=False)
    """The bounds inferred to rule out overflow (`infer_bounds`), per input
    table: also in `requires`, and assumed like the rest of it."""
    _implied: dict[str, str] = field(default_factory=dict, repr=False)
    """A SQL condition per input table that every row reaching the result
    passes, given `requires` (#81, `Rel.need_eval` in
    `SubstraitLean/Implied.lean`): the transformation gives the same result
    on the table's rows that pass it. `sverify.io` sources read only those,
    and skip the files whose statistics rule it out."""
    assumed: list[Issue] = field(default_factory=list)
    """The `SUM`s assumed to fit their type in every group (64 bits for
    integers, the result's precision for decimals), and the operations on
    finite doubles assumed to stay finite: those the inputs' row caps
    (`max_rows`) and the values' range do not prove to fit. The job
    checks each at run time, on the data, and raises where one fails. The
    proof holds under these assumptions (`Rel.noIssue_of_assumedHold`). With
    `on_inferred="off"` they are errors instead."""
    _table_params: dict[str, str] = field(default_factory=dict, repr=False, compare=False)
    """For an input table the proof names (a base table, or the placeholder of a
    contracted upstream result), the transform's parameter it is bound to: the
    text says `requires orders`, the name in the transform's own `requires`, not
    the upstream node that feeds it (#1485)."""
    _params: list[str] = field(default_factory=list, repr=False)
    """The `ibis.param` values the transformation was verified with
    (`verify(..., params=...)`), as `param1 (int64) = 5`: every proof is for
    these values only."""
    _hints: list[str] = field(default_factory=list, repr=False)
    """What to add to the contract for the `issues` it names (#379): bounds
    on a truncated timestamp column, or on the column an integer `SUM` adds
    up, with the largest group the bound lets fit."""
    _bounds: dict[str, tuple[int | None, int | None]] = field(
        default_factory=dict, repr=False, compare=False
    )
    rows: int | None = None
    """At most this many output rows, from the inputs' row caps (`max_rows`
    in `requires`, `Rel.maxRows`); None if nothing bounds them."""
    _relations: list[RelationRows] = field(default_factory=list, repr=False, compare=False)
    """Each relation of the plan, from the result down in pre-order, with
    the bounds Lean proves on its rows and, for an aggregate, on the rows
    of a group (#219)."""
    semantics: Semantics = "reference"
    """The profile the report is under (`verify(semantics=...)`):
    `"reference"`, sverify's reference semantics; `"duckdb"`, what DuckDB
    computes; `"polars"`; `"spark"`; or `"substrait"`, Substrait's own."""
    """The integer bounds Lean found on each integer output column, lowest
    and highest (None: unbounded), for hints."""
    internal_plan: str | None = field(default=None, repr=False, compare=False)
    """The plan the report is about, as Substrait protobuf JSON: the
    transformation as `verify` compiled it and Lean checked it, with the
    `params` bound and the SQL lifted with `semantics`. `run` runs it."""
    observation: Observation = field(default_factory=lambda: _observation.PLAN_BOUND)
    """What the result's consumer observes (`sv.equivalent` in `ensures`).
    When `ensures` names none: rows and list elements as multisets, one zero
    and one NaN (`zeros="canon"`), doubles within the plan's bound
    (`floats="plan"`, printed with the bound, `epsilon`) and other values
    exact (`sverify.observation.PLAN_BOUND`). Under
    the plan's bound a run holds the double columns a postcondition reads
    to their exact value (`sverify.routes.observed`). `equivalence` is the same, by the
    concept's name."""
    _stated: bool = field(default=False, repr=False, compare=False)
    """Whether `ensures` names the observation (`sv.equivalent`)."""
    _floats_on: dict[str, list[str]] = field(default_factory=dict, repr=False, compare=False)
    """Where the observation asks for exact doubles or a tolerance: per
    engine the reference translates to, why that engine's doubles may not
    meet it (empty where they do), checked against the plan's bound
    (`epsilon`) at `verify`. Empty under `floats="plan"`, which every
    engine meets. Where no engine meets it, the plan is not proved
    (`floats_unmet`)."""
    _depends: list[dict] | None = field(default=None, repr=False, compare=False)
    """The options of the profile the proof depends on (`docs/core-semantics.md`,
    step 3c), as the checker reports them: `{"group", "option",
    "behaviours"}` rows. None when the checker does not report them; the
    option-wise transfer check then takes every option of every group the
    plan calls."""
    routes: dict[str, Route] = field(default_factory=dict, repr=False, compare=False)
    """The route each engine ran the plan by (`run(..., route=...)`), by
    engine name."""
    _contract: dict | None = field(default=None, repr=False, compare=False)
    """The request the checker proved, for a check under another profile."""
    _transfer: list[dict] | None = field(default=None, repr=False, compare=False)
    """Under `semantics="substrait"`, the options where Substrait allows more
    than the reference, so that the reference's proof does not carry over:
    `{"group", "option", "preferences", "substrait", "reference"}` rows, each
    with the behaviours the profile allows. Empty when it carries over; None
    under every other profile."""
    output: dict[str, Any] = field(default_factory=dict, repr=False, compare=False)
    """The output's columns with their Ibis types, a decimal's precision and
    scale as the reference types them (`docs/reference-semantics.md`, Decimals):
    the checker's, which a run returns, not Ibis's."""
    _epsilon: dict[str, dict[str, Any]] | None = field(default=None, repr=False, compare=False)
    """How far each double output column may be from a result the reference
    allows on an engine whose summation order differs (`{"abs", "rel"}` per
    column, #568), as the checker computes it for this plan; None where it
    does not."""
    _asof_checks: list[dict[str, Any]] = field(default_factory=list, repr=False, compare=False)
    """Per as-of join of the plan (#1447, `Rel.asofSite`), a plan that counts
    the pairs its range join compares (`AsofSite.pairs`). `run` runs each on
    the engine first and refuses the run above `_asof_max_pairs`
    (`check_asof_pairs`)."""
    _asof_max_pairs: int | None = field(default=None, repr=False, compare=False)
    """The smallest `max_pairs` of the transform's `asof_join` calls; None: no
    cap (a SQL query's `ASOF JOIN`, or `max_pairs=None`)."""
    _margin_checks: list[dict[str, Any]] = field(default_factory=list, repr=False, compare=False)
    """The margin checks of the plan's threshold filters on double sums
    (#929): per filter, a plan that counts the groups whose sum lies within
    its bound's margin of the threshold (`Rel.marginCheck`). `run` runs each
    on the engine before the plan (`check_margins`); `rows_exact` holds
    given them."""
    black_boxes: Mapping[str, tuple[Law, ...]] = field(
        default_factory=dict, repr=False, compare=False
    )
    """The black boxes the transformation calls, in the order of first call,
    each with the laws its row declares, as `sverify.black_box.Law` tuples
    (`("non_null",)`, `("at_least", 0)`), from the checker (#1484). The proofs
    trust a black box for these laws, its signature and its strictness, and
    `test_black_box.py` tests them (D16); no run checks them on the data. The
    verdict does not read this field."""
    _margin_flags: dict[str, int] = field(default_factory=dict, repr=False, compare=False)
    """After a run with `on_inferred="warn"`, per engine, the groups the
    margin checks flagged (#929): for those, the contract holds up to the
    sum's bound."""
    _rows_exact: dict[str, bool] | None = field(default=None, repr=False, compare=False)
    """Per engine, whether every filter, key and sort of the plan keeps the
    same rows and groups under the columns' `ε` (#568's threshold rule): a
    comparison on a double whose threshold lies within `ε` of its range may
    flip. None where the checker does not say."""
    _engines: dict[str, dict[str, Any]] | None = field(default=None, repr=False, compare=False)
    """Per engine, the checker's verdict on the plan's translation from the
    reference (`SubstraitLean/Realize.lean`, #1166): its class and evidence
    over the options the proof depends on, the theorems and facts, the shims,
    the options realized only up to an observation, what refuses it, and the
    transfer check from each other profile. None from a checker without it."""
    _generated_proofs: bool | None = field(default=None, repr=False, compare=False)
    """Whether the checker that made this report had checked its generated
    lift and lowering proofs (`substrait-check --build`); None where it does
    not say. A checker without them proves with `sorry` in their place."""
    _sorted: bool | None = field(default=None, repr=False, compare=False)
    """Whether the plan's result comes out of a sort, as the checker reads it."""
    _conditions: dict[str, list[Condition]] = field(default_factory=dict, repr=False, compare=False)
    _dialect: Literal["ibis", "sql"] = field(default="ibis", repr=False, compare=False)
    """The language of the transformation: the report names functions and
    writes code in it."""
    ties: dict[str, list[str]] = field(default_factory=dict, repr=False, compare=False)
    """For a result not determined up to row order (`deterministic`), the
    `sv.unique(...)` per input table that would determine it: the partition
    (or grouping) and order columns of its windows and ordered aggregates."""
    dialect_differences: tuple[DialectDifference, ...] = field(default=(), compare=False)
    """For SQL, where the reference reads the text differently from DuckDB, as
    a value it gives and DuckDB does not: a double or decimal cast to an
    integer (the reference truncates, DuckDB rounds) and `corr` of one pair
    or a constant side (NULL, NaN). Each entry has the construct, where it
    is, both readings, an example, and the spellings that mean the same under
    both semantics. Empty under `semantics="duckdb"` and for an Ibis
    transformation (`docs/reference-semantics.md`, "DuckDB SQL under the
    reference"). The verdict is unchanged: the list says what the proof
    covers."""
    # What an inferred precondition does (`verify(on_inferred=...)`): an error
    # unless the caller says otherwise (D23).
    _on_inferred: OnInferred = field(default="error", repr=False, compare=False)
    """What the inferred preconditions (`inferred`) do to the proof
    (`verify(on_inferred=...)`): with `"error"`, a plan that needs one is
    not proved (`needed`)."""
    _inferred_from: dict[str, Issue] = field(default_factory=dict, repr=False, compare=False)
    """For each inferred precondition (by label), the runtime error it rules
    out: where it came from."""
    """The preconditions per input table, as conditions: `requires` and
    the bounds inferred (`inferred`). `check_inputs` checks them on data."""
    _postconditions: list[Condition] = field(default_factory=list, repr=False, compare=False)
    """The postconditions, as conditions, in the order of `ensures`
    (`to_substrait` ships them)."""
    inputs: dict[str, ibis.Schema] = field(default_factory=dict, repr=False, compare=False)
    """The schema of each input table the plan reads, by table name: the
    columns `requires` may name, per table, as `output` holds those
    `ensures` may name."""
    preconditions: list[Discharged] = field(default_factory=list, repr=False, compare=False)
    """How each precondition on a bound input was established in the call
    that made this report: from its schema, from metadata (`sverify.io`
    tables) or on the data. Empty for a report of unbound tables; a refresh
    reports its own (`StageRefresh.preconditions`)."""

    def to_json(self, indent: int | None = None) -> str:
        """The report as a versioned JSON document, for CI jobs and tools,
        in the format of `sverify/schemas/report.schema.json`:
        `format` (1), the verdict, each postcondition with its status and
        `reason`, the runtime errors and assumptions, `needs`, the facts on
        each output column, the routes engines ran the plan by, and the rest
        `str(report)` says. Conditions appear as their labels. Within 1.x
        the format only gains keys (`docs/stability.md`).

        Args:
            indent: Indent the JSON by this many spaces; None writes one line.

        Returns:
            The JSON document, keys sorted.
        """
        return json.dumps(_hooks.report_json().to_json(self), indent=indent, sort_keys=True)

    @staticmethod
    def from_json(data: str | Mapping[str, Any]) -> Report:
        """A report from what `to_json` wrote, by this version of sverify or
        an earlier one. Keys this version does not know are left out.

        The report has the same verdict, postconditions, issues, needs,
        facts and routes. It holds no plan, and its conditions are their
        labels, so it does not `run`, `check_inputs` or `to_substrait`.

        Args:
            data: The JSON, as text or parsed.

        Returns:
            The report.

        Raises:
            ValueError: The document's `format` is newer than this version
                reads.
        """
        return _hooks.report_json().from_json(data)

    @staticmethod
    def from_substrait(data: str | bytes | Mapping[str, Any]) -> Report:
        """Read a plan `to_substrait` exported, and prove its contract again
        with the checker.

        The plan goes to the checker as it was exported, pinned options,
        shims and all, with the preconditions and postconditions it
        carries; the report says what the checker proves of it now. For an
        export of a verified plan, `proved` is true again, with the same
        postconditions.

        Args:
            data: The export: protobuf JSON (a string or its dict) or bytes.

        Returns:
            A `Report` of the plan: its postconditions with their status,
            the runtime errors the checker cannot rule out, the facts on
            each output column and the options the proof depends on. Facts
            are in Lean's notation, and nothing is known of the Ibis types.

        Raises:
            ValueError: The plan carries no sverify contract, or the
                checker rejects the plan.
        """
        return _hooks.export().recheck(data)

    @overload
    def to_substrait(
        self,
        format: Literal["json"] = "json",
        *,
        shims: Literal["apply", "annotate", "refuse"] = "apply",
    ) -> str: ...

    @overload
    def to_substrait(
        self,
        format: Literal["binary"],
        *,
        shims: Literal["apply", "annotate", "refuse"] = "apply",
    ) -> bytes: ...

    def to_substrait(
        self,
        format: Literal["json", "binary"] = "json",
        *,
        shims: Literal["apply", "annotate", "refuse"] = "apply",
    ) -> str | bytes:
        """The verified plan for any conforming Substrait consumer, with its
        contract as metadata.

        Every function call names its YAML's URN, its compound name and its
        output type (Substrait 0.106). Every option the proof depends on
        (`depends`) is pinned in the call's options at the reference's
        behaviour. Where Substrait has no option for a choice the proof uses
        (a spec gap, `upstream/bugs/ST-*.json`), `shims` decides: `"apply"`
        rewrites the plan into well-specified Substrait, `"annotate"` keeps
        it and records the choice in the metadata as an assumption the
        consumer must honour, and `"refuse"` refuses the export. A gap where
        the reference raises needs no shim in any mode: the preconditions,
        which travel with the plan, rule those inputs out.

        The contract travels in the plan's `advanced_extensions` as an
        `io.sverify.substrait.v1.Contract`: `requires` (declared, inferred
        and assumed) and `ensures`, each in your terms and as a Substrait
        plan, and a manifest (the profile, the pinned options, the shims and
        assumptions, the observation the result holds up to, the Substrait
        version and extension URNs, sverify's version). `sv.Report.from_substrait`
        reads it back and proves the contract again.

        Args:
            format: `"json"` (protobuf JSON, a string) or `"binary"` (the
                serialized `substrait.Plan`).
            shims: What to do at a spec gap the proof depends on.

        Returns:
            The plan, as protobuf JSON or bytes.

        Raises:
            sverify.errors.ExportError: The report is not proved,
                or the plan has no conforming Substrait form that keeps the
                proof; the message names the reason and the gap.
        """
        return _hooks.export().export(self, format, shims=shims)

    def substrait_contract(
        self, *, shims: Literal["apply", "annotate", "refuse"] = "apply"
    ) -> dict:
        """The contract `to_substrait` embeds, as JSON, for a sidecar file."""
        return _hooks.export().contract_json(self, shims=shims)

    def to_sql(self, dialect: Any = "duckdb", *, optimize: bool = False) -> str:
        """The verified plan as SQL whose meaning is the proof's, in
        `dialect`.

        The SQL keeps every run-time check, as `run` does. Where the report
        is determined up to row order with no class pick (no window ties on
        data that meets the preconditions), windows need no row-order tiebreak, so Snowflake and
        Spark take them. A plan verified under an engine's semantics
        (`semantics="duckdb"`) is written only for an engine its route
        reaches (`sverify.routes.choose`). Snowflake takes plans verified
        under the reference. Run the SQL on data that meets the
        preconditions (`requires`); `run` checks them first
        (`check_inputs`).

        Args:
            dialect: `"duckdb"` (the default), `"snowflake"` or `"spark"`,
                or a `Dialect` (`sverify.sql.dialect_of`).
            optimize: Write the plan the checker rewrote with the facts of
                the preconditions (`docs/optimizations.md`, "The gate"), where
                it gave one. It gives the plan's rows only on data that meets
                the preconditions, which nothing checks for this SQL, so pass
                it only for data you know meets them. Default False: the plan
                as written. The name is provisional (#1787).

        Returns:
            One SQL query, reading the plan's tables by the names it was
            verified with.

        Raises:
            ValueError: The report has no plan (it was not made by
                `verify`), or `dialect` is unknown.
            sverify.errors.UnverifiedRunError: The plan is not proved.
            sverify.errors.RouteError: No route takes the plan to the
                dialect's engine.
            sverify.errors.Unsupported: The dialect cannot express the plan.

        Examples:
            ```python
            report = sv.verify(
                "SELECT host, max(cpu) AS m FROM t GROUP BY host",
                tables={"t": t},
                ensures=[sv.unique("host")],
            )
            print(report.to_sql("snowflake"))
            ```
        """
        from sverify.sql import to_sql

        if self.internal_plan is None:
            raise ValueError("this report has no plan: it was not made by sv.verify")
        d, finite = self._sql_route(dialect)
        # The SQL runs on data nothing here checks, so it is the plan as
        # written: the rewrite rests on the preconditions (ruling 150, C1).
        return to_sql(
            self._plan_to_run("translated", checked=optimize, engine="to_sql"),
            d,
            deterministic=self._exact,
            finite=finite,
            rows="sequence" if self.observation.rows == "sequence" else "multiset",
        )

    def _plan_to_run(self, kind: str | None, *, checked: bool, engine: str) -> str:
        """The plan `engine` runs on the route `kind`, as JSON text: the
        checker's plan to run (`_run_plan`) where the route rests on this
        report (`routes.runs_rewrite`) and the run checked the preconditions on
        its data (`checked`), since every rewrite rests on them (ruling 150,
        C1); the plan as written otherwise, with the reason in
        `_run_gates[engine]`. The one place a run reads the plan (#1787)."""
        from sverify import routes

        assert self.internal_plan is not None
        written = written_plan(self.internal_plan)
        if self._run_plan is None:
            return written
        if not routes.runs_rewrite(kind):
            self._run_gates[engine] = "route"
            return written
        if not checked:
            self._run_gates[engine] = "unchecked"
            return written
        self._run_gates.pop(engine, None)
        return json.dumps(self._run_plan)

    def _with_plan(
        self,
        plan: str,
        engine: str,
        f: Callable[[str], Any],
        recheck: Callable[[str], Any] | None = None,
    ) -> Any:
        """`f` on `plan`, the plan `_plan_to_run` chose. Where `engine`'s
        writer refuses the rewrite (`UnsupportedError`), the run's own checks
        (`recheck`) and `f` on the plan as written, with `"writer"` in
        `_run_gates[engine]`: the checker accepted both, so either run is sound
        (ruling 129, E), and a run checks the plan it runs."""
        assert self.internal_plan is not None
        written = written_plan(self.internal_plan)
        if plan == written:
            return f(plan)
        try:
            return f(plan)
        except UnsupportedError:
            self._run_gates[engine] = "writer"
            if recheck is not None:
                recheck(written)
            return f(written)

    def _sql_route(self, dialect: Any) -> tuple[Any, bool]:
        """The dialect `dialect` names, and whether its SQL checks the
        reference's `±∞` precondition, for this report's plan; refused as
        `run` refuses it."""
        from sverify import routes
        from sverify.sql import dialect_of

        d = dialect_of(dialect)
        if d.name in routes.translations():
            chosen = routes.choose(self, d.name)
        else:
            # An engine without a profile, built in or installed
            # (`sverify.profiles`), takes the reference's translation, with no
            # class claimed.
            reason = None
            if not routes.verified(self):
                reason = routes.not_verified(self)
            elif self.semantics != "reference":
                reason = (
                    f"verified under {self.semantics} semantics; {d.name} SQL is written "
                    "only for plans verified under the reference"
                )
            chosen = routes.Route(
                d.name,
                None if reason else "translated",
                self.semantics,
                reason or "the reference's translation",
                self.deterministic,
                cls="refused" if reason else None,
            )
        if chosen.refused:
            reason = chosen.reason.removesuffix("; run(..., unverified=True) runs it anyway")
            chosen = replace(chosen, reason=reason)
            if not routes.verified(self):
                raise UnverifiedRunError(self, chosen)
            raise routes.RouteError(chosen)
        return d, self.semantics == "reference" or chosen.kind == "translated"

    def check_inputs(
        self,
        con: Connection,
        engine: str | None = None,
        *,
        assumed_checked: bool = False,
        _plan: str | None = None,
    ) -> None:
        """Check the tables of `con` against the schema the plan was verified
        for (`_check_schema`), the preconditions (`requires`, the inferred
        bounds among them) and the `SUM`s assumed to fit (`assumed`), before
        anything runs: a batch that breaks one is refused before the run, with
        the schema difference or the precondition as the message.

        With an `engine`, each table's conditions run there, as one plan the
        checker wrote (`condition_query`): a result that is not TRUE, or a
        plan that raises, is a violation, and a condition the engine's writer
        refuses refuses the check. Without one, Ibis counts on the table's own
        backend.

        Args:
            con: The connection holding the tables.
            engine: The engine to check the conditions on.
            assumed_checked: The run's engine checks the assumed issues as it
                runs its translation (`ProfilePlugin.checks_assumed`), so they
                are not run once more here on DuckDB.

        Raises:
            PreconditionError: A precondition or an assumed `SUM` does not
                hold on the data.
        """
        self._check_schema(con, engine)
        for t, conds in self._conditions.items():
            if not con.has(t):
                continue
            table = con.table(t)
            for c, n, error in violation_counts(table, conds, engine):
                if n or error:
                    what = (
                        f"{label(c)} raised on {t}: {error}"
                        if error
                        else f"{n} row(s) of {t} violate {label(c)}"
                    )
                    raise PreconditionError(
                        f"{what}: refused before the run" + self._source(t, c),
                        source=t,
                        condition=c,
                        rows=violating_rows(table, c),
                    )
        if self.assumed and self.internal_plan is not None and not assumed_checked:
            # On the plan that runs (`_plan`, #1787); the plan as written for
            # a caller outside `run`.
            self._check_assumed(con, _plan or written_plan(self.internal_plan))

    def _check_assumed(self, con: Connection, plan: str) -> None:
        """Check the assumptions on `plan` before an engine whose translation
        does not check them as it runs (a route or an engine without
        `checks_assumed`): the proved DuckDB translation checks a SUM as it
        adds up, an operation on finite doubles as it gives its result (#575)."""
        try:
            run_plan(con, plan, "duckdb")
        except Exception as e:
            raise self._broken_assumption(e) or e from None

    def _check_schema(self, con: Connection, engine: str | None) -> None:
        """Refuse a table that differs from the schema the plan was verified
        for (`refuse_schema`)."""
        if self.internal_plan is not None:
            refuse_schema(json.loads(self.internal_plan), con, engine)

    def _unchecked_requires(self) -> list[str]:
        """The preconditions in `requires` that `_conditions` holds no check
        for, as `table: label`."""
        have = {t: [label(c) for c in cs] for t, cs in self._conditions.items()}
        out = []
        for t, labs in self.requires.items():
            left = list(have.get(t, []))
            for lab in labs:
                if lab in left:
                    left.remove(lab)
                else:
                    out.append(f"{t}: {lab}")
        return out

    def _broken_assumption(self, e: Exception) -> PreconditionError | None:
        """The refusal for an error of an engine's translation that says an
        assumed `SUM` or operation on finite doubles failed on the data; None
        for any other error."""
        message = str(e)
        issues = ("SUM overflow", "overflow to infinity")  # a Polars guard's `issue`
        if not (
            getattr(e, "issue", None) in issues
            or "overflow in SUM" in message
            or "overflow to infinity" in message
        ):
            return None
        broken = ", ".join(_assumption(i) for i in self.assumed)
        err = PreconditionError(
            f"the batch breaks an assumed precondition, {broken}: refused before the run"
        )
        err.__cause__ = e
        return err

    def _source(self, table: str, c: Condition) -> str:
        """Where a precondition the data breaks came from, and what to do,
        for one the report inferred."""
        lab = label(c)
        if lab not in {label(x) for x in self._inferred.get(table, [])}:
            return ""
        issue = self._inferred_from.get(lab)
        where = f" ({issue.kind} otherwise)" if issue is not None else ""
        what = f" from `{issue.what}`{where}" if issue is not None else ""
        return (
            f". The precondition was inferred{what}: drop those rows before the transform, "
            f"`{table}.filter({lab})`, and compute on the rest; or guard the "
            "operation with a CASE; or state the precondition in requires as a fact "
            "about your data"
            if issue is not None
            else f". The precondition was inferred: drop those rows first, `{table}.filter({lab})`"
        )

    def run(
        self,
        con: Connection,
        engine: Engine | Any = None,
        *,
        route: RouteKind | Literal["auto"] = "auto",
        unverified: bool = False,
        reproducible: Observation | None = None,
        check_requires: bool = True,
        streaming: Literal["allow", "require"] = "allow",
        deterministic: bool | None = None,
        optimize: bool = True,
    ) -> pa.Table:
        """Run the plan this report checked (`plan`) over the tables of
        `con`, so the result is the one the report is about.

        The plan reads the tables by the names it was verified with, and
        runs on `engine` as `sverify.engines.run` runs a plan, with the
        meaning `Rel.eval` gives it.

        A plan that is not proved (`proved` is False) is refused
        (`UnverifiedRunError`), with what was not proved in the message;
        `unverified=True` runs it anyway, and
        says so: a warning (`UnverifiedRunWarning`), the route `"unverified"`
        in `routes`, and `sverify.verified: false` in the result's schema
        metadata.

        The run first chooses how the proof reaches the engine
        (`sverify.routes.choose`): `"auto"` takes the plan natively
        where it was verified under the engine's profile, through the
        reference's translation where it was verified under the reference,
        by the option-wise transfer check, or by a re-check under the
        engine's profile, and refuses it otherwise. The route goes into
        `routes`. Where `ensures` names no observation (`sv.equivalent`),
        the engine's doubles may differ from the reference's within the
        plan's bound (`epsilon`), except in the columns a postcondition
        reads.

        Args:
            con: The connection whose tables the plan reads (`sv.connect()`).
            engine: `"duckdb"`, `"polars"`, `"spark"`, or a
                Spark session. Default: the connection's engine.
            route: `"auto"` (the default) chooses a route; `"native"`,
                `"translated"`, `"transfer"` or `"recheck"` takes that one or
                refuses (`"reference"` is a deprecated alias of
                `"translated"`).
            unverified: Run a plan that is not proved, without a route.
                Default False: such a plan is refused.
            reproducible: What a rerun must reproduce: the
                engine's run-to-run variation must refine it, as a sink's
                `reproducible=` states it; `sv.equivalent()` asks for the
                same rows and bits. Default None: determinism is only
                reported (`deterministic`).
            check_requires: Check the preconditions (`requires`, the
                inferred bounds among them) and the assumed `SUM`s on the
                tables of `con` before the run, and refuse a batch that
                breaks one (`check_inputs`), as
                `transform(check_requires=)` does on bound inputs. Default
                True. False skips the check, for a caller that has made it
                already (the tables are still checked against the schema the
                plan was verified for: types, NULLs, integer widths). The
                report's guarantee then holds only on data that meets the
                preconditions, and a batch that does not may raise on the
                engine. With the check, a guard-free plan on the reference's
                route runs without the per-row checks the checker discharged
                on data that meets them, on an engine whose writer a theorem
                covers without them (`guard_free`; Polars, `Rel.polars_sound`);
                the checks of the assumed `SUM`s and `±∞` stay. Without it,
                and on the other engines, every check stays.
            streaming: On Polars, `"require"` refuses a plan any of whose
                nodes runs on the in-memory engine
                (`sverify_polars.engine.fallback_nodes`); `"allow"` (the default)
                runs it. Either way a chosen route records the nodes in
                `Route.fallbacks`.
            optimize: Run the plan the checker rewrote with the facts of the
                preconditions (`docs/optimizations.md`, "The gate"), where it
                gave one and this run checks the preconditions on the data
                (`check_requires`). Default True; False runs the plan as
                written. The name is provisional (#1787).

        Returns:
            The result as an Arrow table, with the transformation's output
            names.

        Raises:
            ValueError: The report has no plan (it was not made by
                `verify`), or `engine` is unknown.
            sverify.errors.UnverifiedRunError: The plan is not proved, and
                `unverified` is False. It is a `VerificationError` and a
                `RouteError`.
            sverify.errors.RouteError: No route takes the plan to `engine`,
                or, with `streaming="require"`, a node of its Polars plan
                runs on the in-memory engine.
            sverify.routes.EngineVersionError: The engine's major version is
                not the one its profile's facts were probed at.
            sverify.errors.PreconditionError: With `check_inputs`, a
                precondition does not hold on the data: nothing ran.

        Examples:
            Verify a query, then run what was verified:

            ```python
            con = sv.connect()
            con.put("t", pa.table({"host": ["a", "a", "b"], "cpu": [1, 5, 7]}))
            report = sv.verify(
                "SELECT host, max(cpu) AS m FROM t WHERE cpu > 3 GROUP BY host",
                tables={"t": con.table("t")},
                ensures=[sv.unique("host")],
            )
            result = report.run(con)  # refused if report.verdict is unproved
            ```
        """
        from sverify import profiles, routes

        if self.internal_plan is None:
            raise ValueError("this report has no plan to run: it was not made by sv.verify")
        reproducible = _deterministic_arg("Report.run", deterministic, reproducible)
        kind: str | None = None
        target = engine if engine is not None else con.engine
        chosen = None
        if unverified and not routes.verified(self):
            chosen = routes.unverified(self, target)
            self.routes[chosen.engine] = chosen
            kind = chosen.kind
            warnings.warn(
                f"running on {chosen.engine} unverified: {chosen.reason}",
                routes.UnverifiedRunWarning,
                stacklevel=2,
            )
        else:
            chosen = routes.choose(self, target, route, reproducible=reproducible)
            self.routes[chosen.engine] = chosen
            kind = chosen.kind
            if chosen.refused:
                if not routes.verified(self):
                    raise UnverifiedRunError(self, chosen)
                raise routes.RouteError(chosen)
        # The engine's translation of the plan checks each assumption as it
        # runs (`ProfilePlugin.checks_assumed`).
        run_on = profiles.find(chosen.engine) if chosen is not None else None
        assumed_checked = (
            check_requires and run_on is not None and run_on.checks_assumed and kind == "translated"
        )
        # The plan this run runs, decided once: the checks below and the run
        # read the same one.
        run_engine = chosen.engine if chosen is not None else str(target)
        plan = self._plan_to_run(kind, checked=check_requires, engine=run_engine)
        # Opting out names its own gate only where it changed the plan, and
        # keeps an earlier reason ("route", "unchecked") otherwise.
        if not optimize and self.internal_plan is not None:
            written = written_plan(self.internal_plan)
            if plan != written:
                plan = written
                self._run_gates[run_engine] = "optimize"
        if check_requires:
            # A precondition with no check would let the run drop guards on
            # data it never looked at: refuse before anything runs.
            if unchecked := self._unchecked_requires():
                raise PreconditionError(
                    "no run-time check for the precondition(s) "
                    + ", ".join(unchecked)
                    + " of this report: refused before the run (check_requires=False skips them)"
                )
            self.check_inputs(con, target, assumed_checked=assumed_checked, _plan=plan)
        else:
            # The proof is about this schema, so it is checked whatever
            # `check_requires` says.
            self._check_schema(con, target)
        self.check_asof_pairs(con, engine)
        if kind != "unverified":
            self.check_margins(con, engine, target, reproducible is not None)
        plugin = profiles.find(target)
        fallbacks = plugin.fallbacks if plugin is not None else None
        if (
            plugin is not None
            and fallbacks is not None
            and (chosen is not None or streaming == "require")
        ):
            self._streaming(con, chosen, streaming, plugin.engine, fallbacks, plan)
        # The check of an overflow to ±∞ is the reference's precondition
        # (#575): it is written for a plan verified under the reference, and
        # for one that reaches the engine through the reference's route.
        finite = self.semantics == "reference" or kind == "translated"
        # The checks the checker discharged (#1166): where the preconditions
        # were checked on these tables and the plan runs by the reference's
        # translation, a guard-free plan runs without its per-row checks on an
        # engine whose writer a theorem covers without them, as the checker
        # names it (`"guard_free_theorem"`); the assumed issues keep theirs.
        name = chosen.engine if chosen is not None else ""
        theorem = ((self._engines or {}).get(name) or {}).get("guard_free_theorem")

        def recheck(written: str) -> None:
            """The run's checks of the plan it runs, again for the plan as
            written after a writer refused the rewrite."""
            if check_requires and self.assumed and not assumed_checked:
                self._check_assumed(con, written)
            if plugin is not None and fallbacks is not None and chosen is not None:
                self._streaming(con, chosen, streaming, plugin.engine, fallbacks, written)

        try:
            if (
                check_requires
                and kind == "translated"
                and self.semantics == "reference"
                and self._guard_free
                and theorem is not None
            ):
                out = self._with_plan(
                    plan,
                    run_engine,
                    lambda plan: run_guard_free(con, plan, name, theorem, finite=finite),
                    recheck,
                )
            else:
                out = self._with_plan(
                    plan,
                    run_engine,
                    lambda plan: run_plan(
                        con,
                        plan,
                        engine,
                        finite=finite,
                        # A proved report's exact level justifies Spark's windows
                        # without a row-order tiebreak (`to_sql`'s `deterministic`).
                        tie_free=self._exact and kind != "unverified",
                    ),
                    recheck,
                )
        except Exception as e:
            # The translation's own checks of the assumptions, which `check_inputs`
            # did not run first, refuse the batch as that run would have.
            if assumed_checked and (refusal := self._broken_assumption(e)) is not None:
                raise refusal from e
            raise
        out = self._declared_widths(out)
        if kind == "unverified":
            meta = {**(out.schema.metadata or {}), b"sverify.verified": b"false"}
            out = out.replace_schema_metadata(meta)
        return out

    def _declared_widths(self, out: pa.Table) -> pa.Table:
        """`out` with each integer column at the width `output` states: a
        passed-through narrow column Polars widened to int64 goes back to its
        declared width (a native cast, exact: the values came from that width,
        ruling 121)."""
        want = dict(self.output)
        fields = []
        for f in out.schema:
            ty = want.get(f.name)
            if ty is not None and ty.is_integer() and pa.types.is_integer(f.type):
                f = f.with_type(ty.to_pyarrow())
            fields.append(f)
        schema = pa.schema(fields, metadata=out.schema.metadata)
        return out if schema.equals(out.schema) else out.cast(schema)

    def check_asof_pairs(self, con: Connection, engine: Any) -> None:
        """Count, on `engine`, the pairs each as-of join of the plan compares
        (`_asof_checks`), over the tables of `con` the plan reads too, and
        refuse the run where a count is over the cap (`_asof_max_pairs`).

        Raises:
            UnsupportedError: An as-of join compares more pairs than the cap.
        """
        from sverify._asof_cap import too_many

        cap = self._asof_max_pairs
        if cap is None:
            return
        for chk in self._asof_checks:
            res = run_plan(con, written_plan(json.dumps(chk["plan"])), engine)
            n = int(res.column(0)[0].as_py() or 0)
            if n > cap:
                raise UnsupportedError(too_many(n, cap))

    def check_margins(
        self, con: Connection, engine: Any, target: str, deterministic: bool = False
    ) -> int:
        """Run the margin checks of the plan's threshold filters on double
        sums (`Rel.marginCheck`) on `engine`, on the tables of `con`
        the plan reads too, and count the groups they flag: those whose sum
        lies within its bound's margin of the threshold, where the engine may
        keep other groups than the reference.

        Returns:
            The groups flagged; with `verify(on_inferred="warn")`, also
            recorded in `_margin_flags` and warned about (`InferredWarning`).

        The check and the plan must read one snapshot: each input the check
        reads is an Arrow table, a `Resident` table or a `Scan` pinned to a
        version (`_pinned`). Another input warns (`InferredWarning`), and
        refuses the run with `deterministic` (a rerun that must reproduce
        the result, `reproducible=`).

        Raises:
            PreconditionError: A check flags a group, and the report was not
                verified with `on_inferred="warn"`; or, with `deterministic`,
                an input the check reads is not pinned to one version.
        """

        from sverify import profiles
        from sverify.sql import parse_plan
        from sverify.sql.core import open_choices

        total = 0
        for chk in self._margin_checks:
            on = (chk.get("engines") or {}).get(target)
            if on is None:
                # Not covered on this engine: its threshold rule refused the route.
                continue
            loose = [t for t in read_tables(chk["plan"]) if con.has(t) and not _pinned(con.get(t))]
            if loose:
                msg = (
                    f"the margin check and the plan read {', '.join(loose)} twice, and "
                    f"{'it is' if len(loose) == 1 else 'they are'} not pinned to one version: "
                    "the two reads may see different rows"
                )
                if deterministic:
                    raise PreconditionError(msg)
                warnings.warn(InferredWarning(msg, self), stacklevel=3)
            plan = written_plan(json.dumps(chk["plan"]))
            # Where the runner leaves ties and a LIMIT's rows open (`ProfilePlugin.rows`),
            # the check and the run each pick their own: its count says nothing
            # about the run's sums. The ordinal of `rows="sequence"` makes them one.
            runner = profiles.find(target)
            if (
                runner is not None
                and runner.rows == "multiset"
                and not self.deterministic
                and (open_ := open_choices(parse_plan(json.loads(plan)).root))
            ):
                what = " and ".join(sorted(set(open_)))
                if self._on_inferred != "warn":
                    raise PreconditionError(
                        f"the margin check and the run each evaluate {what} on {target}, whose "
                        "rows are open (ties, or the rows of a LIMIT): the check's count may "
                        "miss groups the run sums differently; pin the rows with `reproducible=`, "
                        "order by a key that makes the order total, or run with "
                        '`on_inferred="warn"`'
                    )
                warnings.warn(
                    InferredWarning(
                        f"the margin check and the run each evaluate {what} on {target}, whose "
                        "rows are open: the check's count may miss groups the run sums "
                        "differently",
                        self,
                    ),
                    stacklevel=3,
                )
            # Without the overflow checks of #575: the margin is at most `A`, and
            # a `v − t` past the largest double is farther than any bound.
            # Its own windows aggregate whole partitions, so no row order matters there;
            # the relations below the sum can hold open choices (above), and
            # `tie_free=True` drops their tiebreak on an engine that reads it.
            res = run_plan(con, plan, engine, finite=False, tie_free=True)
            k = int(res.column(0)[0].as_py() or 0)
            if not k:
                continue
            total += k
            msg = on["message"].replace("{k}", str(k))
            if self._on_inferred == "warn":
                warnings.warn(InferredWarning(msg, self), stacklevel=3)
            else:
                raise PreconditionError(msg)
        if self._on_inferred == "warn":
            self._margin_flags[target] = total
        return total

    def _assumed(self) -> list[Issue]:
        """The assumptions a report shows: not those about an operation
        that may raise a division by zero anyway."""
        raising = {i.expr for i in self.errors if i.kind == "division by zero"}
        return [i for i in self.assumed if i.expr not in raising]

    def _inferred_note(self, lab: str) -> str:
        issue = self._inferred_from.get(lab)
        return " (inferred)" if issue is None else f" (inferred from {issue.what})"

    def _streaming(
        self,
        con: Connection,
        chosen: Any,
        streaming: str,
        engine: str,
        fallbacks: Any,
        plan_text: str,
    ) -> None:
        """Record the nodes of the plan the engine runs outside its chosen
        executor (`ProfilePlugin.fallbacks`: Polars's in-memory nodes of its
        streaming plan) in its route, and refuse it with
        `streaming="require"` if it has any."""
        import dataclasses

        from sverify import routes
        from sverify.engine import read_tables

        assert self.internal_plan is not None
        plan = json.loads(plan_text)
        tables = {t: con._arrow[t] for t in read_tables(plan)}
        nodes = tuple(fallbacks(plan, tables))
        if chosen is not None:
            chosen = dataclasses.replace(chosen, fallbacks=nodes)
            self.routes[chosen.engine] = chosen
        if streaming == "require" and nodes:
            refused = routes.Route(
                engine=engine,
                kind=None,
                profile=chosen.profile if chosen is not None else self.semantics,
                reason=(
                    f"{len(nodes)} node(s) of the streaming plan run on the in-memory engine "
                    f"(streaming='require'): "
                    + "; ".join(n[:120] for n in nodes)
                    + "; run with streaming='allow' to let them run in memory"
                ),
                fallbacks=nodes,
            )
            self.routes[engine] = refused
            raise routes.RouteError(refused)

    @property
    def verdict(self) -> Verdict:
        """What the checker proved: `PROVED` (every postcondition holds and no
        run raises), `PROVED_WITH_CHECKS` (the same, but a run stops where a
        check of `assumed` fails on the data) or `UNPROVED`. With an
        observation (`sv.equivalent`), proved also means that no postcondition
        depends on what it ignores and that some engine's doubles meet it
        (`floats_unmet`). Under `semantics="substrait"`, the reference's proof
        also carries over (`transfer` is empty)."""
        if not self._proved:
            return Verdict.UNPROVED
        return Verdict.PROVED_WITH_CHECKS if self.assumed else Verdict.PROVED

    @property
    def _proved(self) -> bool:
        """Either proved verdict: what a run, an export and a summary need."""
        return all(c.portable for c in self.ensures) and self._otherwise_sound

    @property
    def _verified(self) -> bool:
        """Proved, or unproved only in postconditions checked on the output
        data (`on_unproved="check"`): what a run may take."""
        return not self._unmet_ensures() and self._otherwise_sound

    @property
    def _otherwise_sound(self) -> bool:
        """What a proved verdict needs besides its postconditions."""
        return not (self.errors or self._transfer or self.needs or self.floats_unmet)

    def _unmet_ensures(self) -> list[CheckedCondition]:
        """The postconditions that are neither proved nor checked on the data."""
        return [c for c in self.ensures if not (c.portable or c.checked)]

    @property
    def floats_unmet(self) -> str | None:
        """Why no engine's doubles meet the observation's `floats` (exact
        doubles, or a tolerance below the plan's bound), in words; None
        where one does (`floats_on`)."""
        if not self._floats_on or not all(self._floats_on.values()):
            return None
        return "; ".join(f"on {e}: {'; '.join(ps)}" for e, ps in self._floats_on.items())

    def _evidence_lines(self) -> list[str]:
        """An `evidence:` line per engine a run has not taken the plan to
        yet: its class there, and whether a theorem proves it or a test of
        the engine's facts stands for it (`routes.evidence_on`)."""
        from sverify import routes as _routes

        lines = []
        for e, got in _routes.evidence_on(self).items():
            if e in self.routes or got.problems or got.evidence is None:
                continue
            lines.append(f"evidence: {e} {got.cls}, {_routes.evidence_text(got, e)}")
        return lines

    def _observes_lines(self) -> list[str]:
        """The `observes:` line: the observation, the plan's bound beside a
        stated tolerance, and which engines' doubles meet it."""
        from sverify import routes as _routes

        obs = self.observation
        bound = _routes.plan_bound(self._epsilon)
        if obs == _observation.PLAN_BOUND and bound is None:
            return []
        line = f"observes: {obs}"
        if obs.floats != "plan" and bound is not None:
            line += f"; the plan's bound on its doubles is {_observation._bound_text(bound)}"
        if not self._floats_on:
            return [line]
        met = [e for e, ps in self._floats_on.items() if not ps]
        missed = [e for e, ps in self._floats_on.items() if ps]
        want = "exact doubles" if obs.floats == "exact" else "the tolerance"
        if not missed:
            line += f"; {', '.join(met)} meet {want}"
        elif not met:
            line += f"; NOT met: no engine meets {want}"
            line += _routes._cap_text(_routes.max_rows_fix(self, "", obs))
        else:
            line += f"; {', '.join(met)} meet {want}, {', '.join(missed)} do not"
        return [line] + [f"  on {e}: {p}" for e in missed for p in self._floats_on[e]]

    @property
    def needs(self) -> list[Needed]:
        """The preconditions the proof needs that `requires` does not state,
        one `Needed` each: the table, the column, the comparison and the
        bound, the SQL, the condition ready for `requires=`, the runtime
        error it rules out and the fixes in words. These are the bounds
        sverify inferred (`infer_bounds`) and does not assume, so the list
        is empty unless `on_inferred="error"`. `suggested_requires` adds
        them to the stated preconditions.

            report = sv.verify(expr)
            if not report._proved:
                report = sv.verify(expr, requires=report.suggested_requires)
        """
        if self._on_inferred != "error":
            return []
        return self._inferred_needs()

    def _inferred_needs(self) -> list[Needed]:
        """Every inferred bound (`inferred`) as a `Needed`, assumed or not.

        Building them (an Ibis deferred and a text each) is most of the cost
        of `str(report)` and `to_json`, which read `needs` several times,
        so they are kept until what they are built from changes; `verify`
        sets those fields after constructing the report."""
        key = (
            self._dialect,
            tuple((t, tuple(map(str, cs))) for t, cs in self._inferred.items()),
            tuple((lab, id(i)) for lab, i in self._inferred_from.items()),
        )
        cached = self.__dict__.get("_needs_cache")
        if cached is not None and cached[0] == key:
            return list(cached[1])
        out = self._build_inferred_needs()
        self.__dict__["_needs_cache"] = (key, tuple(out))
        return out

    def _build_inferred_needs(self) -> list[Needed]:
        return [
            _needed(
                t,
                c,
                self._dialect,
                self._inferred_from.get(label(c)),
                self._needs_text(t, [label(c)]),
            )
            for t, cs in self._inferred.items()
            for c in cs
        ]

    @property
    def suggested_requires(self) -> dict[str, list[Condition]]:
        """The `requires=` mapping that states every precondition the proof
        uses: the stated ones and those sverify inferred (`needs`, and the
        bounds `on_inferred="warn"` or `"ignore"` assumes), per input table,
        ready to pass to `verify` or to paste into a contract."""
        out: dict[str, list[Condition]] = {}
        for t, cs in self._conditions.items():
            out[t] = [c for c in cs if not isinstance(c, Inferred)]
        # The bounds a hint names, which a proof confirmed (`_confirm_hints`).
        extra = [(n.table, n.condition, n.label) for n in self._inferred_needs()]
        for i in self.issues:
            extra += [(t, c, label(c)) for t, cs in i.hint_needs.items() for c in cs]
        for t, c, lab in extra:
            have = out.setdefault(t, [])
            if c is not None and lab not in {label(x) for x in have}:
                have.append(c)
        return {t: cs for t, cs in out.items() if cs}

    @property
    def needed(self) -> dict[str, list[str]]:
        """Deprecated: `needs`. Their labels per input table."""
        warnings.warn(
            "Report.needed is deprecated; read Report.needs",
            DeprecationWarning,
            stacklevel=2,
        )
        return {t: list(labs) for t, labs in _labels_by_table(self.needs).items()}

    @property
    def needed_text(self) -> list[str]:
        """Deprecated: `Needed.text` of each of `needs`."""
        warnings.warn(
            "Report.needed_text is deprecated; read Needed.text of report.needs",
            DeprecationWarning,
            stacklevel=2,
        )
        return self._needs_lines()

    @property
    def needed_conditions(self) -> dict[str, list[Condition]]:
        """Deprecated: `Needed.condition` of each of `needs`, or the whole
        mapping as `suggested_requires`."""
        warnings.warn(
            "Report.needed_conditions is deprecated; read Needed.condition of report.needs, "
            "or report.suggested_requires",
            DeprecationWarning,
            stacklevel=2,
        )
        out: dict[str, list[Condition]] = {}
        for n in self.needs:
            if n.condition is not None:
                out.setdefault(n.table, []).append(n.condition)
        return out

    @property
    def equivalence(self) -> Observation:
        """The equivalence the result is proved up to: `sv.equivalent(...)` in
        `ensures`, or rows as a multiset with exact values (`observation`)."""
        return self.observation

    def _needs_text(self, table: str, labs: Sequence[str]) -> str:
        """Needed preconditions on one table that come from one operation,
        where they come from, and the fixes."""
        table = self._table_params.get(table, table)
        issues = [i for lab in labs if (i := self._inferred_from.get(lab)) is not None]
        kinds = " or ".join(dict.fromkeys(i.kind for i in issues))
        where = f", inferred from `{issues[0].what}` ({kinds} otherwise)" if issues else ""
        both = " and ".join(labs)
        it = "it" if len(labs) == 1 else "them"
        cond = labs[0] if len(labs) == 1 else " & ".join(labs)
        return (
            f"{both} on {table}{where}: declare {it} in requires (each run then checks "
            f"{it} on the data), or rewrite so no row needs {it} (`{table}.filter({cond})` "
            f"first, or a CASE); on_inferred='warn' assumes {it} instead"
        )

    def _needs_lines(self, needed: Mapping[str, Sequence[str]] | None = None) -> list[str]:
        """`_needs_text` for each table and operation (the labels of `needs`
        by default; `inferred`, as labels, for a warning)."""
        out = []
        if needed is None:
            needed = _labels_by_table(self.needs)
        for t, labs in needed.items():
            groups: dict[str, list[str]] = {}
            for lab in labs:
                issue = self._inferred_from.get(lab)
                groups.setdefault(issue.what if issue else lab, []).append(lab)
            out += [self._needs_text(t, g) for g in groups.values()]
        return out

    @property
    def errors(self) -> list[Issue]:
        """The `issues` an engine fails on at run time (`Issue.error` is true)."""
        return [i for i in self.issues if i.error]

    @property
    def warnings(self) -> list[Issue]:
        """The `issues` that do not count against a proof. None do: an
        `SUM` that may leave its type is an error (`errors`)."""
        return [i for i in self.issues if not i.error]

    @property
    def suggestions(self) -> dict[str, list[Needed]]:
        """For each unproved postcondition with one, the preconditions under
        which it would be proved, one `Needed` each, by the postcondition's
        label (`{"(_.y <= 100)": [Needed(table="orders", label="(_.x <= 50)", …)]}`)."""
        return {
            c.label: [
                _needed(t, x, self._dialect, text=f"{label(x)} on {t} would prove {c.label}")
                for t, cs in c.suggested.items()
                for x in cs
            ]
            for c in self.ensures
            if c.suggested
        }

    @property
    def unproved(self) -> list[CheckedCondition]:
        """The postconditions in `ensures` that were not proved."""
        return [c for c in self.ensures if not c.proved]

    @property
    def notes(self) -> list[str]:
        """What the report notes about the result as a whole, as `str(report)`
        prints them after "note: ": that rows may tie in an `ORDER BY`
        (`deterministic` is False, `ties` says which keys would help), that
        the proof holds for the `params` given only, and where the reference
        reads the SQL differently from DuckDB (`dialect_differences`)."""
        out = [] if self.deterministic else [self._ties_hint()]
        if self._params:
            out.append(f"{PARAMS_NOTE}: {', '.join(self._params)}")
        out += [f"dialect: {d}" for d in self.dialect_differences]
        return out

    def route(
        self,
        engine: Any,
        route: RouteKind | Literal["auto"] = "auto",
        *,
        reproducible: Observation | None = None,
    ) -> Route:
        """The route by which `run` would take the plan to `engine`, and the
        plan's class there, without running it: the route `report.routes`
        records after a run.

        Args:
            engine: The engine's name (`"duckdb"`, `"polars"`, …) or a Spark
                session.
            route: `"auto"` (the default) tries the routes in turn; a route
                by name (`"native"`, `"reference"`, `"transfer"`,
                `"recheck"`) is taken or refused.
            reproducible: What a rerun must reproduce, as `run` takes it.

        Returns:
            The `Route`: its `kind`, `cls` (`"exact"`, `"observed"`, `"shim"`
            or `"refused"`), `observation` and `reason`. A plan that is not
            proved is refused, with `reason` saying so.

        Raises:
            EngineVersionError: The installed engine is another major
                version than its profile's.
            EngineSettingsError: A setting the engine's profile depends on
                differs from its facts'.
        """
        from sverify import routes as _routes

        return _routes.choose(self, engine, route, reproducible=reproducible)

    def _all_hints(self) -> list[str]:
        """`hints`, and the general overflow hint for an overflow neither they
        nor its own `Issue.hint` cover."""
        truncated = any(h.startswith(TRUNC_HINT) for h in self._hints)
        covered = [
            i
            for i in self.errors
            if i.kind == "overflow" and (i.hint or truncated and _truncates(i.expr))
        ]
        if any(i.kind == "overflow" and i not in covered for i in self.errors):
            return [*self._hints, OVERFLOW_HINT]
        return self._hints

    @property
    def _summary(self) -> str:
        """The report's first line, by the verdict: "proved"; "proved with
        checks: " and the assumptions that run time checks ("2 assumptions");
        or "NOT proved: " and what is missing, counted ("1 of 2
        postconditions not proved, 1 possible runtime error")."""
        match self.verdict:
            case Verdict.PROVED:
                return "proved"
            case Verdict.PROVED_WITH_CHECKS:
                k = len(self.assumed)
                return f"proved with checks: {k} assumption{'' if k == 1 else 's'}"
            case _:
                return f"NOT proved: {', '.join(self._counts())}"

    def _counts(self) -> list[str]:
        """What keeps the plan from being proved, counted."""

        def n(k: int, one: str, many: str | None = None) -> str:
            return f"{k} {one if k == 1 else many or one + 's'}"

        out = []
        if unproved := self.unproved:
            out.append(f"{len(unproved)} of {n(len(self.ensures), 'postcondition')} not proved")
        if ignored := [c for c in self.ensures if c.proved and c.ignores]:
            out.append(
                f"{n(len(ignored), 'postcondition')} "
                f"{'depends' if len(ignored) == 1 else 'depend'} on what the observation ignores"
            )
        if self.errors:
            out.append(n(len(self.errors), "possible runtime error"))
        if needed := len(self.needs):
            out.append(n(needed, "precondition") + " needed")
        if self._transfer:
            out.append(n(len(self._transfer), "option") + " where Substrait allows more")
        if self.floats_unmet:
            out.append("no engine's doubles meet the observation")
        return out or ["see the report"]

    def _ties_hint(self) -> str:
        """The note on ties (#688): where the order is open, and the key
        that closes it, where one on an input reaches the ORDER BY."""
        from sverify._user_text import named

        out = TIES_HINT.format(_ORDERED.get(self._dialect, _ORDERED["ibis"]))
        plan = json.loads(self.internal_plan) if self.internal_plan else None
        places = [named(t.what, plan) for t in self._class_places]
        if places and all(places):
            out += f" ({'; '.join(dict.fromkeys(p for p in places if p))})"
        if self.ties:
            keys = " and ".join(
                f"{', '.join(f'`{k}`' for k in ks)} in the requires of {t!r}"
                for t, ks in self.ties.items()
            )
            return f"{out}. For a reproducible result, declare {keys}"
        return (
            f"{out}. For a reproducible result, order by columns that are unique there; "
            "no key on an input that sverify follows reaches them"
        )

    def __str__(self) -> str:
        lines = [self._summary]
        if self._proved and self._generated_proofs is False:
            lines[0] += UNCHECKED_CHECKER
        c = self._plain_contract()
        if c["guarantees"]:
            lines += ["The output guarantees:", *[f"  {g}" for g in c["guarantees"]]]
        if c["checks"]:
            lines += ["Each run checks on the data:", *[f"  {k}" for k in c["checks"]]]
        bad = [x for head, more in self._not_proved() for x in (head, *[f"  {m}" for m in more])]
        if bad:
            lines += ["Not proved:", *[f"  {b}" for b in bad]]
        lines += self._trusts_lines()
        notes = [*self._all_hints(), *self.notes]
        if notes:
            lines += ["Notes:", *[f"  {n}" for n in notes]]
        if self.facts or self.rows is not None:
            lines.append("Known about the output:")
            if self.rows is not None:
                lines.append(f"  rows: at most {self.rows:,}")
            lines += [f"  {name}: {value}" for name, value in self.facts.items()]
        return "\n".join(lines)

    def _trusts_lines(self) -> list[str]:
        """One `trusts:` line per black box the plan calls, with its laws:
        trusted, not checked on the data (`assumes:` is for those)."""
        return [
            f"trusts: black box {name} keeps its declared laws"
            + (f" ({', '.join(' '.join(map(str, law)) for law in laws)})" if laws else "")
            for name, laws in self.black_boxes.items()
        ]

    def _plain_contract(self, sources: Collection[str] | None = None) -> dict[str, list[str]]:
        """What the contract means for the data, in words (`sverify.cli.summary`):

        * `guarantees`: what every output row (or the output) meets, proved;
        * `checks`: what each run checks on the data before it writes (the
          preconditions on the sources, postconditions checked on the output,
          sums assumed to fit). With `sources`, only the preconditions on
          those tables: the others follow from what the transforms feeding
          them guarantee;
        * `not_proved`: what is not proved, and the runtime errors it may raise.
        """
        from sverify._user_text import plain

        guarantees = [plain(c.label) for c in self.ensures if c.proved and not c.ignores]
        if self.rows is not None:
            guarantees.append(f"at most {self.rows:,} rows")
        checks: list[str] = []
        needed = _labels_by_table(self.needs)
        for table, conds in self.requires.items():
            if sources is not None and table not in sources:
                continue
            shown = self._table_params.get(table, table)
            inferred = {label(c) for c in self._inferred.get(table, [])}
            checks += [
                f"{shown}: {plain(c)}" + (self._inferred_note(c) if c in inferred else "")
                for c in conds
                if c not in needed.get(table, ())
            ]
        checks += [f"output: {plain(c.label)}" for c in self.ensures if c.checked]
        checks += [f"while it runs: {i.assumption}" for i in self.assumed]
        not_proved = [head for head, _ in self._not_proved()]
        return {"guarantees": guarantees, "checks": checks, "not_proved": not_proved}

    def _not_proved(self) -> list[tuple[str, list[str]]]:
        """What is not proved, each as one line and the lines that go with it:
        a postcondition that is not proved, or that depends on what the
        observation ignores (with its counterexample and suggestion), the
        preconditions it needs, the runtime errors it may raise (with their
        hints), Substrait's options and the observation's doubles."""
        from sverify._user_text import plain

        out: list[tuple[str, list[str]]] = []
        for c in self._unmet_ensures():
            more = []
            if c.counterexample is not None:
                more.append(f"counterexample: {c.counterexample}")
            if c.suggested:
                more.append(_would_hold(c))
            why = c.why if not c.proved else _observation.why(c.ignores)
            out.append((f"{plain(c.label)}: {why}", more))
        out += [(n, []) for n in self._needs_lines()]
        out += [
            (f"may fail: {i.message}", [f"hint: {i.hint}"] if i.hint else []) for i in self.errors
        ]
        if self._transfer:
            out.append((f"Substrait allows more at {len(self._transfer)} option(s)", []))
        if self.floats_unmet:
            out.append((f"doubles: {self.floats_unmet}", []))
        return out

    def details(self) -> str:
        """The full text of the report: the preconditions and `needs`, each
        postcondition with its status, the semantics, the evidence for each engine
        and the routes, as an auditor reads it. `str(report)` is the contract in
        plain words."""
        lines = [self._summary]
        if self._proved and self._generated_proofs is False:
            lines[0] += UNCHECKED_CHECKER
        needed = _labels_by_table(self.needs)
        for table, conds in self.requires.items():
            inferred = {label(c) for c in self._inferred.get(table, [])}
            lines += [
                f"requires {self._table_params.get(table, table)}: {c}"
                + (self._inferred_note(c) if c in inferred else "")
                for c in conds
                if c not in needed.get(table, ())
            ]
        lines += [f"needs: {n}" for n in self._needs_lines()]
        for c in self.ensures:
            lines.append(f"ensures {c.label}: {c.message}")
            if c.counterexample is not None:
                lines.append(f"  counterexample: {c.counterexample}")
            if c.suggested:
                lines.append(f"  {_would_hold(c)}")
        lines += [f"assumes: {i.assumption}" for i in self._assumed()]
        lines += self._trusts_lines()
        lines += [f"checks at run time: {c['label']}" for c in self._margin_checks]
        for i in self.errors:
            lines.append(f"may fail: {i.message}")
            if i.hint:
                lines.append(f"  hint: {i.hint}")
        lines += [f"hint: {h}" for h in self._all_hints()]
        lines += [f"note: {n}" for n in self.notes]
        lines.append(f"semantics: {self.semantics}")
        lines += [f"  {_transfer_failure(f)}" for f in self._transfer or ()]
        lines += self._observes_lines()
        lines += self._evidence_lines()
        lines += [f"route on {e}: {r}" for e, r in self.routes.items()]
        if self.facts or self.rows is not None:
            lines.append("known about the output:")
            if self.rows is not None:
                lines.append(f"  rows: at most {self.rows:,}")
            lines += [f"  {name}: {value}" for name, value in self.facts.items()]
        return "\n".join(lines)

    def _repr_markdown_(self) -> str:
        def status(c: CheckedCondition) -> str:
            if c.proved:
                return "✅ proved"
            if c.checked:
                return f"☑️ {c.why}; {DATA_CHECK}"
            if c.counterexample is None:
                return f"❌ {c.why}"
            return f"❌ {c.why}; fails on `{c.counterexample}`".replace("|", "\\|")

        rows = []
        for c in self.ensures:
            rows.append(f"| `{c.label}` | {status(c)} |")
            if c.suggested:
                rows.append(f"| suggestion | {_would_hold(c).replace('|', '\\|')} |")
        for n in self._needs_lines():
            rows.append(f"| needs | ❌ {n.replace('|', '\\|')} |")
        # Issues quote expressions, which may contain `|` (a regex, an OR).
        for i in self.errors:
            note = f" ({RUNTIME_CHECK})" if i.assumed else ""
            rows.append(
                f"| runtime | ❌ may fail: {(str(i) + _cause(i)).replace('|', '\\|')}{note} |"
            )
            if i.hint:
                rows.append(f"| hint | {i.hint.replace('|', '\\|')} |")
        inferred = [
            f"`{label(c)}` on {t}" for t, cs in self._inferred.items() for c in cs if not self.needs
        ]
        inferred += [
            f"SUM of `{i.what}` {_sum_assumed(i)}"
            if _sum(i)
            else f"`{i.shown or i.expr}` {FINITE_ASSUMED}"
            for i in self._assumed()
        ]
        rows += [f"| hint | {h.replace('|', '\\|')} |" for h in self._all_hints()]
        facts = [f"| `{n}` | {v} |" for n, v in self.facts.items()]
        if self.rows is not None:
            facts.insert(0, f"| (rows) | at most {self.rows:,} |")
        note = [f"**{self._summary}**", ""]
        note += [] if self.deterministic else [f"> ⚠️ {self._ties_hint()}", ""]
        if self._params:
            note += [f"> ℹ️ {PARAMS_NOTE}: {', '.join(self._params)}", ""]
        if inferred:
            note += [f"> ℹ️ assumed (inferred): {', '.join(inferred)}", ""]
        note += [f"> semantics: {self.semantics}", ""]
        return "\n".join(
            [
                *note,
                "| postcondition | status |",
                "|---|---|",
                *rows,
                "",
                "| output column | known values |",
                "|---|---|",
                *facts,
            ]
        )


#: Private fields that never had a public name: no deprecated alias.
_REPORT_PRIVATE = [
    "table_params",
    "run_plan",
    "run_gate",
    "run_unchecked",
    "run_gates",
    "asof_checks",
    "asof_max_pairs",
]

_REPORT_INTERNAL = [
    "windows_total",
    "tie_places",
    "exact",
    "class_places",
    "guard_free",
    "unchecked",
    "optimized",
    "rewrites",
    "inferred",
    "implied",
    "params",
    "hints",
    "bounds",
    "relations",
    "stated",
    "floats_on",
    "depends",
    "contract",
    "transfer",
    "epsilon",
    "rows_exact",
    "margin_checks",
    "margin_flags",
    "engines",
    "sorted",
    "generated_proofs",
    "conditions",
    "dialect",
    "on_inferred",
    "inferred_from",
    "postconditions",
]
"""`Report`'s fields that are internal (B4 of the 1.0 API review): each has
an underscore, and its old name reads it with a `DeprecationWarning` for a
release. `plan` is `internal_plan`."""


_deprecated.add(Report, {**{old: "_" + old for old in _REPORT_INTERNAL}, "plan": "internal_plan"})


def _would_hold(c: CheckedCondition) -> str:
    """The suggestion line of an unproved postcondition."""
    parts = [
        f"{', '.join(f'`{label(x)}`' for x in cs)} in the requires of {t!r}"
        for t, cs in c.suggested.items()
    ]
    return "would hold with " + " and ".join(parts)


PARAMS_NOTE = "proved for these parameter values only"


#: The functions whose order of ties is open, in each input language.
_ORDERED = {
    "ibis": "first(), last(), group_concat(), mode(), argmin() or argmax()",
    "sql": "FIRST, LAST, STRING_AGG, MODE, ARG_MIN or ARG_MAX",
}


TIES_HINT = (
    "rows may tie in the ORDER BY of a window, of a LIMIT or of {}, or the reference "
    "leaves a value open, so the engine decides and a rerun may give other rows. The "
    "postconditions are proved for every choice"
)


class VerificationError(SverifyError):
    """A postcondition, or the absence of runtime errors, could not be proved.

    Import it from `sverify.errors`. The message's first line counts what
    is missing; then one line per finding: each needed precondition, each
    unproved postcondition with what the checker established about it, and
    each possible runtime error with its hint. `report` holds the rest.

    Attributes:
        report: The `Report` of the failed proof.
    """

    code = "not_proved"

    def __init__(self, report: Report):
        self.report = report
        super().__init__(error_text(report))


def error_text(report: Report) -> str:
    """A `VerificationError`'s message: what is missing, counted, and
    one line per finding with its hint, each hint once; `e.report` has the
    full report."""
    lines = [f"{', '.join(report._counts())} (e.report has the details)"]
    lines += [f"  needs: {n}" for n in report._needs_lines()]
    for c in report.ensures:
        if not c.proved:
            line = f"  not proved: {c.label}: {c.why}"
            if c.counterexample is not None:
                line += f" (counterexample: {c.counterexample})"
            lines.append(line)
            if c.suggested:
                lines.append(f"    {_would_hold(c)}")
        elif c.ignores:
            lines.append(f"  not proved: {c.label}: {_observation.why(c.ignores)}")
    hints: list[str] = []
    for i in report.errors:
        lines.append(f"  may fail: {i.message}")
        if i.hint and i.hint not in hints:
            hints.append(i.hint)
            lines.append(f"    hint: {i.hint}")
    lines += [f"  hint: {h}" for h in report._all_hints() if h not in hints]
    lines += [f"  {_transfer_failure(f)}" for f in report._transfer or ()]
    if report.floats_unmet:
        lines.append(f"  doubles: {report.floats_unmet}")
    return "\n".join(lines)


class UnverifiedRunError(VerificationError, RouteError):
    """A run or refresh of a plan that is not proved, refused.

    Import it from `sverify.errors`. It is a `VerificationError`, so
    `except VerificationError` catches every "not proved", and a
    `RouteError`, as the refusal was before 0.6. `run(..., unverified=True)`
    or `refresh(unverified=True)` runs the plan anyway, and
    `transform(on_unproved="warn")` makes a node's refreshes do so.

    Attributes:
        report: The `Report` that is not proved.
        route: The refused `Route`, whose `reason` says what was not proved.
    """

    code = "unverified_run"

    def __init__(self, report: Report, route: Route):
        self.report = report
        self.route = route
        Exception.__init__(self, f"refused on {route.engine}: {route.reason}")


class PostconditionError(SverifyError):
    """Output data violates a postcondition (only raised by runtime checks).

    Import it from `sverify.errors`. Raised with `on_unproved="check"`,
    when a postcondition the checker could not prove fails on the output rows. The
    message says how many output rows violate which condition.
    """

    code = "postcondition_failed"


_EPOCH_DAY = date(1970, 1, 1)


_MICROSECOND = timedelta(microseconds=1)


def render_fact(abstract: dict, dtype: Any) -> str | None:
    """Describe a column's abstract value for doubles, decimals (their unscaled
    integers), timestamps, dates and intervals (microseconds); None
    keeps Lean's own description."""
    rng = abstract.get("int")
    span: tuple[int, int] | None = None
    if (dec := abstract.get("decimal")) is not None:
        # The plan's own type, which Lean states: Ibis may type a decimal
        # product at another scale than the model computes it.
        scale = dec["scale"]
        # The wider precision: the plan may declare more digits than the model
        # needs (DuckDB's SUM is DECIMAL(38, s)), or fewer (Ibis types `a + a`
        # at `a`'s), and the model computes exactly.
        same = dtype.is_decimal() and dtype.scale == scale and dtype.precision is not None
        precision = max(dtype.precision, dec["precision"]) if same else dec["precision"]
        show = lambda k: f"{_decimals.scaled(k, -scale):.{scale}f}"  # noqa: E731
        noun = f"a decimal({precision}, {scale})"
    elif dtype.is_floating():
        show: Callable[[int], str] = lambda k: repr(decode_double(k))  # noqa: E731
        noun = "a double"
    elif dtype.is_timestamp():
        epoch = datetime(1970, 1, 1)
        span = (datetime.min - epoch) // _MICROSECOND, (datetime.max - epoch) // _MICROSECOND
        show = lambda k: (  # noqa: E731
            (epoch + timedelta(microseconds=k)).isoformat(sep=" ")
            if span[0] <= k <= span[1]
            else f"{k:+} µs from 1970-01-01"
        )
        noun = "a timestamp"
    elif dtype.is_date():
        span = (date.min - _EPOCH_DAY).days, (date.max - _EPOCH_DAY).days
        show = lambda k: (  # noqa: E731
            (_EPOCH_DAY + timedelta(days=k)).isoformat()
            if span[0] <= k <= span[1]
            else f"{k:+} days from 1970-01-01"
        )
        noun = "a date"
    elif dtype.is_interval():
        show = lambda k: str(timedelta(microseconds=k))  # noqa: E731
        noun = "an interval"
    else:
        return None
    parts = []
    if rng is not None:
        lo = None if rng["lo"] is None else int(rng["lo"])
        hi = None if rng["hi"] is None else int(rng["hi"])
        if not dtype.is_floating():
            # Bounds near the 64-bit limits go without saying (as in Lean's text).
            lo = None if lo is not None and lo <= -(2**60) else lo
            hi = None if hi is not None and hi >= 2**60 else hi
        if span is not None:
            # So do bounds at or past what a Python date or datetime holds, the
            # years 1 to 9999: they are the reference's own (D32), which a DATE
            # or TIMESTAMP has by its type (a DATE cast from a TIMESTAMP is
            # computed and may reach beyond, #435).
            lo = None if lo is not None and lo <= span[0] else lo
            hi = None if hi is not None and hi >= span[1] else hi
        if dtype.is_interval():
            # And an interval as long as two of the reference's timestamps
            # apart, or longer.
            widest = (datetime.max - datetime.min) // _MICROSECOND
            lo = None if lo is not None and lo <= -widest else lo
            hi = None if hi is not None and hi >= widest else hi
        if lo is None and hi is None:
            parts.append(f"any {noun.split(' ', 1)[1]}")
        elif lo is not None and hi is not None and lo == hi:
            parts.append(f"{noun} = {show(lo)}")
        elif dtype.is_floating():
            # Codes are 0 and odd numbers of magnitude 3 or more; a bound
            # between two codes reads best against its neighbour, zero first.
            def valid(k: int) -> bool:
                return k == 0 or (k % 2 == 1 and abs(k) >= 3)

            def up(k: int) -> int:
                """The smallest code ≥ k."""
                return k if valid(k) else 0 if k in (-2, -1) else 3 if k in (1, 2) else k + 1

            def down(k: int) -> int:
                """The largest code ≤ k."""
                return k if valid(k) else 0 if k in (1, 2) else -3 if k in (-2, -1) else k - 1

            def ge(k: int) -> str:
                n = up(k)
                return f"≥ {show(n)}" if n in (k, 0) else f"> {show(down(k - 1))}"

            def le(k: int) -> str:
                p = down(k)
                return f"≤ {show(p)}" if p in (k, 0) else f"< {show(up(k + 1))}"

            if hi is None:
                parts.append(f"{noun} {ge(lo)}")  # type: ignore[arg-type]
            elif lo is None:
                parts.append(f"{noun} {le(hi)}")
            else:
                parts.append(f"{noun} {ge(lo)} and {le(hi)}")
        elif hi is None:
            parts.append(f"{noun} ≥ {show(lo)}")  # type: ignore[arg-type]
        elif lo is None:
            parts.append(f"{noun} ≤ {show(hi)}")
        else:
            parts.append(f"{noun} in [{show(lo)}, {show(hi)}]")
    if abstract.get("null"):
        parts.append("NULL")
    return " or ".join(parts) if parts else "nothing (no rows)"


@dataclass(frozen=True)
class Needed:
    """A precondition a proof needs that `requires` does not state: a bound
    on one input column. `Report.needs` lists those the proof needs
    (`on_inferred="error"` does not assume them), `Issue.needs` those that
    rule out one runtime error, and `Report.suggestions` those under which
    an unproved postcondition would be proved."""

    table: str
    """The input table."""
    column: str | None
    """The input column it is on."""
    op: str | None
    """`>=`, `>`, `<=`, `<`, `<>` or `IS NOT NULL`; None if it is none of
    these."""
    value: str | None
    """The bound, as a SQL literal (`9000000000000000000`,
    `TIMESTAMP '2000-01-01 00:00:00'`); None for `IS NOT NULL`."""
    sql: str
    """The whole condition as DuckDB's SQL, NULL passing where the column
    is nullable: `"qty" IS NULL OR "qty" < 9000000000000000000`."""
    label: str
    """The condition as `Report.needed` lists it: `(_.qty < 9 * 10**18)`."""
    code: str
    """The condition as the Python a user writes in `requires`, for an
    editor's quick fix: `_.qty < 9 * 10**18`, `_.qty != 0`,
    `_.qty.notnull()`. `sql` is the form for a SQL contract."""
    issue: Issue | None
    """The runtime error it rules out, and where; None where it rules out
    none (a suggestion for a postcondition) or is the `Issue`'s own."""
    condition: Condition | None = None
    """The condition, ready for `requires=`: an Ibis deferred for an Ibis
    transform (`_.qty < 9 * 10**18`, or `_.qty.isnull() | (_.qty < 9 * 10**18)`
    where `qty` may be NULL, as the bound lets NULL pass), `sql` for a SQL
    one or where the bound has no Ibis form (an Ibis transform reads SQL
    conditions too)."""
    text: str = ""
    """The precondition in words: where it comes from, and the fixes."""


def _needed(
    table: str,
    c: Condition,
    dialect: str,
    issue: Issue | None = None,
    text: str = "",
) -> Needed:
    """A `Needed` for the condition `c` on `table`: an `Inferred` bound, or
    a label where the bound is not at hand."""
    lab = label(c)
    column = getattr(c, "column", None)
    op, value = c.parts() if isinstance(c, Inferred) else (None, None)
    sql = str(c) if isinstance(c, str) else lab
    n = Needed(table, column, op, value, sql, lab, _unparen(lab), issue, text=text)
    cond = _needed_deferred(n) if dialect == "ibis" else None
    return replace(n, condition=cond if cond is not None else n.sql)


def _labels_by_table(needs: Sequence[Needed]) -> dict[str, tuple[str, ...]]:
    """The labels of `needs` per input table, in order."""
    out: dict[str, tuple[str, ...]] = {}
    for n in needs:
        out[n.table] = (*out.get(n.table, ()), n.label)
    return out


def _sql_value(value: str) -> Any:
    """The Python value of a SQL literal `Needed.value` gives: an integer,
    a double, a decimal, a date or a timestamp; None for anything else."""
    if re.fullmatch(r"-?\d+", value):
        return int(value)
    if re.fullmatch(r"-?\d+\.\d+", value):
        return Decimal(value)
    try:
        if (m := re.fullmatch(r"DATE '(.+)'", value)) is not None:
            return date.fromisoformat(m[1])
        if (m := re.fullmatch(r"TIMESTAMP '(.+)'", value)) is not None:
            return datetime.fromisoformat(m[1])
        x = float(value)
    except ValueError:
        return None
    return x if math.isfinite(x) else None


def _needed_deferred(n: Needed) -> Deferred | None:
    """`n` as an Ibis deferred, letting NULL pass where its SQL does; None
    where it has no such form."""
    if n.column is None or n.op is None:
        return None
    col: Any = ibis._[n.column]
    if n.op == "IS NOT NULL":
        return col.notnull()
    v = _sql_value(n.value or "")
    if v is None:
        return None
    ops_ = {">=": col >= v, ">": col > v, "<=": col <= v, "<": col < v, "<>": col != v}
    cmp = ops_[n.op]
    nulls = '"' + n.column.replace('"', '""') + '" IS NULL OR '
    return col.isnull() | cmp if n.sql.startswith(nulls) else cmp


def condition_query(table: Transform, cond: Condition, semantics: str = "reference") -> Transform:
    """A query selecting one condition column from a table or transformation:
    SQL for a SQL condition on a SQL transformation, an Ibis expression
    otherwise (a SQL condition on an Ibis table is a SQL model over it, with
    `semantics`)."""
    if isinstance(cond, str):
        query = f'SELECT ({cond}) AS "c" FROM {{}} AS "t"'
        if isinstance(table, str):
            return query.format(f"({table})")
        from sverify.ibis_substrait import SQLModel, Unsupported, sql_model_schema

        query = query.format('"t"')
        try:
            schema = sql_model_schema(query, {"t": table.schema()}, semantics)
        except Unsupported as e:
            raise Unsupported(f"condition {cond!r}: {e}") from e
        return SQLModel(query, (table.op(),), ("t",), schema, "duckdb", semantics).to_expr()
    if isinstance(table, str):
        raise TypeError("Ibis conditions need an Ibis transformation; use a SQL string instead")
    if isinstance(table, ir.Join):
        # Ibis merges a select over a join into the join's own select
        # (`Join.select`); the checker wants the condition over the
        # transformation as it is (#1484, `ContractCheck.postOf`).
        table = ir.Table(table.op())
    return table.select(c=resolve(cond, table))


def _unparen(code: str) -> str:
    """`code` without the one pair of parentheses around all of it."""
    if not (code.startswith("(") and code.endswith(")")):
        return code
    depth = 0
    for i, ch in enumerate(code):
        depth += {"(": 1, ")": -1}.get(ch, 0)
        if depth == 0 and i < len(code) - 1:
            return code
    return code[1:-1]


OnInferred = Literal["error", "warn", "ignore", "off"]


def violations(table: ir.Table, cond: Condition, engine: Engine | None = None) -> int:
    """Rows of a bound table where `cond` is not TRUE (FALSE or NULL), or for
    `unique`, rows beyond the first for each repeated key.

    With an engine named, the condition's plan runs there, over the tables of
    the connection `table` is bound to; otherwise Ibis counts on that
    connection."""
    if not isinstance(cond, TableCondition) and engine is not None:
        con = connection_of(table)
        if con is None:
            raise ValueError("checking a condition on an engine needs a table of sverify.connect()")
        plan = written_plan(plan_json(con, condition_query(table, cond)))
        return sum(v is not True for v in run_plan(con, plan, engine).column(0).to_pylist())
    if isinstance(cond, TableCondition):
        return _table_violations(table, cond, engine)
    if isinstance(cond, str):
        backend: Any = ibis.get_backend(table)
        sql = ibis.to_sql(table, dialect=backend.name)
        query = f'SELECT count(*) FROM ({sql}) AS "t" WHERE NOT coalesce(({cond}), FALSE)'
        # On the backend's own connection: Ibis 12's `backend.sql` asks DuckDB 2
        # for the query's schema with a method it no longer has.
        # `raw_sql` returns the connection itself: fetch every row, so that it
        # is free for the next query, and leave it open.
        return int(backend.raw_sql(query).fetchall()[0][0])
    count: Any = table.filter(~resolve(cond, table).fill_null(ibis.literal(False))).count()
    return _count(count)


def _table_violations(table: ir.Table, cond: TableCondition, engine: str | None) -> int:
    """Rows of the bound `table` that break the table condition `cond`, from its
    count as a plan run by the engine (the connection's, unless one is named):
    the count has the reference's meaning on every engine, and a condition the
    engine's writer refuses refuses the check (`SverifyError`)."""
    return _table_counts(table, [cond], engine)[0]


def _table_counts(
    table: ir.Table, conds: Sequence[TableCondition], engine: str | None
) -> list[int]:
    """`_table_violations` for several table conditions on one table, from one
    plan where the writer takes it: their counts as the rows of a union, each
    tagged with its position. Where it does not, one plan each. A table of the
    caller's own Ibis backend is counted there, by the same relations."""
    con = connection_of(table)
    if con is None:
        # The caller's own Ibis backend (a database, a memtable): its rows stay
        # there, and it counts the same relations (`Report.run`'s engines work
        # on a connection's tables).
        backend = ibis.get_backend(table)
        return [
            c.settle(c.count_query(table, backend.table).to_pyarrow().column(0)[0].as_py())
            for c in conds
        ]
    on = engine or con.engine
    queries = [c.count_query(table, con.table) for c in conds]
    if len(queries) > 1:
        tagged = [
            q.select(i=ibis.literal(i, "int64"), v=q.v.cast("int64")) for i, q in enumerate(queries)
        ]
        try:
            plan = written_plan(plan_json(con, ibis.union(*tagged, distinct=False)))
            out = run_plan(con, plan, on)
        except SverifyError:
            pass  # a writer that takes one count at a time, below
        else:
            got = dict(zip(out.column(0).to_pylist(), out.column(1).to_pylist(), strict=True))
            return [c.settle(got[i]) for i, c in enumerate(conds)]
    return [
        c.settle(run_plan(con, written_plan(plan_json(con, q)), on).column(0)[0].as_py())
        for c, q in zip(conds, queries, strict=True)
    ]


def violation_counts(
    table: ir.Table, conds: Sequence[Condition], engine: str | None = None
) -> list[tuple[Condition, int, str | None]]:
    """Each condition of `conds` with the rows of `table` that break it (a
    result that is not TRUE) and the error that stopped its check, if one did.

    With an `engine`, the row-wise conditions that are SQL strings run there
    as one plan, and the Ibis ones as another (`conditions_query`): one plan
    per table where each condition had one. A plan that raises is a violation
    of the first condition that raises alone. A condition the writer refuses
    for the engine refuses the check (`SverifyError`), with no fallback to
    Ibis. Without an `engine`, Ibis counts each condition on the table's own
    backend (`violations`)."""
    counts: dict[int, tuple[int, str | None]] = {}
    on_table = [i for i, c in enumerate(conds) if isinstance(c, TableCondition)]
    if on_table:
        table_conds = [c for c in conds if isinstance(c, TableCondition)]
        for i, n in zip(on_table, _table_counts(table, table_conds, engine), strict=True):
            counts[i] = (n, None)
    if engine is None:
        for i, c in enumerate(conds):
            if i in counts:
                continue
            counts[i] = (
                _run_planned(table, c, "duckdb")
                if isinstance(c, PlannedCondition)
                else (violations(table, c), None)
            )
        return [(c, *counts[i]) for i, c in enumerate(conds)]
    groups: dict[bool, list[int]] = {True: [], False: []}
    for i, c in enumerate(conds):
        if i in counts:
            continue
        if isinstance(c, PlannedCondition):
            counts[i] = _run_planned(table, c, engine)
        else:
            groups[isinstance(c, str)].append(i)
    con = connection_of(table)
    for idxs in groups.values():
        if not idxs:
            continue
        if con is None:
            raise ValueError("checking a condition on an engine needs a table of sverify.connect()")
        try:
            out = _run_conditions(con, table, [conds[i] for i in idxs], engine)
            for k, i in enumerate(idxs):
                counts[i] = (_not_true(out.column(k)), None)
        except SverifyError:
            raise
        except Exception:
            # Which condition raised: run them one by one.
            for i in idxs:
                try:
                    counts[i] = (
                        _not_true(_run_conditions(con, table, [conds[i]], engine).column(0)),
                        None,
                    )
                except SverifyError:
                    raise
                except Exception as e:
                    counts[i] = (0, str(e).splitlines()[0] if str(e) else type(e).__name__)
    return [(c, *counts[i]) for i, c in enumerate(conds)]


def _run_planned(table: ir.Table, cond: PlannedCondition, engine: str) -> tuple[int, str | None]:
    """The rows of `table` that break a condition read from an export, from its
    own plan run on `engine`; a plan that raises is a violation."""
    con = connection_of(table)
    if con is None:
        raise ValueError("checking a condition on an engine needs a table of sverify.connect()")
    try:
        return _not_true(run_plan(con, written_plan(cond.plan), engine).column(0)), None
    except SverifyError:
        raise
    except Exception as e:
        return 0, str(e).splitlines()[0] if str(e) else type(e).__name__


def _not_true(column: Any) -> int:
    return sum(v is not True for v in column.to_pylist())


def _run_conditions(
    con: Connection, table: ir.Table, conds: Sequence[Condition], engine: str
) -> pa.Table:
    """The columns of `conds` over `table`, from one checker-written plan run
    on `engine`: SQL conditions as one `SELECT`, Ibis ones as one `select`."""
    if all(isinstance(c, str) for c in conds):
        items = ", ".join(f'({c}) AS "c{i}"' for i, c in enumerate(conds))
        query = f'SELECT {items} FROM "t" AS "t"'
        from sverify.ibis_substrait import SQLModel, sql_model_schema

        schema = sql_model_schema(query, {"t": table.schema()}, "reference")
        inputs: Any = (table.op(),)  # a table's op is the relation the model reads
        q = SQLModel(query, inputs, ("t",), schema, "duckdb", "reference").to_expr()
    else:
        q = table.select(**{f"c{i}": resolve(c, table) for i, c in enumerate(conds)})
    return run_plan(con, written_plan(plan_json(con, q)), engine)


def violating_rows(table: ir.Table, cond: Condition, limit: int = ROWS_SHOWN) -> pa.Table | None:
    """Up to `limit` rows of the bound `table` where `cond` is not TRUE, or
    for `unique`, the rows of a repeated key; None for a condition on the
    table as a whole, or if the rows cannot be fetched (they only go into an
    error, which says how many rows break the condition either way)."""
    try:
        if isinstance(cond, Unique):
            cols = list(cond.cols)
            counts = table.group_by(cols).aggregate(__sverify_n=table.count())
            dup = counts.filter(counts["__sverify_n"] > 1).select(cols)
            return table.semi_join(dup, cols).limit(limit).to_pyarrow()
        if isinstance(cond, TableCondition):
            return None
        if isinstance(cond, str):
            backend: Any = ibis.get_backend(table)
            sql = ibis.to_sql(table, dialect=backend.name)
            query = (
                f'SELECT * FROM ({sql}) AS "t" WHERE NOT coalesce(({cond}), FALSE) LIMIT {limit}'
            )
            # Fetch every row, as `violations` does, so that the connection
            # is free for the next query (DuckDB 2 refuses work on a
            # connection with a result left unread).
            import pyarrow

            cur = backend.raw_sql(query)
            names = [d[0] for d in cur.description]
            rows = [dict(zip(names, r, strict=True)) for r in cur.fetchall()]
            return pyarrow.Table.from_pylist(rows, schema=table.schema().to_pyarrow())
        bad = table.filter(~resolve(cond, table).fill_null(ibis.literal(False)))
        return bad.limit(limit).to_pyarrow()
    except Exception:
        return None


def _example(table: ir.Table, cond: Condition, col: str) -> object:
    """One value of column `col` where `cond` is not TRUE, for a message."""
    rows = violating_rows(table, cond, 1)
    return rows.column(col)[0].as_py() if rows is not None and rows.num_rows else "?"


def refuse_schema(plan: object, con: Connection, engine: str | None = None) -> None:
    """Refuse a table of `con` that differs from the schema `plan` was verified
    for (`sverify._run_schema`): a missing column, a type the reader would
    change, a NULL in a column read as non-null, an integer outside the
    declared type's range (D46). An Arrow table's range is one native pass; a
    table the engine reads where it is has its range counted on `engine`."""
    for t, schemas in declared_columns(plan).items():
        if not con.has(t):
            continue
        z = con.get(t)
        data = z if isinstance(z, pa.Table) else None
        checks: set[tuple[str, str | None]] = set()
        for declared in schemas:
            found, more = schema_problems(declared, con.schema(t), data)
            if found:
                raise PreconditionError(
                    f"table {t} differs from the schema the plan was verified for: "
                    + "; ".join(found)
                    + ": refused before the run. Declare the column as it is (a wider "
                    "integer type for a value outside the width), or fix the source"
                )
            checks.update(more)
        table = con.table(t)
        todo: list[tuple[str, str | None, Any]] = []
        for col, key in sorted(checks, key=lambda c: (c[0], c[1] or "")):
            x: Any = ibis._[col]
            if key is None:
                todo.append((col, key, x.notnull()))
            else:
                lo, hi = int_range(key)
                todo.append((col, key, x.isnull() | ((x >= lo) & (x <= hi))))
        # One plan over the table counts every check (`violation_counts`).
        counts = (
            violation_counts(table, [cond for _col, _key, cond in todo], engine) if todo else []
        )
        for (col, key, cond), (_c, n, error) in zip(todo, counts, strict=True):
            if n or error:
                what = (
                    f"the check of column {col!r} raised: {error}"
                    if error
                    else null_message(col, n)
                    if key is None
                    else range_message(col, key, n, _example(table, cond, col))
                )
                raise PreconditionError(
                    f"table {t} differs from the schema the plan was verified for: {what}"
                    ": refused before the run. Declare the column as it is (a wider integer "
                    "type for a value outside the width), or fix the source",
                    source=t,
                )
