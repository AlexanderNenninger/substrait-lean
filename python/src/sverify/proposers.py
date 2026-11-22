"""Proposers: what proposes a precondition or a counterexample for an
obligation the checker leaves open (#2245).

Internal: not part of sverify's public API (`docs/stability.md`); it may
change in any release.

A proposer only proposes. A report relies on a proposal only once it is
confirmed: a precondition by proving the postcondition again under it
(`verify` with `infer`), a counterexample by `Rel.eval`. A proposal's
`verdict` says whether it is confirmed yet.

sverify has two proposers, and `verify` runs them itself:

- `infer`: the checker's backward interval pass (`Infer.suggest`,
  `analysis/Sverify/Analysis/Infer.lean`) proposes bounds on input columns,
  and `Infer` writes them as conditions on the tables;
- `search`: the bounded search of `sverify.counterexample` proposes small
  input tables, each one evaluated by `Rel.eval`.

A package registers a proposer of its own under the entry-point group
`sverify.proposers`, as an engine registers under `sverify.profiles`:

```toml
[project.entry-points."sverify.proposers"]
myproposer = "my_package:PROPOSER"
```

`proposers()` lists them; `verify` runs none but its own two yet (#2245).
"""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from datetime import date, datetime, timedelta
from importlib.metadata import entry_points
from typing import Any, Literal, Protocol

from sverify import _decimals, _engines, counterexample
from sverify._checker import MAX_MAG, decode_double
from sverify.conditions import TextFact
from sverify.report import Inferred

#: The entry-point group a package registers its proposer under.
GROUP = "sverify.proposers"

Kind = Literal["precondition", "counterexample"]
"""What an obligation asks for: preconditions that would prove it, or input
tables on which it fails."""


@dataclass(frozen=True)
class Obligation:
    """What the checker leaves open, and what a proposer needs to propose
    for it."""

    kind: Kind
    schemas: Mapping[str, Any]
    """The input tables' Ibis schemas, by name."""
    data: Mapping[str, Any]
    """The rest, by kind. A precondition: `needs`, the checker's bounds
    (`{table, col, lo, hi}`, `{table, col, ne}`, `{table, col, not_null}` or
    `{table, col, text}`). A counterexample: the keyword arguments of
    `sverify.counterexample.search` after the schemas."""


@dataclass(frozen=True)
class Verdict:
    """Whether a proposal is confirmed, and by what."""

    ok: bool
    proved_by: str
    """`"Rel.eval"` for a counterexample evaluated on the plan."""


@dataclass(frozen=True)
class Proposal:
    """What a proposer proposes for one obligation."""

    proposer: str
    value: Any
    """By kind: the conditions per table (`Inferred`), or a `Counterexample`."""
    verdict: Verdict | None = None
    """None until something confirms it."""


class Proposer(Protocol):
    """Proposes for the obligations of its kinds; None where it has nothing."""

    name: str
    kinds: tuple[Kind, ...]

    def propose(self, obligation: Obligation) -> Proposal | None: ...


def _nice(x: int, up: bool) -> tuple[int, str]:
    """A round number near `x`, at or above it if `up`, else at or below,
    and how to write it: `2**62`, `3 * 10**18` or `1_000`."""
    if x < 0:
        v, text = _nice(-x, not up)
        return -v, f"-{text}" if v else "0"
    if x < 10**6:
        return x, f"{x:_}"
    k = x.bit_length() - 1
    two = 2 ** (k + 1 if up and 2**k < x else k)
    e = len(str(x)) - 1
    d = x // 10**e + (1 if up and x % 10**e else 0)
    ten = d * 10**e
    better = min if up else max
    v = better(two, ten)
    if v == two:
        return v, f"2**{v.bit_length() - 1}"
    d, e = (v // 10**e, e) if v // 10**e < 10 else (1, e + 1)
    return v, (f"10**{e}" if d == 1 else f"{d} * 10**{e}")


_EPOCH = datetime(1970, 1, 1)


_US_MIN = (datetime.min - _EPOCH) // timedelta(microseconds=1)


_US_MAX = (datetime.max - _EPOCH) // timedelta(microseconds=1)


def _year_of(code: int, per_year_unit: timedelta) -> int:
    """The year of a timestamp (microseconds) or date (days) code, clamped to
    Python's years."""
    us = code * (per_year_unit // timedelta(microseconds=1))
    if us < _US_MIN:
        return 1
    if us > _US_MAX:
        return 9999
    return (_EPOCH + timedelta(microseconds=us)).year


def _bound_conditions(col: str, dtype: Any, lo: int | None, hi: int | None) -> list[Inferred]:
    """`lo <= col <= hi` as conditions, rounded inward to round numbers (or
    whole years), each side its own condition. Empty for a type the
    inference does not write bounds for."""
    ref = f"_.{col}" if col.isidentifier() else f"_[{col!r}]"
    sql = '"' + col.replace('"', '""') + '"'
    # NULL cannot overflow, so a bound lets it pass.
    null = f"{sql} IS NULL OR " if dtype.nullable else ""
    out = []
    if dtype.is_integer():
        # A side at or past 64 bits holds for every integer column, and its
        # constant (2**63) would be a HUGEINT, which the lift refuses (#616).
        # A narrower column's own limits stay, the proof needs them stated,
        # each a constant of the column's type, so it is a fact about the
        # column (`v <= 127` on a TINYINT, not `v < 128`).
        if lo is not None and lo <= -(2**63):
            lo = None
        if hi is not None and hi >= 2**63 - 1:
            hi = None
        if lo is not None:
            if lo <= dtype.bounds.lower:
                v, text = dtype.bounds.lower, f"{dtype.bounds.lower:_}"
            else:
                v, text = _nice(lo, up=True)
            out.append(Inferred(f"{null}{sql} >= {v}", f"({ref} >= {text})"))
        if hi is not None:
            if hi >= dtype.bounds.upper:
                top = dtype.bounds.upper
                out.append(Inferred(f"{null}{sql} <= {top}", f"({ref} <= {top:_})"))
            else:
                v, text = _nice(hi + 1, up=False)
                out.append(Inferred(f"{null}{sql} < {v}", f"({ref} < {text})"))
        return out
    if dtype.is_floating():
        return _double_conditions(ref, sql, null, lo, hi)
    if dtype.is_decimal() and dtype.scale is not None:
        scale = dtype.scale

        def dec(k: int) -> str:
            text = f"{_decimals.scaled(k, -scale):.{scale}f}"
            if scale == 0 and abs(k) >= 2**63:
                # A whole number past 64 bits reads as a HUGEINT, which the
                # lift refuses (#1252); cast from a string it stays a decimal.
                return f"CAST('{text}' AS DECIMAL(38, 0))"
            return text

        # Large bounds as round whole numbers (`5 * 10**35`), small ones exactly.
        if lo is not None:
            if abs(lo) >= 10 ** (scale + 6):
                v, text = _nice(-((-lo) // 10**scale), up=True)
                out.append(Inferred(f"{null}{sql} >= {dec(v * 10**scale)}", f"({ref} >= {text})"))
            else:
                out.append(Inferred(f"{null}{sql} >= {dec(lo)}", f"({ref} >= {dec(lo)})"))
        if hi is not None:
            if abs(hi) >= 10 ** (scale + 6):
                v, text = _nice(hi // 10**scale + 1, up=False)
                out.append(Inferred(f"{null}{sql} < {dec(v * 10**scale)}", f"({ref} < {text})"))
            else:
                out.append(Inferred(f"{null}{sql} <= {dec(hi)}", f"({ref} <= {dec(hi)})"))
        return out
    if dtype.is_timestamp() and dtype.timezone is None:
        unit, kind, py = timedelta(microseconds=1), "TIMESTAMP", "datetime"
    elif dtype.is_date():
        unit, kind, py = timedelta(days=1), "DATE", "date"
    else:
        return []

    def code(year: int) -> int:
        return (datetime(year, 1, 1) - _EPOCH) // unit

    def lit(year: int) -> str:
        day = date(year, 1, 1)
        return f"{kind} '{day.isoformat()}{' 00:00:00' if kind == 'TIMESTAMP' else ''}'"

    if lo is not None and hi is not None and lo > hi:
        return []  # no value meets it: nothing to suggest
    if lo is not None:
        y = _year_of(lo, unit)
        if code(y) < lo:
            y += 1
        if y > 9999 and lo > (datetime.max - _EPOCH) // unit:
            return []  # past Python's last datetime: no value meets it
        if y > 9999:
            # Inside the last year: no whole year to round up to, so the bound
            # itself, as Python's last datetime or date allows.
            exact = _EPOCH + lo * unit
            text = exact.isoformat(sep=" ") if kind == "TIMESTAMP" else exact.date().isoformat()
            args = (
                ", ".join(map(str, exact.timetuple()[:6]))
                if kind == "TIMESTAMP"
                else (f"{exact.year}, {exact.month}, {exact.day}")
            )
            out.append(Inferred(f"{null}{sql} >= {kind} '{text}'", f"({ref} >= {py}({args}))"))
        else:
            out.append(Inferred(f"{null}{sql} >= {lit(y)}", f"({ref} >= {py}({y}, 1, 1))"))
    if hi is not None:
        last = (
            datetime(9999, 12, 31, 23, 59, 59, 999999)
            if kind == "TIMESTAMP"
            else datetime(9999, 12, 31)
        )
        if hi >= (last - _EPOCH) // unit:
            # Up to the reference's last one (D32): 9999-12-31 itself holds.
            if kind == "TIMESTAMP":
                text, args = "9999-12-31 23:59:59.999999", "9999, 12, 31, 23, 59, 59, 999999"
            else:
                text, args = "9999-12-31", "9999, 12, 31"
            out.append(Inferred(f"{null}{sql} <= {kind} '{text}'", f"({ref} <= {py}({args}))"))
        else:
            y = _year_of(hi + 1, unit)
            out.append(Inferred(f"{null}{sql} < {lit(y)}", f"({ref} < {py}({y}, 1, 1))"))
    return out


# Codes of the smallest positive and the largest finite double.
_TINY_CODE = 1


_MAX_CODE = 2 * MAX_MAG + 1


def _double_conditions(
    ref: str, sql: str, null: str, lo: int | None, hi: int | None
) -> list[Inferred]:
    """`lo <= col <= hi` on double codes: `> 0` for the smallest positive
    double, round powers of two near ±2⁶³ (a cast to BIGINT), and the
    decoded doubles otherwise."""

    def num(x: float) -> str:
        if x.is_integer() and abs(x) >= 1e6:
            return _nice(int(x), up=x < 0)[1]
        return repr(x)

    out = []
    if lo is not None:
        if lo == _TINY_CODE:
            out.append(Inferred(f"{null}{sql} > 0", f"({ref} > 0)"))
        elif lo > -_MAX_CODE:
            x = decode_double(lo)
            out.append(Inferred(f"{null}{sql} >= {x!r}", f"({ref} >= {num(x)})"))
        else:
            x = decode_double(-_MAX_CODE)
            out.append(Inferred(f"{null}{sql} >= {x!r}", f"({ref} >= {x!r})"))
    if hi is not None:
        nxt = decode_double(hi + 1)
        if hi < _MAX_CODE and nxt.is_integer() and abs(nxt) >= 1e6:
            # Just below a round number: `< 2**63`.
            out.append(Inferred(f"{null}{sql} < {nxt!r}", f"({ref} < {num(nxt)})"))
        else:
            x = decode_double(min(hi, _MAX_CODE))
            out.append(Inferred(f"{null}{sql} <= {x!r}", f"({ref} <= {x!r})"))
    return out


def _ne_condition(col: str, dtype: Any, k: int) -> Inferred | None:
    """`col != k`, for a code `k` of the column's type (a divisor's 0)."""
    ref = f"_.{col}" if col.isidentifier() else f"_[{col!r}]"
    sql = '"' + col.replace('"', '""') + '"'
    null = f"{sql} IS NULL OR " if dtype.nullable else ""
    if dtype.is_integer():
        v = str(k)
    elif dtype.is_floating():
        v = repr(decode_double(k))
    elif dtype.is_decimal() and dtype.scale is not None:
        v = f"{_decimals.scaled(k, -dtype.scale):.{dtype.scale}f}"
    else:
        return None
    return Inferred(f"{null}{sql} <> {v}", f"({ref} != {v})")


def _not_null_condition(col: str) -> Inferred:
    """`col IS NOT NULL` (a divisor's `COUNT` of the column)."""
    ref = f"_.{col}" if col.isidentifier() else f"_[{col!r}]"
    sql = '"' + col.replace('"', '""') + '"'
    return Inferred(f"{sql} IS NOT NULL", f"{ref}.notnull()")


def _text_condition(col: str, fact: TextFact) -> Inferred:
    """`col` holds text of the declared `fact` (NULL passes): `"ascii"`, the precondition
    under which `ILIKE`, `reverse`, `ascii` and `levenshtein` agree across engines
    (#1506); `"plain"` for a regular expression with `\\w`, `\\d`, `\\s` or `\\b`, no
    vertical tab either (`Text.classesDiffer`); `"upper_agreed"` and `"lower_agreed"`,
    in the agreed alphabet of `UPPER` or `LOWER`: no scalar the engines map differently
    (`Text.upperRaises`, `lowerRaises`, D51).
    Its SQL is the writers' guard in the default engine's dialect, the one the data is
    checked on; its Ibis form is one regular expression with the same characters."""
    from sverify.sql.core import ascii_text, case_class

    dialect = _engines.sql_dialect()
    sql = '"' + col.replace('"', '""') + '"'
    ref = f"_.{col}" if col.isidentifier() else f"_[{col!r}]"
    if fact in ("upper_agreed", "lower_agreed"):
        which: Literal["upper", "lower"] = "upper" if fact == "upper_agreed" else "lower"
        bad = case_class(which)
        cond = f"NOT {dialect().case_differs(sql, which)}"
    else:
        bad = r"[^\x00-\x7f]|\x0b" if fact == "plain" else r"[^\x00-\x7f]"
        cond = ascii_text(dialect(), sql, fact == "plain")
    out = Inferred(f"{sql} IS NULL OR {cond}", f"(~{ref}.re_search({bad!r}))")
    out.fact = fact
    return out


class Infer:
    """The checker's backward pass, written as conditions on the tables."""

    name = "infer"
    kinds: tuple[Kind, ...] = ("precondition",)

    def propose(self, obligation: Obligation) -> Proposal | None:
        conds = self.conditions(obligation.data["needs"], obligation.schemas)
        return Proposal(self.name, conds) if conds else None

    @staticmethod
    def conditions(needs: Sequence[dict], schemas: Mapping[str, Any]) -> dict[str, list[Inferred]]:
        """The conditions of the checker's bounds (column positions, integer
        codes as strings), per table."""
        out: dict[str, list[Inferred]] = {}
        for n in needs:
            schema = schemas.get(n["table"])
            if schema is None or n["col"] >= len(schema):
                continue
            col = list(schema)[n["col"]]
            have = out.setdefault(n["table"], [])
            if "text" in n:
                new = [_text_condition(col, n["text"])]
            elif n.get("not_null"):
                new = [_not_null_condition(col)] if schema[col].nullable else []
            elif "ne" in n:
                c = _ne_condition(col, schema[col], int(n["ne"]))
                new = [] if c is None else [c]
            else:
                lo, hi = (None if n[k] is None else int(n[k]) for k in ("lo", "hi"))
                new = _bound_conditions(col, schema[col], lo, hi)
            for c in new:
                c.column = col
            have += [c for c in new if c not in have]
        return {t: cs for t, cs in out.items() if cs}


class Search:
    """The bounded counterexample search. It evaluates every hit by
    `Rel.eval`, so a proposal comes confirmed."""

    name = "search"
    kinds: tuple[Kind, ...] = ("counterexample",)

    def propose(self, obligation: Obligation) -> Proposal | None:
        found = counterexample.search(obligation.schemas, **obligation.data)
        if found is None:
            return None
        return Proposal(self.name, found, Verdict(True, "Rel.eval"))


INFER = Infer()
SEARCH = Search()


def proposers() -> dict[str, Proposer]:
    """Every proposer by name: sverify's own, and those registered under
    `sverify.proposers`. A registered one with a built-in's name is skipped."""
    out: dict[str, Proposer] = {p.name: p for p in (INFER, SEARCH)}
    for ep in entry_points(group=GROUP):
        if ep.name not in out:
            out[ep.name] = ep.load()
    return out
