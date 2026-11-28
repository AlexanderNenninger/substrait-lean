"""DuckDB's SQL as sverify's lift reads it (#866): its `Surface`, with the
checks of the text SQLGlot's DuckDB dialect cannot tell apart, and the front
end `sverify_duckdb.PLUGIN` registers. The lift itself is shared
(`sverify.sql_lift`)."""

from __future__ import annotations

import re
from collections.abc import Mapping, Sequence
from typing import Any

import sqlglot as sg
import sqlglot.expressions as sge
from ibis.backends.sql.datatypes import DuckDBType

from sverify.plan_json import Unsupported
from sverify.sql_lift import DUCKDB, Lifted, Surface, lift, reading
from sverify.sql_lift._base import _KNOWN, full_name

#: Quoted text (strings, quoted names) and comments, which hold no numbers.
_QUOTED = re.compile(r"'(?:[^']|'')*'|\"(?:[^\"]|\"\")*\"|--[^\n]*|/\*.*?\*/", re.S)
#: A number as written, from its first digit (not inside a name).
_NUMBER = re.compile(r"(?<![\w$.])\d[\w.]*")


def _check_numbers(query: str, tokens: Sequence[Any]) -> None:
    """Refuse a number with an underscore that is not between two digits
    (`1__2`, `1._5`). DuckDB reads such an underscore as the start of an
    alias (`1__2` is 1 named `__2`); SQLGlot reads every underscore as a digit
    separator (12), upstream/bugs/SG-4.json."""
    for m in _NUMBER.finditer(_QUOTED.sub(" ", query)):
        if re.search(r"(?<!\d)_|_(?!\d)", m.group()):
            raise Unsupported(
                f"the number {m.group()!r}: an underscore not between two digits is read "
                "differently by DuckDB and SQLGlot (SG-4); write the number without it",
                construct="NUMERIC LITERAL",
            )


def _check_regex_operators(query: str, tokens: Sequence[Any]) -> None:
    """Refuse `s ~ p` and `s !~ p`: DuckDB's `~` matches anywhere in `s`
    (`regexp_matches`), but SQLGlot reads it as `regexp_full_match`, so the
    tree cannot tell them apart (upstream/bugs/SG-10.json). A `~` before an
    operand is the bitwise not."""
    from sqlglot.tokens import TokenType

    operand = {TokenType.STRING, TokenType.NUMBER, TokenType.VAR, TokenType.IDENTIFIER,
               TokenType.R_PAREN, TokenType.R_BRACKET, TokenType.NULL, TokenType.TRUE,
               TokenType.FALSE}  # fmt: skip
    for k, tok in enumerate(tokens):
        if tok.token_type != TokenType.TILDE or k == 0:
            continue
        before = tokens[k - 1]
        if before.token_type == TokenType.NOT and before.text == "!" and k > 1:
            before = tokens[k - 2]
        if before.token_type in operand:
            raise Unsupported(
                "the regular expression operator ~ is not supported yet: SQLGlot reads it as "
                "regexp_full_match, DuckDB as regexp_matches; write regexp_matches(s, p)",
                construct="REGULAR EXPRESSION OPERATOR",
            )


def _check_date_bin(query: str, tokens: Sequence[Any]) -> None:
    """Refuse `date_bin(...)`: DuckDB 2.0.0 has no such function, but SQLGlot reads it as the
    node of `time_bucket`, so the tree cannot tell them apart."""
    from sqlglot.tokens import TokenType

    for tok, after in zip(tokens, tokens[1:], strict=False):
        if (
            tok.token_type == TokenType.VAR
            and tok.text.lower() == "date_bin"
            and after.token_type == TokenType.L_PAREN
        ):
            raise Unsupported(
                "DuckDB has no function date_bin; write time_bucket(width, ts[, origin])",
                construct="function date_bin",
            )


def _check_intervals(query: str, tokens: Sequence[Any]) -> None:
    """Refuse `INTERVAL '… ago'`, which negates the interval in DuckDB.
    SQLGlot drops the `ago` of a single unit (`'1 day ago'` reads as
    `INTERVAL '1' DAY`), so the tree cannot tell (#626, upstream/bugs/SG-8.json)."""
    from sqlglot.tokens import TokenType

    for before, tok in zip(tokens, tokens[1:], strict=False):
        if (
            before.token_type == TokenType.INTERVAL
            and tok.token_type == TokenType.STRING
            and re.search(r"\bago\b", tok.text, re.I)
        ):
            raise Unsupported(
                f"INTERVAL {tok.text!r}: an interval with `ago` is not supported yet (SG-8); "
                "write a negative interval, INTERVAL '-1' DAY",
                construct="INTERVAL",
            )


def _builtin_schemas(tree: sge.Expr) -> sge.Expr:
    """A call qualified by its built-in schema (`main.lower(x)`,
    `system.main.lower(x)`) read as the bare function (#328). DuckDB reads
    no other qualifier of a built-in function (`pg_catalog.lower(x)` and
    `memory.main.lower(x)` are binder errors), so neither does the lift.
    SQLGlot reads `lower(x)` as `Lower` but the qualified call as an
    anonymous one, so the call is parsed again without its qualifier."""

    def bare(n: sge.Expr) -> sge.Expr:
        if isinstance(n, sge.Dot) and isinstance(n.expression, sge.Anonymous):
            path = [n.this] if not isinstance(n.this, sge.Dot) else [n.this.this, n.this.expression]
            names = [p.name.lower() if isinstance(p, sge.Identifier) else None for p in path]
            if names in (["main"], ["system", "main"]):
                return sg.parse_one(n.expression.sql("duckdb"), read="duckdb")
        return n

    return tree.transform(bare, copy=False)


#: DuckDB's SQL as the lift reads it: its own semantics is `DUCKDB`, and its
#: generated lift table's semantics are `duckdb` and `reference`.
DUCKDB_SQL = Surface(
    "duckdb",
    "DuckDB",
    DUCKDB,
    null_ordering="nulls_are_last",
    types=DuckDBType,
    catalog="memory",
    db="main",
    generated={"duckdb": "duckdb", "portable": "reference"},
    checks=(_check_numbers, _check_intervals, _check_regex_operators, _check_date_bin),
    rewrites=(_builtin_schemas,),
    known=_KNOWN,
)


def lift_duckdb(query: str, schemas: Mapping[str, Any], semantics: str = "duckdb") -> Lifted:
    """DuckDB's SQL `query` lifted to a plan over the Ibis schemas `schemas`
    (by table name), under the profile `semantics` names (`"duckdb"` or
    `"portable"`): `sverify.sql_lift.lift` with DuckDB's surface."""
    return lift(query, schemas, semantics, surface=DUCKDB_SQL)


def read_tables(query: str) -> set[tuple[str, str, str]]:
    """The tables `query` reads, by DuckDB's resolution (`shop.main.orders`
    reads the input of that key); none where SQLGlot cannot parse it (the lift
    says why)."""
    with reading(DUCKDB_SQL):
        try:
            return {full_name(t) for t in sg.parse_one(query, read="duckdb").find_all(sge.Table)}
        except sg.errors.ParseError:
            return set()


def full_name_duckdb(table: sge.Table | str) -> tuple[str, str, str]:
    """A table name's (catalog, schema, name) as DuckDB resolves it."""
    with reading(DUCKDB_SQL):
        return full_name(table)
