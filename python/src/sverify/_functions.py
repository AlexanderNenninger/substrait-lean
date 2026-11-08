"""The function table: one row per simple scalar function (strings, math,
bitwise), with its Substrait anchor, area and group, and what the SQL writer,
the SQL lift and the Ibis producer make of it (#544, wave 3).

The rows follow `docs/core-semantics.md`: a function's options are its
group's (`GROUPS`), each option is a row of `OPTIONS`, and each profile
chooses among an option's behaviours (`CHOICES`). Lean's tables are the
source (D1, `core/Sverify/Core/Functions.lean`); `tests/test_functions.py`
checks the names, anchors, groups, options and the reference's choices
against them (`substrait-check --functions` and `--options`, #444).

Internal: not part of sverify's public API. It imports nothing of sverify's,
so every layer can read it.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass, field
from types import MappingProxyType
from typing import Literal

# -- options and choices ------------------------------------------------------


@dataclass(frozen=True)
class Option:
    """A choice point: an option of Substrait's (`substrait` is its name in
    the YAML) or sverify's own (`None`), with the behaviours the core allows."""

    id: str
    substrait: str | None
    core: tuple[str, ...]
    extra: tuple[tuple[str, str], ...] = ()
    """Behaviours outside the YAML, each with the fact that records it."""


@dataclass(frozen=True)
class Choice:
    """A profile's choice for an option: Lean's `Choice.oneOf behaviours`
    when `default` is `None`, otherwise `Choice.asked behaviours default`:
    the plan's first preference among `behaviours`, `default` where it states
    none."""

    behaviours: tuple[str, ...]
    default: tuple[str, ...] | None = None


def _asked(*bs: str) -> Choice:
    """The plan's preference among `bs`; the first where it states none."""
    return Choice(bs, bs[:1])


_ROUNDINGS = ("TIE_TO_EVEN", "TIE_AWAY_FROM_ZERO", "TRUNCATE", "CEILING", "FLOOR")
#: `round`'s five more.
_ROUND_TIES = ("AWAY_FROM_ZERO", "TIE_DOWN", "TIE_UP", "TIE_TOWARDS_ZERO", "TIE_TO_ODD")

#: The options of the groups below (`docs/core-semantics.md`, "The option catalogue").
OPTIONS: Mapping[str, Option] = MappingProxyType(
    {
        o.id: o
        for o in (
            Option("rounding", "rounding", (*_ROUNDINGS, *_ROUND_TIES, "RECIPROCAL"),
                   (("RECIPROCAL", "polars-scalar-divisor"),)),
            Option("on_domain_error", "on_domain_error", ("NAN", "NULL", "ERROR"),
                   (("NAN", "duckdb-R15-math-domain"),)),
            Option("on_log_zero", "on_log_zero", ("NAN", "ERROR", "MINUS_INFINITY")),
            Option("shift_range", None, ("ERROR", "ZERO", "DROP_BITS"),
                   (("ERROR", "duckdb-R15-shift-left"), ("ZERO", "duckdb-R15-shift-right"))),
            Option("negative_start", "negative_start",
                   ("WRAP_FROM_END", "LEFT_OF_BEGINNING", "ERROR")),
            Option("substring_range", None, ("ERROR", "COMPUTE"),
                   (("ERROR", "duckdb-substring-range"),)),
            Option("case_sensitivity", "case_sensitivity",
                   ("CASE_SENSITIVE", "CASE_INSENSITIVE", "CASE_INSENSITIVE_ASCII")),
            Option("char_set", "char_set", ("UTF8", "ASCII_ONLY")),
            Option("null_handling", "null_handling", ("IGNORE_NULLS", "ACCEPT_NULLS")),
            Option("string_positions", None,
                   ("ONE_BASED_CHARS", "ZERO_BASED_CHARS", "ZERO_BASED_BYTES"),
                   (("ZERO_BASED_CHARS", "polars-substring"),
                    ("ZERO_BASED_BYTES", "polars-strpos"))),
        )
    }
)  # fmt: skip

#: Each group's options, in the order the design lists them.
GROUPS: Mapping[str, tuple[str, ...]] = MappingProxyType(
    {
        "int.bit": (),
        "int.shift": ("shift_range",),
        "fp.elem": ("rounding", "on_domain_error"),
        "fp.log": ("rounding", "on_domain_error", "on_log_zero"),
        "str.sub": ("negative_start", "substring_range", "string_positions"),
        "str.match": ("case_sensitivity", "string_positions"),
        "str.case": ("char_set",),
        "str.concat": ("null_handling",),
        "str.plain": (),
        "str.opaque": (),
    }
)

#: Each profile's choice, by (group, option); a `None` group is every group's.
CHOICES: Mapping[str, Mapping[tuple[str | None, str], Choice]] = MappingProxyType(
    {
        "reference": MappingProxyType(
            {
                (None, "rounding"): _asked("TIE_TO_EVEN"),
                (None, "on_domain_error"): _asked("ERROR"),  # #215
                (None, "on_log_zero"): _asked("ERROR"),
                (None, "shift_range"): Choice(("DROP_BITS",)),
                (None, "negative_start"): _asked("WRAP_FROM_END", "LEFT_OF_BEGINNING"),  # #209
                (None, "substring_range"): Choice(("ERROR",)),  # #336
                (None, "case_sensitivity"): _asked("CASE_SENSITIVE"),
                (None, "char_set"): _asked("UTF8"),
                (None, "null_handling"): _asked("ACCEPT_NULLS"),
                (None, "string_positions"): Choice(("ONE_BASED_CHARS",)),
            }
        ),
        "duckdb": MappingProxyType(
            {
                (None, "rounding"): Choice(("TIE_TO_EVEN",)),
                (None, "on_domain_error"): Choice(("NAN",)),  # duckdb-R15-math-domain
                (None, "on_log_zero"): Choice(("MINUS_INFINITY",)),
                (None, "shift_range"): Choice(("ERROR", "ZERO")),  # R15-shift-*
                (None, "negative_start"): Choice(("WRAP_FROM_END",)),  # duckdb-R13
                (None, "substring_range"): Choice(("ERROR",)),  # duckdb-substring-range
                (None, "case_sensitivity"): Choice(("CASE_SENSITIVE",)),
                (None, "char_set"): Choice(("UTF8",)),
                (None, "null_handling"): Choice(("ACCEPT_NULLS",)),
                (None, "string_positions"): Choice(("ONE_BASED_CHARS",)),
            }
        ),
    }
)


def choice(profile: str, group: str, option: str) -> Choice:
    """`profile`'s choice for `option` in `group`: the group's own row, else
    the option's."""
    rows = CHOICES[profile]
    return rows.get((group, option)) or rows[(None, option)]


# -- functions ------------------------------------------------------------------


@dataclass(frozen=True)
class No:
    """A dialect that does not write the function, and why."""

    reason: str


#: The SQL writer's kinds of results that are not booleans (`UN_KINDS`).
FixedKind = Literal["int", "float", "str", "time", "date", "tod"]
#: A function's arguments and result, as the SQL writer's kinds.
ArgKind = Literal["str", "int", "float"]
ResultKind = Literal["str", "int", "float", "bool"]


@dataclass(frozen=True)
class Fn:
    name: str
    """Substrait's name, as `Functions.lean` declares it."""
    anchor: int
    area: Literal["core", "strings"]
    group: str
    args: tuple[ArgKind, ...] = ()
    """The kinds of its arguments where the table's rules read them."""
    result: ResultKind = "bool"
    op: str = ""
    """The SQL writer's `Un.op` or `Bin.op` ("" for none)."""
    node: Literal["Un", "Bin"] | None = None
    """`Un` or `Bin`; by default `Un` for one argument and `Bin` for two."""
    param: bool = False
    """The writer's operation carries the name in its `param` (`fmath`, `bit`)."""
    call: bool = True
    """`mkCall` makes the operation of the arguments as they are."""
    expr: bool = False
    """The writer writes `sql` of its operands (`_Writer.table_expr`)."""
    label: str = ""
    """What its error messages call it; the name by default."""
    ascii: str = ""
    """Engines agree on ASCII text only: what the guard's error calls it."""
    sql: Mapping[str, str | No] = field(default_factory=dict)
    """The SQL by dialect name, `""` for every other, with `{0}`, `{1}` for
    the operands; a dialect with neither refuses (`Dialect.refused`)."""
    aliases: tuple[str, ...] = ()
    """Other names `mkCall` reads."""
    lift: tuple[str, ...] = ()
    """SQLGlot's nodes that the lift reads as this function, by the area's rule."""
    ibis: tuple[str, ...] = ()
    """Ibis's operations that the producer writes as this function, by the area's rule."""

    @property
    def options(self) -> tuple[str, ...]:
        return GROUPS[self.group]

    @property
    def reference(self) -> Mapping[str, Choice]:
        """The reference's choice at each of its options."""
        return {o: choice("reference", self.group, o) for o in self.options}

    @property
    def what(self) -> str:
        return self.label or self.name

    @property
    def un(self) -> bool:
        return self.node == "Un" if self.node else len(self.args) == 1


def _libm(name: str) -> dict[str, str | No]:
    """An elementary function of a double, C's `libm` on the engines that use it."""
    sql: dict[str, str | No] = {
        "": f"{name.upper()}({{0}})",
        "snowflake": No(
            f"Snowflake's {name.upper()} is not documented to be C's libm, "
            "which the Lean model uses"
        ),
    }
    if name != "sqrt":  # IEEE 754 rounds square roots correctly, as libm does.
        sql["spark"] = No(
            f"Spark's {name.upper()} is Java's StrictMath, not the C libm the Lean model uses"
        )
    return sql


def _fp(name: str, anchor: int, group: str, lift: str, ibis: str) -> Fn:
    return Fn(name, anchor, "core", group, ("float",), "float", "fmath", param=True,
              sql=_libm(name), lift=(lift,) if lift else (), ibis=(ibis,))  # fmt: skip


def _bit(name: str, anchor: int, ibis: str, duckdb: str, spark: str, snowflake: str) -> Fn:
    # The count of a shift is in 0–63, bits shifted out are lost (`BitOp`).
    shift = "shift" in name
    return Fn(name, anchor, "core", "int.shift" if shift else "int.bit", ("int", "int"), "int",
              "bit", param=True, ibis=(ibis,), sql={
                  "duckdb": duckdb or No(f"DuckDB's {name} is its lowering's (`Dialect.lowered`)"),
                  "spark": spark,
                  "snowflake": snowflake or No(f"Snowflake's bit shifts are not 64-bit ({name})"),
              })  # fmt: skip


def _str(name: str, anchor: int, group: str, args: int, result: ResultKind, op: str = "",
         **kw: object) -> Fn:  # fmt: skip
    return Fn(name, anchor, "strings", group, ("str",) * args, result, op or name, **kw)  # type: ignore[arg-type]


#: The rows, in `Functions.lean`'s order within each area.
FUNCTIONS: tuple[Fn, ...] = (
    # Elementary functions of doubles (`FMath`, `core/Sverify/Core/Numeric.lean`).
    _fp("sqrt", 100, "fp.elem", "Sqrt", "Sqrt"),
    _fp("exp", 101, "fp.elem", "Exp", "Exp"),
    _fp("ln", 102, "fp.log", "Ln", "Ln"),
    _fp("log10", 103, "fp.log", "", "Log10"),
    _fp("log2", 104, "fp.log", "", "Log2"),
    _fp("sin", 105, "fp.elem", "Sin", "Sin"),
    _fp("cos", 106, "fp.elem", "Cos", "Cos"),
    _fp("tan", 107, "fp.elem", "Tan", "Tan"),
    _fp("asin", 108, "fp.elem", "Asin", "Asin"),
    _fp("acos", 109, "fp.elem", "Acos", "Acos"),
    _fp("atan", 110, "fp.elem", "Atan", "Atan"),
    Fn("atan2", 111, "core", "fp.elem", ("float", "float"), "float", "fatan2", ibis=("Atan2",),
       sql={"": "ATAN2({0}, {1})",
            "spark": No("Spark's ATAN2 is Java's StrictMath, not the C libm the Lean model uses"),
            "snowflake": No("Snowflake's ATAN2 is not documented to be C's libm")}),
    # `ln x / ln b` (`Dialect.float_logb`).
    Fn("logb", 112, "core", "fp.log", ("float", "float"), "float", "flogb"),
    # Bitwise operations of 64-bit integers, in two's complement (`BitOp`).
    _bit("bitwise_and", 113, "BitwiseAnd", "({0} & {1})", "({0} & {1})", "BITAND({0}, {1})"),
    _bit("bitwise_or", 114, "BitwiseOr", "({0} | {1})", "({0} | {1})", "BITOR({0}, {1})"),
    _bit("bitwise_xor", 115, "BitwiseXor", "xor({0}, {1})", "({0} ^ {1})", "BITXOR({0}, {1})"),
    # DuckDB's `<<` is its lowering's: it raises where bits are shifted out.
    _bit("bitwise_shift_left", 116, "BitwiseLeftShift", "",
         "shiftleft({0}, CAST({1} AS INT))", ""),
    _bit("bitwise_shift_right", 117, "BitwiseRightShift", "({0} >> {1})",
         "shiftright({0}, CAST({1} AS INT))", ""),
    # Strings (`core/Sverify/Core/Text.lean`): characters are Unicode scalar values.
    # Upper and lower case are a black box, Rust's `str::to_uppercase`;
    # engines map case with their own tables (`'ß'`).
    _str("upper", 20, "str.case", 1, "str", expr=True, ascii="UPPER", sql={"": "UPPER({0})"},
         lift=("Upper",), ibis=("Uppercase",)),
    _str("lower", 21, "str.case", 1, "str", expr=True, ascii="LOWER", sql={"": "LOWER({0})"},
         lift=("Lower",), ibis=("Lowercase",)),
    _str("character_length", 22, "str.plain", 1, "int", "length", expr=True, label="length",
         aliases=("char_length", "length"), ibis=("StringLength",),
         sql={"": "CHAR_LENGTH({0})", "duckdb": "length({0})", "spark": "length({0})",
              "snowflake": "LENGTH({0})"}),
    _str("regexp_match", 23, "str.opaque", 1, "int", "regex_match", call=False),
    # NULL if either is.
    _str("str_concat", 27, "str.concat", 2, "str", "concat", expr=True, label="||",
         sql={"": "({0} || {1})"}, lift=("DPipe",)),
    # The 1-based position of the first `t` in `s`, 0 if none, 1 for ''.
    _str("strpos", 28, "str.match", 2, "int", expr=True,
         sql={"": "POSITION({1} IN {0})", "duckdb": "strpos({0}, {1})",
              "spark": "locate({1}, {0})",
              # Snowflake's POSITION is 1 for an empty needle and NULL with a NULL
              # (Snowflake behaviour recorded privately).
              }),
    _str("starts_with", 29, "str.match", 2, "bool", expr=True, lift=("StartsWith",),
         ibis=("StartsWith",),
         sql={"": "starts_with({0}, {1})", "spark": "startswith({0}, {1})",
              "snowflake": "STARTSWITH({0}, {1})"}),
    _str("ends_with", 30, "str.match", 2, "bool", expr=True, lift=("EndsWith",),
         ibis=("EndsWith",),
         sql={"": "ends_with({0}, {1})", "duckdb": "suffix({0}, {1})",
              "spark": "endswith({0}, {1})", "snowflake": "ENDSWITH({0}, {1})"}),
    _str("like", 31, "str.match", 2, "bool", call=False),
    _str("substring", 32, "str.sub", 2, "str", "substr", call=False),
    _str("btrim", 33, "str.plain", 2, "str", "trim", call=False),
    _str("ltrim", 34, "str.plain", 2, "str", "trim", call=False),
    _str("rtrim", 35, "str.plain", 2, "str", "trim", call=False),
    # Engines that reverse grapheme clusters agree on ASCII text.
    _str("reverse", 200, "str.plain", 1, "str", expr=True, ascii="reverse",
         sql={"": "REVERSE({0})"}, ibis=("Reverse",)),
    # The code point of the first character, 0 for ''.
    _str("ascii", 201, "str.plain", 1, "int", expr=True, ascii="ascii", sql={"": "ASCII({0})"},
         ibis=("StringAscii",)),
    _str("replace", 202, "str.match", 1, "str", call=False),
    Fn("repeat", 203, "strings", "str.plain", ("str", "int"), "str", "repeat",
       ibis=("Repeat",)),
    _str("ilike", 204, "str.opaque", 2, "bool", call=False),
    # The edit distance in characters.
    _str("levenshtein", 205, "str.plain", 2, "int", expr=True, ascii="levenshtein",
         sql={"": "LEVENSHTEIN({0}, {1})", "snowflake": "EDITDISTANCE({0}, {1})"},
         ibis=("Levenshtein",)),
    _str("regexp_extract", 206, "str.opaque", 1, "str", "regex_extract", call=False),
    _str("regexp_replace", 207, "str.opaque", 1, "str", "regex_replace", call=False),
    # Lowercase hex of the UTF-8 bytes (#50).
    _str("md5", 208, "str.opaque", 1, "str", expr=True, sql={"duckdb": "md5({0})"},
         lift=("MD5",)),
    _str("sha256", 209, "str.opaque", 1, "str", expr=True, sql={"duckdb": "sha256({0})"}),
)  # fmt: skip

#: The rows by name and by each alias.
BY_NAME: Mapping[str, Fn] = MappingProxyType(
    {n: f for f in FUNCTIONS for n in (f.name, *f.aliases)}
)


def area(name: str) -> tuple[Fn, ...]:
    """The rows of one area."""
    return tuple(f for f in FUNCTIONS if f.area == name)


def kinds(area_: str, un: bool) -> dict[str, FixedKind]:
    """The result kinds of an area's `Un` (or `Bin`) operations that are not
    booleans (`UN_KINDS`, `BIN_KINDS`)."""
    return {f.op: f.result for f in area(area_) if f.op and f.un == un and f.result != "bool"}


def sql(fn: Fn, dialect: str) -> str | No | None:
    """The row's SQL for `dialect`, its default, or `None`."""
    return fn.sql.get(dialect, fn.sql.get(""))
