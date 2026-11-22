"""`sverify.substrait_export`'s own readers (#750): Substrait's JSON types as
`Ty` and back, and the YAMLs' derivation expressions, which give each call
its return type."""

from __future__ import annotations

import pytest

from sverify import substrait_export as se
from sverify.substrait_export import ExportError, Ty

I64 = Ty("i64")

TYPES = [
    Ty("boolean"),
    Ty("i8"),
    I64,
    Ty("fp64"),
    Ty("string"),
    Ty("binary"),
    Ty("date"),
    Ty("uuid"),
    Ty("interval_year"),
    Ty("interval_day", (3,)),
    Ty("interval_compound"),
    Ty("decimal", (38, 10)),
    Ty("fixedchar", (4,)),
    Ty("varchar", (255,)),
    Ty("fixedbinary", (16,)),
    Ty("precision_time", (6,)),
    Ty("precision_timestamp", (9,)),
    Ty("precision_timestamp_tz", (3,)),
    Ty("list", (Ty("string"),)),
    Ty("struct", (I64, Ty("list", (Ty("decimal", (10, 2)),)))),
    Ty("struct", ()),
    Ty("map", (Ty("string"), Ty("map", (I64, Ty("fp32"))))),
]


@pytest.mark.parametrize("t", TYPES, ids=se._show)
def test_a_type_reads_back_as_itself(t: Ty) -> None:
    j = t.json()
    assert ty_nullable(j)
    assert se.ty_of(j) == t


def ty_nullable(j: dict) -> bool:
    [(_, body)] = j.items()
    return body["nullability"] == "NULLABILITY_NULLABLE"


def test_reading_a_type_fills_the_defaults_and_skips_the_variation() -> None:
    assert se.ty_of({"precisionTimestamp": {}}) == Ty("precision_timestamp", (6,))
    assert se.ty_of({"decimal": None}) == Ty("decimal", (0, 0))
    assert se.ty_of({"i32": {}, "typeVariationReference": 1}) == Ty("i32")
    # An interval of days without a precision is in microseconds.
    assert Ty("interval_day").json() == {
        "intervalDay": {"nullability": "NULLABILITY_NULLABLE", "precision": 6}
    }


def test_a_type_outside_the_table_is_refused() -> None:
    with pytest.raises(ExportError, match="cannot read the type userDefined"):
        se.ty_of({"userDefined": {"typeReference": 1}})
    with pytest.raises(ExportError, match="cannot write the type timestamp"):
        Ty("timestamp").json()


# -- the YAMLs' derivation expressions -----------------------------------------------


def ev(text: str, **env):
    return se._Expr(text, env).expr()


@pytest.mark.parametrize(
    ("text", "value"),
    [
        ("1 + 2 * 3", 7),
        ("(1 + 2) * 3", 9),
        ("7 - 2 - 1", 4),
        ("7 / 2", 3),
        ("-7 / 2", -3),
        ("-(2 + 3)", -5),
        ("min(4, 2, 9)", 2),
        ("MAX(4, min(2, 9))", 4),
        ("1 < 2", True),
        ("2 <= 2 && 3 >= 4", False),
        # #2452: `!` and `!=` used to read as names.
        ("1 == 2 || 2 != 3", True),
        ("!true", False),
        ("!(1 > 2)", True),
        ("1 > 2 ? 10 : 20", 20),
        # The conditional nests to the right.
        ("false ? 1 : true ? 2 : 3", 2),
        ("P1 + 1", 11),
    ],
)
def test_an_integer_expression(text, value) -> None:
    assert ev(text, P1=10) == value


def test_a_type_expression() -> None:
    assert ev("decimal<P1, S1 + 2>", P1=10, S1=2) == Ty("decimal", (10, 4))
    assert ev("list<any1>", any1=I64) == Ty("list", (I64,))
    assert ev("any1", any1=I64) == I64
    assert ev("str") == Ty("string") and ev("dec<1,0>") == Ty("decimal", (1, 0))
    assert se._parse_type("i64?") == I64
    assert se._parse_type("list?<i32?>") == Ty("list", (Ty("i32"),))


@pytest.mark.parametrize("text", ["1 +", "min(1, 2", "(1", "1 ? 2", "1 $ 2", ""])
def test_a_malformed_expression_is_refused(text) -> None:
    with pytest.raises(ExportError, match="cannot read the YAML expression"):
        ev(text)


#: The return of `multiply` of two decimals in Substrait's
#: `functions_arithmetic_decimal.yaml`.
DECIMAL_MULTIPLY = """
init_scale = S1 + S2
init_prec = P1 + P2 + 1
min_scale = min(init_scale, 6)
delta = init_prec - 38
prec = min(init_prec, 38)
scale_after_borrow = max(init_scale - delta, min_scale)
scale = init_prec > 38 ? scale_after_borrow : init_scale
DECIMAL<prec, scale>
"""


@pytest.mark.parametrize(
    ("p1", "s1", "p2", "s2", "out"),
    [
        (10, 2, 12, 3, (23, 5)),
        # Over 38 digits the scale is borrowed down, to at least 6.
        (38, 10, 38, 10, (38, 6)),
        (30, 2, 20, 1, (38, 3)),
    ],
)
def test_a_return_type_derivation(p1, s1, p2, s2, out) -> None:
    env = {"P1": p1, "S1": s1, "P2": p2, "S2": s2}
    assert se._return({"return": DECIMAL_MULTIPLY}, env) == Ty("decimal", out)


def test_a_return_that_is_no_type_or_an_unbound_variable_is_refused() -> None:
    with pytest.raises(ExportError, match="is not a type"):
        se._return({"return": "1 + 1"}, {})
    with pytest.raises(ExportError, match="any1 is not bound"):
        se._return({"return": "any1"}, {})
    assert se._return({"return": "list<any1>"}, {"any1": I64}) == Ty("list", (I64,))


def test_matching_binds_type_and_integer_variables() -> None:
    env: dict = {}
    dec = se._decl("decimal<P1,S1>")
    assert se._match(dec, Ty("decimal", (10, 2)), env) and env == {"P1": 10, "S1": 2}
    # A bound variable must match again.
    assert not se._match(se._decl("decimal<P1,S2>"), Ty("decimal", (12, 0)), env)
    env = {}
    assert se._match(se._decl("any1"), I64, env) and not se._match(se._decl("any1"), Ty("i32"), env)
    assert se._match(se._decl("list<any1>"), Ty("list", (I64,)), env)
    assert not se._match(se._decl("decimal<38,0>"), Ty("decimal", (10, 0)), {})
    assert not se._match(se._decl("i64"), Ty("i32"), {})
    assert not se._match(se._decl("u!geometry"), Ty("u!geometry"), {})
    assert not se._match(se._decl("map<any1,any2>"), Ty("map", (I64,)), {})
