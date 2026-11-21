"""float32 (REAL) columns and constants (#1908): sverify reads them, compares,
orders, groups and passes them through, and casts them to double; arithmetic on
them rounds to 32 bits, which the model does not have yet (#417), so it is
refused with the step named. A run returns float32 where `Report.output` says
float32, on every engine."""

import math
import struct

import duckdb
import ibis
import pyarrow as pa
import pytest
from ibis import _

import sverify as sv
from sverify._unsupported import Unsupported

ENGINES = ["duckdb", "polars", "spark"]

T = ibis.table({"f": "float32", "d": "float64", "i": "int64"}, name="t")
DATA = pa.table(
    {
        "f": pa.array([0.3, 0.1, None, -2.7, 1e30], pa.float32()),
        "d": [0.1, 0.2, 0.3, 0.4, 0.5],
        "i": [1, 2, 3, 4, 5],
    }
)
F32 = [0.30000001192092896, 0.10000000149011612, None, -2.700000047683716, 1.0000000150474662e30]

#: What each query gives on DATA, and the type of its column `x`.
READS = {
    "passed through": (lambda t: t.select(x=t.f), F32, pa.float32()),
    "compared": (
        lambda t: t.filter(t.f > ibis.literal(0.1, "float32")).select(x=t.f),
        [F32[0], F32[4]],
        pa.float32(),
    ),
    "compared with a double": (
        lambda t: t.filter(t.f > 0.1).select(x=t.f),
        [F32[0], F32[1], F32[4]],
        pa.float32(),
    ),
    "ordered": (
        lambda t: t.order_by("f").select(x=t.f),
        [F32[3], F32[1], F32[0], F32[4], None],
        pa.float32(),
    ),
    "cast to double": (lambda t: t.select(x=t.f.cast("float64")), F32, pa.float64()),
    "max": (lambda t: t.aggregate(x=t.f.max()), [F32[4]], pa.float32()),
    "is null": (
        lambda t: t.select(x=t.f.isnull()),
        [False, False, True, False, False],
        pa.bool_(),
    ),
    "a constant": (
        lambda t: t.select(x=ibis.literal(0.1, "float32")).limit(1),
        [F32[1]],
        pa.float32(),
    ),
}


def run(report, engine):
    if engine == "spark":
        from spark_session import session

        session()  # skips without pyspark or a JVM
    con = sv.connect()
    con.put("t", DATA)
    return report.run(con, engine).column("x")


@pytest.mark.parametrize("engine", ENGINES)
@pytest.mark.parametrize("name", list(READS))
def test_float32_is_read(name, engine):
    build, expected, ty = READS[name]
    report = sv.verify(build(T))
    assert report.issues == [], report.issues
    got = run(report, engine)
    assert got.to_pylist() == expected
    assert got.type == ty


#: Every use whose result depends on the width (ruling 186 P5), and the words
#: its refusal has. (Ibis casts `corr`'s and `cov`'s arguments to double
#: itself, which widens exactly, so those read.)
WIDTH_DEPENDENT = {
    "arithmetic": (lambda t: t.select(x=t.f + 1), r"FLOAT \(fp32\)"),
    "negation": (lambda t: t.select(x=-t.f), r"FLOAT \(fp32\)"),
    "sum": (lambda t: t.aggregate(x=t.f.sum()), r"FLOAT \(fp32\)"),
    "mean": (lambda t: t.aggregate(x=t.f.mean()), r"FLOAT \(fp32\)"),
    "variance": (lambda t: t.aggregate(x=t.f.var()), r"FLOAT \(fp32\)"),
    "std": (lambda t: t.aggregate(x=t.f.std()), r"FLOAT \(fp32\)"),
    "median": (lambda t: t.aggregate(x=t.f.median()), r"FLOAT \(fp32\)"),
    "round": (lambda t: t.select(x=t.f.round(2)), r"FLOAT \(fp32\)"),
    "cast to a string": (lambda t: t.select(x=t.f.cast("string")), "cast"),
    "cast to a decimal": (lambda t: t.select(x=t.f.cast("decimal(10, 2)")), r"FLOAT \(fp32\)"),
    "cast to float32": (lambda t: t.select(x=t.d.cast("float32")), r"FLOAT \(fp32\)"),
}


@pytest.mark.parametrize("name", list(WIDTH_DEPENDENT))
def test_a_width_dependent_use_of_float32_is_refused(name):
    build, words = WIDTH_DEPENDENT[name]
    with pytest.raises(Unsupported, match=words):
        sv.verify(build(T))


#: Constants each engine must hold bit for bit (ruling 186 P4).
CONSTANTS = [
    0.1,
    16777216.0,
    3.4028234663852886e38,  # the largest single
    1.401298464324817e-45,  # the smallest subnormal
    123.456789,  # nine digits
    -0.0,
    math.nan,
    math.inf,
]


def single_bits(x: float) -> int:
    return struct.unpack("<I", struct.pack("<f", x))[0]


@pytest.mark.parametrize("engine", ENGINES)
@pytest.mark.parametrize("v", CONSTANTS, ids=repr)
def test_a_float32_constant_is_exact_on_every_engine(engine, v):
    report = sv.verify(T.select(x=ibis.literal(v, "float32")).limit(1))
    assert report.issues == [], report.issues
    got = run(report, engine)
    assert got.type == pa.float32()
    (x,) = got.to_pylist()
    if math.isnan(v):
        assert math.isnan(x)
    else:
        assert single_bits(x) == single_bits(v)


def test_preconditions_on_float32_are_read():
    """The condition sverify infers for `sqrt(f)` is SQL on a float32 column,
    which the SQL lift reads."""
    report = sv.verify(T.select(x=T.f.sqrt()))
    assert report.issues == [], report.issues
    assert report.requires == {"t": ["(_.f >= 0.0)"]}


TABLES = {"t": {"f": "float32", "i": "int64"}}


@pytest.mark.parametrize(
    "sql",
    [
        # DuckDB brings a REAL and a decimal to a REAL: `0.3::REAL = 0.3`.
        "SELECT f FROM t WHERE f = 0.3",
        "SELECT f FROM t WHERE f >= 0.1",
        "SELECT f FROM t WHERE f > 1",
        # A REAL and a DOUBLE to a DOUBLE: `0.3::REAL <> 0.3::DOUBLE`.
        "SELECT f FROM t WHERE f = 0.3::DOUBLE",
        "SELECT max(f) AS f FROM t",
    ],
)
def test_sql_on_float32_is_duckdbs(sql):
    report = sv.verify(sql, tables=TABLES)
    assert report.issues == [], report.issues
    native = duckdb.connect()
    native.register("t", DATA)
    expected = [row[0] for row in native.execute(sql).fetchall()]
    con = sv.connect()
    con.put("t", DATA)
    assert report.run(con, "duckdb").column("f").to_pylist() == expected


def test_sql_comparing_float32_with_an_integer_column_is_refused():
    """DuckDB casts the integer to REAL, which rounds (#417)."""
    with pytest.raises(Unsupported, match=r"FLOAT \(fp32\)"):
        sv.verify("SELECT f FROM t WHERE f > i", tables=TABLES)


@pytest.mark.parametrize(
    "sql",
    [
        # Past 2^53 an integer goes through a double first: two roundings.
        "SELECT f FROM t WHERE f = 9007199254740993",
        # Just above the midpoint between the singles 1 and 1 + 2^-23: its nearest
        # double is the midpoint, which rounds to 1, where DuckDB gives 1 + 2^-23.
        "SELECT f FROM t WHERE f = 1.00000005960464477539062500001",
    ],
)
def test_a_constant_that_would_round_twice_is_refused(sql):
    """Ruling 186 P3: the folded constant is DuckDB's, rounded once."""
    with pytest.raises(Unsupported, match="round twice"):
        sv.verify(sql, tables=TABLES)


def test_an_integer_constant_rounds_to_float32_as_duckdb():
    """`16777217` next to a REAL is the REAL 16777216 (duckdb-coerce-real)."""
    data = pa.table({"f": pa.array([16777216.0], pa.float32()), "i": [1]})
    report = sv.verify("SELECT f FROM t WHERE f = 16777217", tables=TABLES)
    con = sv.connect()
    con.put("t", data)
    assert report.run(con, "duckdb").column("f").to_pylist() == [16777216.0]


@pytest.mark.parametrize("engine", ENGINES)
def test_a_negative_zero_constant_meets_zero_at_a_key(engine):
    """A `-0.0` constant stays `-0.0` (ruling 186 P4, D31), and a key compares
    it equal to `0.0`: one group, and every row joins."""
    zero = ibis.literal(0.0)
    flip = ibis.ifelse(T.i % 2 == 0, ibis.literal(-0.0), zero)
    grouped = sv.verify(T.mutate(k=flip).group_by("k").agg(x=T.i.count()))
    assert grouped.issues == [], grouped.issues
    assert run(grouped, engine).to_pylist() == [5]
    left = T.select(k=ibis.literal(-0.0), a=T.i)
    right = T.select(k=zero, b=T.i)
    joined = sv.verify(left.join(right, "k").select(x=_.a))
    assert joined.issues == [], joined.issues
    assert len(run(joined, engine)) == 25


@pytest.mark.parametrize("engine", ENGINES)
def test_a_float32_cast_to_an_integer_truncates_on_every_engine(engine):
    """The reference truncates (R9), and the written plan does too, where
    DuckDB's own cast rounds 0.55 to 1 (#2152)."""
    t = ibis.table({"f": "!float32"}, name="t")
    report = sv.verify(t.select(x=t.f.cast("int8")), requires=["f > -100 AND f < 100"])
    assert report.verdict == "proved", report.issues
    if engine == "spark":
        from spark_session import session

        session()
    con = sv.connect()
    con.put("t", pa.table({"f": pa.array([0.55, 1.5, -1.5, 99.9], pa.float32())}))
    assert report.run(con, engine).column("x").to_pylist() == [0, 1, -1, 99]
