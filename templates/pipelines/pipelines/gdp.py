"""GDP and its main components for ten EU countries and the EU, from
Eurostat's `nama_10_gdp`, in million euros at current prices and in chain
linked volumes (2010).

Two tables:

* `gdp`: one row per country, unit, national accounts item and year, with
  the value and Eurostat's flag (`p` provisional, `b` break in series, …).
* `trade_openness`: exports plus imports per country and year, at current
  prices, beside GDP.

Check it with `sverify check pipelines/gdp.py`; refresh it with
`sverify refresh pipelines/gdp.py:trade_openness_table`.
"""

import sverify as sv
from ibis import _

from _eurostat import eurostat
from _lake import sink

KEY = ("geo", "unit", "na_item", "time")
FLAGS = ["p", "b", "e", "d", "u", "c", "n", "s"]

nama_10_gdp = eurostat(
    "nama_10_gdp",
    "A.CP_MEUR+CLV10_MEUR.B1GQ+P3+P5G+P6+P7.DE+FR+IT+ES+NL+PL+SE+AT+BE+EU27_2020",
    dimensions=["freq", "unit", "na_item", "geo"],
    start="2015",
)


@sv.transform(
    requires={
        "nama_10_gdp": [
            sv.unique(*KEY),
            _.geo.notnull(),
            _.unit.notnull(),
            _.na_item.notnull(),
            _.time.notnull(),
            _.value.isnull() | ((_.value >= 0) & (_.value < 1e9)),
            _.flag.isnull() | _.flag.isin(FLAGS),
        ]
    },
    ensures=[
        sv.unique(*KEY),
        _.value.notnull(),
        _.value >= 0,
        _.value < 1e9,
        _.flag.isnull() | _.flag.isin(FLAGS),
    ],
)
def gdp(nama_10_gdp):
    """Observed values only: Eurostat marks a missing value with an empty
    cell and a flag."""
    t = nama_10_gdp
    return t.filter(t.value.notnull()).select(*KEY, "value", "flag")


@sv.transform(
    ensures=[sv.unique("geo", "time"), _.gdp > 0, _.trade >= 0],
)
def trade_openness(gdp):
    """Exports (P6) plus imports (P7) of goods and services beside GDP
    (B1GQ), at current prices."""
    cp = gdp.filter(gdp.unit == "CP_MEUR")
    total = cp.filter(cp.na_item == "B1GQ").select("geo", "time", gdp="value")
    exports = cp.filter(cp.na_item == "P6").select("geo", "time", exports="value")
    imports = cp.filter(cp.na_item == "P7").select("geo", "time", imports="value")
    j = total.join(exports, ["geo", "time"]).join(imports, ["geo", "time"])
    return j.filter(j.gdp > 0).select("geo", "time", "gdp", trade=j.exports + j.imports)


gdp_table = nama_10_gdp.pipe(gdp).write(sink("gdp"))
trade_openness_table = gdp_table.pipe(trade_openness).write(sink("trade_openness"))
