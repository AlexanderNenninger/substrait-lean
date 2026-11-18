"""The case-mapping tables of the tier-1 engines (D51): what `upper` and
`lower` give each Unicode scalar value on DuckDB, Polars and Spark, and where
they differ.

Run `python -m sverify_dev.case_tables [--write]` from `python/`: every
scalar value (U+0000 to U+10FFFF without the surrogates) goes through each
engine alone, as a one-character string. A value an engine maps to itself is
not recorded. `--write` stores the per-engine tables and the differences in
`engines/<engine>/probes/case-tables.json` and
`characterization/case-differences.json`. Context rules (the final sigma) are
not one-character facts and are probed apart (`CONTEXT`).
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[3]
SCALARS = [c for c in range(0x110000) if not 0xD800 <= c <= 0xDFFF]
#: Strings whose mapping depends on context, not on one character.
CONTEXT = ["ΣΑΣ", "ΑΣ", "Σ", "ΑΣΑ", "ΑΣ.", "İ", "ß", "ŉ", "ǰ", "ΐ", "ﬁ", "i̇"]


def duckdb_tables() -> dict[str, dict[str, str]]:
    import duckdb
    import pyarrow as pa

    con = duckdb.connect()
    t = pa.table({"s": [chr(c) for c in SCALARS]})
    con.register("t", t)
    rows = con.sql("SELECT s, upper(s), lower(s) FROM t").fetchall()
    return _diff(rows)


def polars_tables() -> dict[str, dict[str, str]]:
    import polars as pl

    df = pl.DataFrame({"s": [chr(c) for c in SCALARS]})
    out = df.select("s", u=pl.col("s").str.to_uppercase(), l=pl.col("s").str.to_lowercase())
    return _diff(out.rows())


def spark_tables() -> dict[str, dict[str, str]]:
    import pyarrow as pa

    from sverify_spark import engine

    spark = engine.session()
    t = pa.table({"s": [chr(c) for c in SCALARS]})
    spark.createDataFrame(t.to_pandas()).createOrReplaceTempView("t")
    rows = [tuple(r) for r in spark.sql("SELECT s, upper(s), lower(s) FROM t").collect()]
    return _diff(rows)


def _diff(rows: list[tuple[str, str, str]]) -> dict[str, dict[str, str]]:
    return {
        "upper": {f"{ord(s):04X}": u for s, u, _ in rows if u != s},
        "lower": {f"{ord(s):04X}": lo for s, _, lo in rows if lo != s},
    }


def context(engine: str) -> dict[str, list[str]]:
    """`upper` and `lower` of each `CONTEXT` string, one engine."""
    if engine == "duckdb":
        import duckdb

        con = duckdb.connect()
        return {
            s: list(con.execute("SELECT upper(?), lower(?)", [s, s]).fetchall()[0]) for s in CONTEXT
        }
    if engine == "polars":
        import polars as pl

        df = pl.DataFrame({"s": CONTEXT}).select(
            "s", u=pl.col("s").str.to_uppercase(), l=pl.col("s").str.to_lowercase()
        )
        return {s: [u, lo] for s, u, lo in df.rows()}
    from sverify_spark import engine as spark_engine

    spark = spark_engine.session()
    return {
        s: list(spark.sql("SELECT upper(?), lower(?)", args=[s, s]).collect()[0]) for s in CONTEXT
    }


def spark_setting(name: str, conf: str | None = None) -> None:
    """Spark's tables under another setting, as their difference from the
    default table, merged into `engines/spark/probes/case-tables-settings.json`
    under `name`. A conf is `key=value`; the JVM's locale is set from the
    outside (`PYSPARK_SUBMIT_ARGS="--driver-java-options '-Duser.language=tr'
    pyspark-shell"`) and recorded as it is."""
    import pyarrow as pa

    from sverify_spark import engine

    spark = engine.session()
    if conf:
        spark.conf.set(*conf.split("=", 1))
    spark.createDataFrame(
        pa.table({"s": [chr(c) for c in SCALARS]}).to_pandas()
    ).createOrReplaceTempView("t")
    got = _diff([tuple(r) for r in spark.sql("SELECT s, upper(s), lower(s) FROM t").collect()])
    base = json.loads((ROOT / "engines" / "spark" / "probes" / "case-tables.json").read_text())
    jvm: Any = spark.sparkContext._jvm
    assert jvm is not None
    entry: dict = {
        "locale": str(jvm.java.util.Locale.getDefault()),
        "conf": conf,
    }
    # ASCII letters in a string with one non-ASCII scalar leave the ASCII path.
    entry["context"] = {
        w: [str(x) for x in spark.sql("SELECT upper(?), lower(?)", args=[w, w]).collect()[0]]
        for w in ("Ié", "iÉ", "éI i", "İ", "ÌI")
    }
    for d in ("upper", "lower"):
        keys = sorted(set(got[d]) | set(base[d]), key=lambda h: int(h, 16))
        entry[d] = {
            h: [base[d].get(h, chr(int(h, 16))), got[d].get(h, chr(int(h, 16)))]
            for h in keys
            if base[d].get(h, chr(int(h, 16))) != got[d].get(h, chr(int(h, 16)))
        }
    print(
        name, entry["locale"], conf, {d: len(entry[d]) for d in ("upper", "lower")}, file=sys.stderr
    )
    path = ROOT / "engines" / "spark" / "probes" / "case-tables-settings.json"
    data = json.loads(path.read_text()) if path.exists() else {}
    data[name] = entry
    path.write_text(json.dumps(data, ensure_ascii=False, indent=0, sort_keys=True) + "\n")


def differences(tables: dict[str, dict[str, dict[str, str]]]) -> dict:
    """Per direction, the scalar values the engines map differently, with each
    engine's result (an engine that keeps the value gives itself)."""
    out: dict[str, dict] = {}
    for d in ("upper", "lower"):
        keys = set().union(*(t[d].keys() for t in tables.values()))
        diff = {}
        for k in sorted(keys, key=lambda h: int(h, 16)):
            ch = chr(int(k, 16))
            got = {e: t[d].get(k, ch) for e, t in tables.items()}
            if len(set(got.values())) > 1:
                diff[k] = got
        out[d] = {
            "scalars_mapped_by_some_engine": len(keys),
            "scalars_that_differ": len(diff),
            "differ": diff,
        }
    return out


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--write", action="store_true")
    ap.add_argument("--spark-setting", metavar="NAME", help="record Spark's tables under a setting")
    ap.add_argument("--conf", help="the setting's conf, key=value")
    ap.add_argument("--engines", default="", help="comma-separated; default: all")
    args = ap.parse_args(argv)
    if args.spark_setting:
        return spark_setting(args.spark_setting, args.conf)
    runners = {
        f.__name__.removesuffix("_tables"): f for f in (duckdb_tables, polars_tables, spark_tables)
    }
    tables = {e: runners[e]() for e in (args.engines.split(",") if args.engines else runners)}
    for e, t in tables.items():
        print(e, {d: len(m) for d, m in t.items()}, file=sys.stderr)
    diff = differences(tables)
    for d, v in diff.items():
        print(
            d,
            v["scalars_mapped_by_some_engine"],
            "mapped by some engine;",
            v["scalars_that_differ"],
            "differ",
            file=sys.stderr,
        )
    if not args.write:
        return
    for e, t in tables.items():
        p = ROOT / "engines" / e / "probes" / "case-tables.json"
        p.write_text(json.dumps({"context": context(e), **t}, ensure_ascii=False, indent=0) + "\n")
    p = ROOT / "characterization" / "case-differences.json"
    p.write_text(
        json.dumps({"engines": sorted(tables), **diff}, ensure_ascii=False, indent=0) + "\n"
    )


if __name__ == "__main__":
    main()
