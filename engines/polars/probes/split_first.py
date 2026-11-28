"""Polars's `s.str.split(t).list.first()` against the reference's `sverify_split_first`
(`Text.splitFirst`): the prefix of `s` before the leftmost `t`, `s` where `t` does not
occur or is empty, NULL for a NULL argument (ruling 286, K3, #2586).

Run with the pinned Polars (2.1.0) on both engines; prints the mismatches. The empty `t`
is the expected one: Polars splits into characters there."""

import polars as pl

CASES = [
    ("héllo wörld", "ö"),  # non-ASCII, a multi-byte needle
    ("日本語日本", "本"),  # several occurrences: the leftmost
    ("abcabc", "b"),
    ("aaa", "aa"),  # overlapping occurrences
    ("xyzxyz", "yz"),
    ("éé", "é"),  # at the start
    ("a.b", "."),  # regex metacharacters are literal
    ("a*b", "*"),
    ("abc", "d"),  # absent
    ("ab", "abc"),  # longer than s
    ("", "a"),
    ("abc", "abc"),  # the whole string
    (None, "a"),
    ("abc", None),
    (None, None),
    ("abc", ""),  # empty t: Polars splits into characters
    ("", ""),
]

#: An empty `t`: Polars's split gives the first code point (the unit `Text.substr`
#: counts), NULL for an empty `s` (`Lowering.splitExcepted`, ruling 290).
EMPTY = [
    ("日本", ""),  # a first character of three bytes
    ("😀a", ""),  # of four bytes
    ("\u00e9x", ""),  # the single code point U+00E9: comes back whole
    ("e\u0301x", ""),  # e followed by U+0301 (a combining acute): two code points
    ("a", ""),
    ("", ""),
    (None, ""),
    ("abc", None),
]


def polars_ref(s: str | None, t: str | None) -> str | None:
    """Polars's own split: the first code point for an empty `t`, NULL for an
    empty `s`, else `Text.splitFirst`."""
    if s is None or t is None:
        return None
    if t == "":
        return None if s == "" else s[:1]
    return ref(s, t)


def ref(s: str | None, t: str | None) -> str | None:
    if s is None or t is None:
        return None
    if t == "":
        return s
    i = s.find(t)
    return s if i < 0 else s[:i]


def main() -> None:
    df = pl.DataFrame(
        {"s": [s for s, _ in CASES], "t": [t for _, t in CASES]},
        schema={"s": pl.String, "t": pl.String},
    )
    print("polars", pl.__version__)
    for engine in ("in-memory", "streaming"):
        q = df.lazy().select(r=pl.col("s").str.split(pl.col("t")).list.first())
        got = q.collect(engine=engine)["r"].to_list()
        bad = [(c, g, ref(*c)) for c, g in zip(CASES, got, strict=True) if g != ref(*c)]
        print(engine, f"{len(CASES)} rows, mismatches:", bad)
        e = pl.DataFrame(
            {"s": [s for s, _ in EMPTY], "t": [t for _, t in EMPTY]},
            schema={"s": pl.String, "t": pl.String},
        )
        got = e.lazy().select(r=pl.col("s").str.split(pl.col("t")).list.first())
        got = got.collect(engine=engine)["r"].to_list()
        bad = [(c, g) for c, g in zip(EMPTY, got, strict=True) if g != polars_ref(*c)]
        print(engine, f"{len(EMPTY)} rows of an empty t, the first code point:", bad)


if __name__ == "__main__":
    main()
