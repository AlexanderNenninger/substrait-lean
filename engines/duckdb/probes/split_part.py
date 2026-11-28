"""DuckDB's `split_part(s, t, 1)` against the reference's `sverify_split_first`
(`Text.splitFirst`): the prefix of `s` before the leftmost `t`, `s` where `t` does not
occur or is empty, NULL for a NULL argument (ruling 286, ruling 290, #2586).

Run with the pinned DuckDB (2.0.1); prints the mismatches. The empty `t` is the expected
one: DuckDB splits into code points there."""

import duckdb

CASES = [
    ("héllo wörld", "ö"),  # non-ASCII, a multi-byte needle
    ("日本語日本", "本"),  # several occurrences: the leftmost
    ("abcabc", "b"),
    ("aaa", "aa"),  # overlapping occurrences
    ("éé", "é"),  # at the start
    ("a.b", "."),  # regex metacharacters are literal
    ("a%b", "%"),
    ("abc", "d"),  # absent
    ("ab", "abc"),  # longer than s
    ("", "a"),
    ("abc", "abc"),  # the whole string
    (None, "a"),
    ("abc", None),
    (None, None),
]

#: An empty `t`: DuckDB gives the first code point, `''` for an empty `s`.
EMPTY = [
    ("日本", ""),  # a first character of three bytes
    ("😀a", ""),  # of four bytes
    ("éx", ""),  # a base letter and a combining mark: two code points
    ("a", ""),
    ("", ""),
    (None, ""),
    ("abc", None),
]


def ref(s: str | None, t: str | None) -> str | None:
    if s is None or t is None:
        return None
    if t == "":
        return s
    i = s.find(t)
    return s if i < 0 else s[:i]


def duck_empty(s: str | None, t: str | None) -> str | None:
    """DuckDB's own value for an empty `t`: the first code point."""
    if s is None or t is None:
        return None
    return s[:1]


def main() -> None:
    con = duckdb.connect()
    print("duckdb", duckdb.__version__)

    def run(rows: list[tuple[str | None, str | None]]) -> list[str | None]:
        return [con.execute("SELECT split_part(?, ?, 1)", [s, t]).fetchone()[0] for s, t in rows]

    got = run(CASES)
    bad = [(c, g, ref(*c)) for c, g in zip(CASES, got, strict=True) if g != ref(*c)]
    print(f"{len(CASES)} rows against Text.splitFirst, mismatches:", bad)
    got = run(EMPTY)
    bad = [(c, g) for c, g in zip(EMPTY, got, strict=True) if g != duck_empty(*c)]
    print(f"{len(EMPTY)} rows of an empty t, the first code point, mismatches:", bad)


if __name__ == "__main__":
    main()
