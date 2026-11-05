"""Strings, LIKE, regexes, digests (`sql_lift/strings.py`)."""

from __future__ import annotations

from sverify_dev.coverage_targets._common import target

AREA = "strings"

TARGETS = [
    target(
        AREA,
        "basic string functions",
        "in",
        "catalogue: string_basic 3, like 9; dbt cross-db macros",
        True,
        sql="SELECT trim(name), upper(name), length(name), left(name, 2), substring(name, 2, 3), "
        "strpos(name, 'a'), starts_with(name, 'a'), replace(name, 'a', 'b'), "
        "name || '-' || name, name ILIKE 'A%' FROM t",
    ),
    target(
        AREA,
        "md5 and sha256",
        "in",
        "catalogue hash 1; dbt surrogate keys",
        True,
        sql="SELECT md5(CAST(id AS VARCHAR) || '-' || coalesce(name, '')), sha256(name) FROM t",
    ),
    target(
        AREA,
        "regexp_matches, regexp_extract, regexp_replace",
        "in",
        "catalogue regex_replace (ClickBench q28, through Ibis); Eurostat flags; Ibis re_* verify",
        True,
        sql="SELECT regexp_matches(name, '^a'), regexp_extract(name, '([0-9]+)', 1), "
        "regexp_replace(name, ':', '') FROM t",
        issue=808,
    ),
    target(
        AREA,
        "split_part, string_split and concat_ws",
        "in",
        "dbt.split_part; concat_ws surrogate keys; Eurostat",
        True,
        sql="SELECT split_part(name, ' ', 1), concat_ws('-', name, region) "
        "FROM t JOIN u USING (name)",
        issue=808,
    ),
    target(
        AREA,
        "right, lpad and rpad",
        "in",
        "dbt.right; Ibis right, lpad, rpad verify",
        True,
        sql="SELECT right(name, 2), lpad(name, 5, '0') FROM t",
        issue=808,
    ),
    target(
        AREA,
        "hash()",
        "skipped",
        "Ibis hash",
        False,
        sql="SELECT hash(name) FROM t",
        ibis="hash",
        why="the engine's own hash, which changes between versions; md5 or sha256 verify",
    ),
    target(
        AREA,
        "JSON",
        "skipped",
        "catalogue json (none verified); event payloads",
        False,
        sql="SELECT json_extract_string(name, '$.a') FROM t",
        why="no JSON type in the model; flatten JSON at the source into typed columns",
    ),
    target(
        AREA,
        "translate, URL parts, LIKE ESCAPE, GLOB",
        "after",
        "Ibis translate, host; replay ~150",
        False,
        sql="SELECT translate(name, 'ab', 'cd') FROM t",
        ibis="translate",
        issue=328,
    ),
]
