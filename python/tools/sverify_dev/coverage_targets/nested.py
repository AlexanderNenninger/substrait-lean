"""Lists, structs, UNNEST (`sql_lift/nested.py`)."""

from __future__ import annotations

from sverify_dev.coverage_targets._common import target

AREA = "nested"

TARGETS = [
    target(
        AREA,
        "list literals, indexing, UNNEST",
        "in",
        "catalogue unnest 1; Ibis lists",
        True,
        sql="SELECT xs[1], unnest(xs) FROM t",
    ),
    target(
        AREA,
        "len, list_contains, computed list elements",
        "in",
        "tag filters on list columns; replay (part of 1,724 list refusals)",
        False,
        sql="SELECT len(xs), list_contains(xs, 1), [qty, id] FROM t",
        issue=812,
    ),
    target(
        AREA,
        "lambdas and other list functions",
        "after",
        "replay ~1,500",
        False,
        sql="SELECT list_transform(xs, x -> x + 1) FROM t",
        ibis="unnest keep_empty",
        issue=348,
    ),
    target(
        AREA,
        "vector functions",
        "after",
        "embeddings pipelines; replay 53",
        False,
        sql="SELECT array_cosine_similarity([1.0, 2.0]::DOUBLE[2], [2.0, 1.0]::DOUBLE[2]) FROM t",
        issue=327,
    ),
    target(
        AREA,
        "structs and MAP",
        "after",
        "replay 1,229",
        False,
        sql="SELECT {'a': qty} FROM t",
        issue=349,
    ),
    target(
        AREA,
        "VARIANT, BLOB, geometry",
        "skipped",
        "replay 1,619",
        False,
        sql="SELECT CAST(name AS BLOB) FROM t",
        why="types outside the model",
    ),
]
