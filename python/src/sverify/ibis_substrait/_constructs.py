"""The name a user calls an Ibis operation by, for `UnsupportedError.construct` (#700).

An Ibis operation class is named for what it computes (`ArrayCollect`); the user
writes `collect`. A refusal of an operation not listed here sets no construct.
"""

from typing import Any

#: Ibis aggregate and window operation classes, by the method the user calls.
OP_METHODS = {
    "All": "all",
    "Any": "any",
    "ApproxCountDistinct": "approx_nunique",
    "ApproxMedian": "approx_median",
    "Arbitrary": "arbitrary",
    "ArgMax": "argmax",
    "ArgMin": "argmin",
    "ArrayCollect": "collect",
    "BitAnd": "bit_and",
    "BitOr": "bit_or",
    "BitXor": "bit_xor",
    "Correlation": "corr",
    "DateFromYMD": "date",
    "DateNow": "today",
    "Count": "count",
    "CountDistinct": "nunique",
    "CountDistinctStar": "nunique",
    "CountStar": "count",
    "Covariance": "cov",
    "CumeDist": "cume_dist",
    "DenseRank": "dense_rank",
    "First": "first",
    "GroupConcat": "group_concat",
    "Lag": "lag",
    "Last": "last",
    "Lead": "lead",
    "Max": "max",
    "Mean": "mean",
    "Median": "median",
    "Min": "min",
    "Mode": "mode",
    "MultiQuantile": "quantile",
    "NTile": "ntile",
    "NthValue": "nth",
    "PercentRank": "percent_rank",
    "Quantile": "quantile",
    "MinRank": "rank",
    "RowNumber": "row_number",
    "StandardDev": "std",
    "StringToDate": "to_date",
    "StringToTimestamp": "to_timestamp",
    "Sum": "sum",
    "TimeFromHMS": "time",
    "TimestampFromYMDHMS": "timestamp",
    "TimestampNow": "now",
    "Variance": "var",
}


def class_construct(name: str) -> str | None:
    """`function <method>` for the Ibis operation class `name` if the user calls it by a
    method, else None."""
    method = OP_METHODS.get(name)
    return None if method is None else f"function {method}"


def op_construct(op: Any) -> str | None:
    """`class_construct` of an operation."""
    return class_construct(type(op).__name__)
