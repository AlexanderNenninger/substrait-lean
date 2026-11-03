### `substring` out of range is an error, and strings have fewer than 2³² characters

- The size hypothesis for strings is now 2³² characters (it was 2⁶²); relations
  a window reads keep 2⁶² rows (#336).
- `substring` with an offset outside `[-2³², 2³²)` or a length of `2³²` or more
  is an error in the reference semantics, as DuckDB raises. `verify` reports it
  as a domain error unless the offset's bounds rule it out, for columns and
  constants alike, and the written plans raise there on DuckDB and Polars. The
  lift no longer refuses such constants.
