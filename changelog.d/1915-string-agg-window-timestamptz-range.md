### `group_concat` over a window, RANGE frames over `timestamptz`

`group_concat(sep=)` as a window function ([#1915](https://github.com/AlexanderNenninger/substrait-lean/issues/1915)) joins the frame's non-NULL strings in the window's order, on DuckDB. RANGE frames with interval offsets accept a timestamp with time zone as the sort key ([#1931](https://github.com/AlexanderNenninger/substrait-lean/issues/1931)).
