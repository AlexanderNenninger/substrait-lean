### The SQL lift reads `list_append`, `list_prepend`, `flatten`, `list_first` and `list_last`

DuckDB SQL with `list_append(l, x)`, `list_prepend(x, l)` (and their `array_` names), `flatten(l)`, `list_first(l)` and `list_last(l)` lifts (part of [#327](https://github.com/AlexanderNenninger/substrait-lean/issues/327)). A NULL list is empty for an append and a prepend and a NULL value is an element, as in DuckDB; `list_first` and `list_last` are NULL for an empty or NULL list.
