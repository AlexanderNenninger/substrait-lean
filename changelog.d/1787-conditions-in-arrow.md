### Precondition checks count in Arrow

A run that checks its preconditions on an engine counted each condition's failing rows in a Python loop over every row. It now counts them with Arrow's compute kernels. On the catalogue's `fin-vwap` at 10⁶ rows, the preconditions take 10 ms where they took 121, and the checked run on DuckDB 98 ms where it took 212 (#1787).
