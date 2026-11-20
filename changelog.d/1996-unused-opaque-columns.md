### Pipelines ignore an unused map, struct or binary column

A pipeline over a table with a map, struct or binary column no step mentions refreshes, as `verify` does, with or without `requires`. The plans of the view's strategies (delta rules, state per group, touched groups, semi joins) read the columns the view and its conditions mention (#1996).
