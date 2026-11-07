### A faster contract check

The checker analyses each subplan once, bottom-up
([#903](https://github.com/AlexanderNenninger/substrait-lean/issues/903)).
Before, it walked a plan's inputs again at every filter and projection. On
the catalogue's contract requests `verify` spends about a fifth of the
checker time it did: the deepest join trees go from 1.0 s to 0.14 s, and a
chain of 40 projections from 0.34 s to 0.11 s. Results are unchanged:
`Rel.lane_eq` proves the one pass computes the same analysis.
