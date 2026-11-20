### A message names a computed column the output drops

An overflow over a column that an earlier step computes and the output never keeps
reads `amount * 2 * 3 + 1`, where it printed Lean's `(($1 * 3) + 1)`.
