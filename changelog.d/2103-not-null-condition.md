### A condition of `NOT NULL` takes the ELSE branch in the written SQL

A `CASE WHEN NOT CAST(NULL AS BOOLEAN) THEN a ELSE b END` in a written plan took the THEN branch, because the writer folded `NOT NULL` to `TRUE`. `NOT NULL` is NULL, and the CASE takes ELSE, as the reference and the engines' own SQL do.
