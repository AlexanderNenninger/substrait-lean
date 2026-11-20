### ODCS: a fractional row cap reads

`odcs.read` reads a `rowCount` cap such as `mustBeLessOrEqualTo: 2.5` as `max_rows(2)`, where it used to skip it as a lower bound.
