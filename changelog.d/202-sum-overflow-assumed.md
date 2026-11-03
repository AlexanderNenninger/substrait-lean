### An integer `SUM` that may overflow is an assumption checked on the data

`verify` no longer treats a possible integer `SUM` overflow as a warning. Where
the plan bounds a group's rows (a `VALUES` list, a `FETCH` count, an aggregate
without groups) and `requires` bounds the column, the overflow is ruled out.
Elsewhere sverify assumes each sum fits 64 bits, as it assumes inferred bounds
(#244), and lists it in `Report.assumed`; the SQL it writes checks it on the
data while the job runs. With `infer=False` it is an error that makes the
report unproved. Row bounds on tables (#219) will discharge it statically. A
window `SUM` or `AVG` whose frame may hold both `+inf` and `-inf` is now
reported as a domain error, as the grouped one is (#257).
