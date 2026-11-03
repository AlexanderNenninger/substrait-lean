### Overflow hints name the bound to add

A report's overflow hints now name the column and propose bounds (#379),
in `Report.hints` and as `hint:` lines. A truncated or binned timestamp or
date gets a lower and an upper bound on its column, such as
`_.ts >= datetime(2000, 1, 1)` and `_.ts < datetime(2100, 1, 1)`, which clear
the overflow. An integer `SUM` that is checked while the job runs gets the
range Lean knows for the column it adds up and the largest group whose sum
then fits 64 bits, or, for an unbounded column, a bound to add and the group
size it allows. No contract can state a group's size, so the hint says so.
The general hint stays for overflows the new ones do not cover.
