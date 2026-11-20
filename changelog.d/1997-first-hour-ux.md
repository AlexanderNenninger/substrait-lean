### Clearer first hour: run-time checks, constants, quarantine, refresh summary

- A report that holds with checks reads "proved with checks: 1 run-time check" (it said "1 assumption"), matching the `while it runs:` lines below it.
- Double constants print as Python writes them: `amount * 3.0 + 1.0`, not `amount * 3.000000 + 1.000000`, and `value * 3.0000001` keeps its digits.
- `sverify check`'s "Not proved" lines say each postcondition in words (`total < 5: it may be FALSE on some rows`), as its guarantees do.
- `sverify check` lists a node's quarantine table among its credentials only where a precondition sets rows aside (`on_violation="quarantine"`).
- `Refresh.summary()` is one line per node for every refresh: a first refresh reads "paid: computed, requires checked on data, created v1: +2 −0", and what is notable (a recompute, a schema change) leads the line; `str()` keeps the full entry.

([#1997](https://github.com/AlexanderNenninger/substrait-lean/issues/1997))
