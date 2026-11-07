### The checker stays within its memory

- `repeat(s, n)`, and Ibis's `rpad` and `lpad` built on it, are evaluated
  into one string. A count such as `10⁹` built a list of `n` pieces first and
  took the checker past 23 GB, which hung a 16 GB laptop; the same request now
  peaks at 3 to 6 GB, a few copies of its 1 to 2 GB result
  ([#1074](https://github.com/AlexanderNenninger/substrait-lean/issues/1074)).
- A checker request that takes `substrait-check` past 4 GB stops the checker
  and raises `CheckerMemoryError` (a `MemoryError`), and the next request
  starts a new checker. `SVERIFY_CHECKER_MEMORY_MB` sets the cap; 0 turns it
  off. The cap applies on Linux and macOS.
