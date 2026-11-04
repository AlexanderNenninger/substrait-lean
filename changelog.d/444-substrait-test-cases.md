### Substrait's own test cases run against `Profile.substrait`

The function test cases of `substrait-io/substrait` v0.106.0 run against
Substrait's profile on every pull request ([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444), step 4):
`python -m sverify_dev.substrait_cases`, with the ledger
`upstream/substrait-cases.json`. Of 1,317 cases, 631 agree, 625 are refused
and 61 disagree, each disagreement a wrong test case
([ST-13](https://github.com/AlexanderNenninger/substrait-lean/blob/main/upstream/bugs/ST-13.json), [ST-14](https://github.com/AlexanderNenninger/substrait-lean/blob/main/upstream/bugs/ST-14.json),
[ST-15](https://github.com/AlexanderNenninger/substrait-lean/blob/main/upstream/bugs/ST-15.json)).

The replay fixed four parser bugs. `negate` of an integer constant at the
least value of its type (`negate(-128::i8)`) now overflows by its `overflow`
option, where it folded to 128. A call with a list literal argument
(`cardinality([1, 2, 3])`) is read, where constant folding refused it.
`variance` and `std_dev` read their `distribution` as the leading enum
argument of their current signatures. A date minus an interval whose result
is typed as a timestamp of any precision is refused, as the date plus one is,
where it returned a date.
