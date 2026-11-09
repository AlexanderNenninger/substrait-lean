### The analysis, a Lean package of its own

What `verify` proves of a plan under the core, the contract analysis, keys,
issues, sharding and guard elimination, moves into `analysis/`, the Lake
package `sverify-analysis` with modules `Sverify.Analysis.*`
([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)).
It builds on the core alone, with no engine in it, and CI checks that it
does. No theorem changed.
