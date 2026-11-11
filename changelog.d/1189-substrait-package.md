### Substrait's profile, a Lean package of its own

`Profile.substrait`, the YAMLs' own looseness, moves into `engines/substrait/`,
the Lake package `sverify-substrait` with modules `Sverify.Substrait.*`, on the
core alone ([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)).
`verify(semantics="substrait")` is unchanged. With it, every engine's and
Substrait's Lean half is a package of its own. No theorem changed.
