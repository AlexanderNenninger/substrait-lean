# Vendored ibis-substrait

Translates Ibis expressions to Substrait plans. Vendored from
[ibis-project/ibis-substrait](https://github.com/ibis-project/ibis-substrait)
at commit `2cf1e07` (after v4.0.1), under the
Apache License 2.0 (`LICENSE` in this directory). Upstream targets Ibis 9 and
is no longer developed; this copy is ported to the Ibis version `sverify`
pins, trimmed to the operations the Lean model covers, and fixed where its
output differed from Ibis's semantics. Every file carries a notice of our
changes, and the git history records them.
