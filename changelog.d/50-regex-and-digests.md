### Regular expressions and digests

Ibis's `re_extract` and `re_replace` (DuckDB's `regexp_extract` and
`regexp_replace`, with or without the flag `'g'`) and `hexdigest('md5')` and
`hexdigest('sha256')` are verified on DuckDB (#50). Patterns must be
constants in the subset `Text.simpleRegex` accepts, which now includes
non-capturing groups `(?:…)`. Proofs treat these functions as black boxes,
but Lean evaluates them: regular expressions with RE2's leftmost-first
matching and DuckDB's edge cases (`''` where nothing matches, `\1` in the
replacement, empty matches), and the digests as lowercase hex. So
ClickBench Q28 and dbt's surrogate key now verify. DuckDB's `hash()` and
Ibis's URL parts (`host()`, …) are refused, and the other engines refuse
all of these until #271. The DuckDB SQL of `\b` in a pattern now raises on
non-ASCII text, as `\d`, `\w` and `\s` already did, since RE2 and Rust
disagree there.
