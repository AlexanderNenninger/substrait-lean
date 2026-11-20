### Added: `strings="casefold"` and `strings="ascii"`

`sv.equivalent(strings=...)` takes two more levels: `"casefold"` (Unicode's canonical caseless match) and `"ascii"` (the compatibility caseless match, keeping the code points below U+0080, so `søren` equals `sren`). The default stays `"exact"`. The levels are the ones Lean's `StringObs` has; [what they hide](docs/core-semantics.md#what-the-string-levels-hide) ([#1285](https://github.com/AlexanderNenninger/substrait-lean/issues/1285)).
