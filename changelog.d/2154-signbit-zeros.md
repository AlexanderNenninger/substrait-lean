### `signbit` at zero, and black-box refusals in a long-lived checker

Lean now evaluates DuckDB's `signbit` at `+0.0` and `-0.0` (FALSE and TRUE), and refuses it at NaN only. A call Lean does not evaluate (`signbit` of NaN, `string_split('', '')`) is refused every time. Before, the second such call in one checker process read NULL and was reported as a broken law ([#2154](https://github.com/AlexanderNenninger/substrait-lean/issues/2154)).
