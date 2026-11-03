### `avg` of integers follows the plan's output type

An `avg` of integers whose plan declares an integer result, as Substrait's
`avg` of `i64` does, is the exact mean truncated toward zero; a declared
`fp64` result is the mean as a double (#209). Other output types are refused.
