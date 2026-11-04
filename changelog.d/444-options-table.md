### The reference's options in one table

The options a plan may set, and the reference's choice at each, are now one
table in Lean (`SubstraitLean/Options.lean`, step 1a of
[#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)), and
the parser reads it. `substrait-check --options` prints it. Plans are read as
before, with one addition: `variance` and `std_dev` of integers accept
`rounding: TIE_TO_EVEN`, as `avg` of integers does.
