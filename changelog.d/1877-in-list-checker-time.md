### Long IN lists check in milliseconds

The checker's time for `x IN (...)` grew exponentially with the list's length:
2.5 s for 11 literals, minutes for 13. Checking each `OR`'s right operand
re-analysed the left one several times, and an `IN` list nests its `OR`s on
the left. A list of 50 literals now checks in under 0.1 s
([#1877](https://github.com/AlexanderNenninger/substrait-lean/issues/1877)).
