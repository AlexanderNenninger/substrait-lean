### The core's rounding is proved to meet the float bounds' standard model

The bounds in `float-bounds/` are proved for any rounding that meets the
standard model, and the core rounds with integer codes. A new library,
`float-bounds/FloatBridge`, proves that the core's rounding is such a model
and agrees with the codes on every value the core rounds
([#1196](https://github.com/AlexanderNenninger/substrait-lean/issues/1196)),
one step of the link between the two that was trusted.
