### A transformation with an `ibis.param` says how to bind it

A contracted transformation whose body uses an `ibis.param` failed with a
bare `KeyError` from Ibis. It now raises a `TypeError` naming the parameter:
transformations don't bind parameters yet (#354), so prove the expression
with `sv.verify(expr, params={param: value})` or write the values as
`ibis.literal(...)` (#440).
