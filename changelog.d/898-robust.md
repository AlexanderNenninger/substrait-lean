### The checker says what a postcondition depends on

The checker now reports, for each postcondition, the components of an
observation its value depends on, from the columns it reads (#898).
`CheckedCondition.ignores` reads them, and Lean proves that a condition
depending on none of the components the observation ignores holds on every
result equal up to the observation (`Expr.robust_of_depends`). A comparison
narrowed by a tolerance is proved the same way (`Expr.narrow_sound`).
