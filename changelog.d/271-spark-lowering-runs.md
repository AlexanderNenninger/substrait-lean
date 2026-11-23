### Spark runs its generated lowering

The translation to Spark writes double arithmetic, the elementary functions,
`floor`, `ceil`, `date_add` and the shifts from Spark's generated lowering
table, whose templates Lean proves
([#271](https://github.com/AlexanderNenninger/substrait-lean/issues/271)).
The hand-written model of what the writer computes (`Profile.sparkWritten`) is
gone. Spark's soundness now holds on the plan the table lowers, in two
branches: with its guards dropped for a plan without IEEE division, and with
every guard kept where Spark does not raise. More Spark routes are proved
where they were tested, among them integer division, `mod`, the string
matches and the date parts, and 15 rows of Spark's table cite a theorem where
they tracked #271.
