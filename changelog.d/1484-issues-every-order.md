### No runtime error on every order of the ties

The proof that a plan with no reported issue raises no runtime error now
covers every order of the ties the reference allows (`Rel.mayIssues_sound_all`,
#1484). Before, it covered one order, the reference evaluator's. An engine that
breaks a window's ties another way, as the routes for windows on Spark and
Snowflake allow, is covered too. The issues sverify reports are unchanged.
