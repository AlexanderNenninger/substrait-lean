A `BETWEEN` of a `BETWEEN` in a SQL query lifts to a plan whose size is linear in the nesting depth. Each level doubled the plan, so thirty levels never finished.
