### The checker proves postconditions over the transformation itself

`substrait-check --contract` builds each postcondition's plan from the
request's transformation and refuses a postcondition plan that selects from
anything else, so `check_proved_sound` speaks of the transformation the report
is about (#1484, finding 2). Two producers sent other plans: an Ibis condition
over a transformation ending in a join's `select` (Ibis merged the two), and
`Report.from_substrait`, whose exported plan carries shims its postconditions'
plans lacked. Both now send the condition over the transformation.
