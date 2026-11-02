### `ibis.param` values for `verify`

`sverify.verify` takes `params={param: value}`, as Ibis's
`execute(params=...)` does, and binds each `ibis.param` to its value before
compiling (#58). The report is about the expression with those values, and
says so: `Report.params` lists them, and the report notes that its proofs
hold for those values only. A parameter left unbound is still refused, now
with a reason that says to pass `params`.
