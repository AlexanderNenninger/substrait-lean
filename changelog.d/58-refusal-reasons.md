### Refusals say why

`random()`, `uuid()`, `now()`, `today()`, `typeof()`, `ibis.param` and
`try_cast` were refused with "X is not supported". The message now gives
the reason and what to do instead, for example to pass the time in as a
column or constant (#58).
