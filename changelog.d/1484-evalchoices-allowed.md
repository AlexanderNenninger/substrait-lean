### The oracle of `allows_rows` has a theorem for most plans

`Rel.evalChoices_allowed` (`SubstraitLean/ChoicesSound.lean`) proves that a result `allows_rows` accepts is one the reference allows (`Rel.OrderAllowed`), for plans without an aggregate, a `FETCH` or a window. The other plans stay tested; the next changes prove them one at a time (#1484).
