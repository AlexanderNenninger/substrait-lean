### Clearer contracts API and messages

- A `requires` key that names no input raises a `ValueError` naming the key,
  the inputs and a close match, where it raised a bare `KeyError`. A
  transformation with one input takes a plain list,
  `requires=[_.amount >= 0]` (#408).
- `@sv.transform(infer=False)` turns off bound inference, as on `sv.verify`.
  `strict=True` still works and warns that it is deprecated (#409).
- `sv.references("cust", to=customers.id)` names the referenced column with
  an Ibis column or a `(table, column)` pair. The positional form
  `references(col, table, other)` warns that it is deprecated (#412).
- `Connection.datafusion` is deprecated: the DataFusion session is an
  internal of the DataFusion engine (#413).
- Refusals give their reason in terms of the reference semantics, with the
  issue to follow and a workaround, and no longer cite DataFusion's
  behaviour (#410).
- An unproved condition says why in words: "it may be FALSE on some rows",
  and where it may be NULL, how to declare the column NOT NULL. This
  replaces "(it is TRUE or FALSE)"; `CheckedCondition.why` has the text
  (#176).
