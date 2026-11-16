### `sverify check` proves a decorated transform on its declared schemas

`@sv.transform(schemas={"orders": {"id": "int64", "amount": "int64"}})` gives a
transform its input schemas. `sverify check pipeline.py` then proves the contract
of a transform the file never applies, as `paid.check(orders=...)` does, with no
driver script. Without `schemas` the file's `unchecked` message names the new
exit (#1485, item 10).
