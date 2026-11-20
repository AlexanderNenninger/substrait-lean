### Qualified table names in `tables`

`verify`'s `tables` keys may be qualified (`"shop.main.orders"`, `"main.orders"`). A query's reference matches a key as DuckDB resolves names (catalog, schema, table, with the defaults `memory` and `main`), and the same table name in two schemas stays two inputs. A name outside the inputs is refused with the key to add (#706).
