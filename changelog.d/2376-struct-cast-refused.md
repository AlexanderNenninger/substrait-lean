### A cast to a type that holds a struct is refused

A cast whose target is a struct, or a list of structs, is refused: the model carries no field names, so a target with the same field kinds in another order read as the identity, where DuckDB and Polars pair a struct cast's fields by name and Spark by position. The proper pairing follows ([#2376](https://github.com/AlexanderNenninger/substrait-lean/issues/2376)).
