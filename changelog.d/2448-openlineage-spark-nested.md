### `Upstream.schema` reads Spark's nested types as Spark means them

A `schema` facet's `struct<…>`, `array<…>` and `map<…>` now read Spark's type names inside them as Spark's, so `struct<a:int>` is `struct<a: int32>` and `timestamp` inside a struct is `timestamp('UTC')`, the types the Spark job wrote. A malformed nested type is `unknown`. Each type name is read once per process ([#2448](https://github.com/AlexanderNenninger/substrait-lean/issues/2448)).
