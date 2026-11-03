### A source with `schema=` proves contracts without reading

`Source.schema()` returns the schema given as `schema=` without reading the
source, so building a node proves the transform's contract whatever the state
of the source, and the first read happens at the first refresh (#376).
