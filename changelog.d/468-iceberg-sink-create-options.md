### An Iceberg sink creates its table where and how you say

`IcebergSink` takes `location=`, `partition_by=` and `properties=`, and its
first write creates the table with them in one commit. A catalog without a
default location, such as Unity Catalog's Iceberg REST catalog on a schema
without a managed storage root, can now hold a sink, and a sink can create a
partitioned table itself (`partition_by=[("ts", "day"), ("host",
"identity")]`), which then takes each change in the partitions it touches
([#466](https://github.com/AlexanderNenninger/substrait-lean/issues/466)).
They apply only to a table the sink creates: a sink on an existing table
that differs from them warns once and leaves the table as it is
([#468](https://github.com/AlexanderNenninger/substrait-lean/issues/468)).
