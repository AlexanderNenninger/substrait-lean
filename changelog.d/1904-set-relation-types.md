### Substrait export: a set relation whose inputs differ in type is refused

`to_substrait` refuses a plan whose set relation has inputs of different column types, decimals of two precisions for example, which Substrait does not allow. It used to write a plan the Substrait validator rejects (TPC-DS q51). `report.to_sql(dialect)` writes the plan for an engine.
