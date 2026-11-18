### `run` and incremental views count the NULLs of a table the engine reads where it is

The check of `Report.run` and of an incremental view's first load counted a NULL in a non-null column only on an Arrow table. A `Resident` table or a `Scan` of files now gets the same count, on the engine, beside the range check of its integer columns: a NULL in a column the plan reads as non-null is refused, naming the column ([#1540](https://github.com/AlexanderNenninger/substrait-lean/issues/1540)).
