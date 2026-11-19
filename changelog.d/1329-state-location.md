### The state location takes a URI, and Spark sizes its consolidation

`SVERIFY_STATE_LOCATION` names where Polars and Spark write an incremental view's state: a directory, or a URI that the driver and every executor read and write. Spark's consolidation of a state sets its shuffle partitions for the state's size: 8.4 s at eight million rows where Spark's default of 200 partitions took 9.9 s. The interim Arrow store (`sverify._arrow_state`) is gone.
