### Spark keeps a pipeline view's state in Parquet files it writes and reads

On Spark, an incremental view's state is a generation of Parquet files that Spark writes and reads, where it was an Arrow table in the Python process (#1329, #173). Merging a change into the state runs the merge plan on Spark, and ANSI mode raises a weight sum that leaves 64 bits. The driver's peak for four refreshes of a filter view over two million rows is 541 MB where it was 715 MB, and 1147 MB where it was 1840 MB over eight million.
