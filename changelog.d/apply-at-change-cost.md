### A batch updates a source table at the cost of the change

Applying a batch to a pipeline's copy of a source table no longer groups the
whole table. A batch of inserts appends them, and deletes touch only the rows
equal to a deleted row. On the metrics benchmark (2.4 million rows, one minute
of samples per refresh) this was about 200 ms of a 365 ms refresh.
