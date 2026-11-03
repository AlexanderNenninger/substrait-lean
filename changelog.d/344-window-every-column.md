### Windows over every column are deterministic

A window partitioned by every column of its input, such as
`ROW_NUMBER() OVER (PARTITION BY` every column`)`, is now reported as
deterministic without a key. Rows tied in such a partition are equal, so how
an engine breaks the ties cannot change the result (`window_allColumns`,
proved). So `INTERSECT ALL` and `EXCEPT ALL`, which number the copies of each
row this way, are deterministic too, with or without keys on their inputs.
