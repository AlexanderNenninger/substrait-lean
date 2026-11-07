### A sink rewrites rows another application changed

When another application changed rows of a Delta or Iceberg sink after the
node's last commit, a restarted job already declined to resume from them,
but the write did not notice: it skipped the state as committed, keeping the
other rows under the node's record, or wrote its next change on top of them
(#966). A refresh now replaces the rows in that case; maintenance that keeps
the rows (compaction, vacuum, table properties) changes nothing. Found by the
TLA+ model of the refresh protocol (#933).
