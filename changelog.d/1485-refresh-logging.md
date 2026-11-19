### A refresh logs each node and each commit

A refresh writes one INFO line per node and one per commit to the `sverify` logger, in the words of `Refresh.summary()` ("paid: committed merge v5: +2 −0", or "already committed" where an overlapping refresh had committed the same state), so an orchestrator's task log shows what ran without printing the summary (#1485 item 25).
