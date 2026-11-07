### A sink commits only on the table version it read

A Delta or Iceberg sink's write was conditional on the value of the node's
epoch, which another plan's commit (a deploy) can repeat: a write prepared
against the old plan's rows then landed on the new plan's (#964). The write
now goes through the table `contract()` read, so Delta's conflict check and
Iceberg's snapshot assertion fail it on any commit of the node since, and
Iceberg's retry compares the node's last snapshot, not its epoch. Each write
opens the table once less. Found by the TLA+ model of the refresh protocol
(#933).
