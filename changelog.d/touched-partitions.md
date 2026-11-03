### Windows recompute only the partitions a batch touches

A node whose window functions share one `PARTITION BY` (with the partition
keys among its columns) recomputes only the partitions a batch touches, the
way an aggregate recomputes its touched groups. Lean proves it from
`windowEval_sharded` (`TouchedGroups.touched_window_sound`), for inputs
without ties on the partition and sort columns. Windows with different
partitions, or none, are still recomputed and diffed.
