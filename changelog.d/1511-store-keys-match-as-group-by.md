### The state store matches double keys as `GROUP BY` does

An incremental refresh of a view grouped by, or `DISTINCT` over, a double column crashed with `ArrowInvalid: Cannot yet unify dictionaries with nulls` when a NaN key and a NULL key met, and kept `0.0` and `-0.0` apart, so a refresh after an append of `-0.0` gave a count of 1 where a recompute gives 2 (#1511). The store now encodes the combined key column once, with one zero and one NaN on its copy of the key (the stored values stay raw, D31), and NULL as its own key.

Sharded evaluation's split-key and `unique` checks compare doubles the same way (#1519): `0.0` on one shard and `-0.0` on another is now a split key `check_keys` refuses, where the sharded result had two groups for one.
