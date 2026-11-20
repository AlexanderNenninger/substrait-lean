### Status names each node's mode and why it recomputes (breaking: `RefreshReport.diffed`)

`Status` and the refresh report name how each node is maintained: "delta rules", "state per group", "touched groups", "touched frames" or "recompute and diff". A node that is recomputed and diffed says which operator causes it, in `NodeStatus.recomputed` and in the refresh summary. `RefreshReport.diffed` changes from a list of view names to a dict of view to reason: indexing and `.append` no longer work, iteration, truthiness and `len` do (#742).
