### Routes and determinism in refreshes (#444)

- `Node.refresh(engine=..., route="auto")` and `sv.group(...).refresh(route=...)`
  take each node's proof to the engine by a route, as `Report.run` does,
  and refuse before anything runs where none applies
  (`sverify.errors.RouteError`). `StageRefresh.route` records the route and
  its class.
- A stored node whose result is not determined up to row order (its
  report's `deterministic`) is refused: its sink commits each epoch once,
  so a rerun must give the same rows (D10 of
  [core-semantics.md](docs/core-semantics.md#d10-determinism)). A node
  without a sink reports it.
