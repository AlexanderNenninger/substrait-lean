### A faster check: a proof cache, and no search where only ties are open

- Sverify keeps the checker's answers on disk, so the next `verify`,
  `check` or `refresh` of an unchanged transform does not prove it again.
  An entry is keyed by the plans, conditions and profile the checker reads,
  sverify's version and a hash of the checker binary; any change to them
  proves again. The cache is in `SVERIFY_CACHE_DIR` (default
  `~/.cache/sverify`), and `SVERIFY_CACHE=off` turns it off
  ([#825](https://github.com/AlexanderNenninger/substrait-lean/issues/825)).
- A postcondition that only the order of ties leaves open has the reason
  `"ties"` (`CheckedCondition.ties`), and the counterexample search skips
  it ([#691](https://github.com/AlexanderNenninger/substrait-lean/issues/691)).
- A checker request interrupted by the CLI's time budget or Ctrl-C ends
  the checker's process. Before, its answer stayed in the pipe and the next
  request read it as its own.
- The checker speaks protocol 2 (a `--rows` mode for the counterexample
  search): rebuild a checker you set with `SVERIFY_CHECK`.
- CI times every catalogue transform and the tour's notebooks, cold and
  warm, by stage, and fails past the budgets of
  [#745](https://github.com/AlexanderNenninger/substrait-lean/issues/745)
  (`python -m sverify_dev.bench`).
