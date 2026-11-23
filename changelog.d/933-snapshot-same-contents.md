### Fixed

- A node over a source that cannot restore (`from_frame`) no longer rewrites its sink when the sink's record is at a higher version of the same contents. The record's digest says the rows are the state, and the writer skips, as the model of the refresh protocol decides ([#933](https://github.com/AlexanderNenninger/substrait-lean/issues/933)).
