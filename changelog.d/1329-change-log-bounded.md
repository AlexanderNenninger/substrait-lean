### A source's change log drops what every reader has read

`StaticSource` kept every change `apply` made since it was built, and an `io.Source` the last 64 batches, in the Python process, after every node had read them. A long-running pipeline's driver memory grew with its input, beside the views' state in the engine. Each pipeline now reports the version it committed, and the log keeps only the changes some reader has not read yet. A reader that lags keeps its changes; one older than the log gets the whole table to diff, as before (#1329).
