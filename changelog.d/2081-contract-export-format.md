### `sverify contract export` drops `--format`

`sverify contract export` writes ODCS, its one format, so its `--format odcs` flag is gone: drop it from the command. The flag chose nothing, and the 1.x promise keeps a flag for good once 1.0 ships ([#2081](https://github.com/AlexanderNenninger/substrait-lean/issues/2081)).
