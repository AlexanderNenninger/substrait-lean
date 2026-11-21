### `sverify check` on a `.sql` file with an unterminated string exits 2 (#1362)

A tokenizer error of the SQL parser was a traceback; it is a usage error naming the parse failure.
