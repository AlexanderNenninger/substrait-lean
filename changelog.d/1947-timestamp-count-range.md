A cast of an integer count of seconds, milliseconds or microseconds to a
timestamp now raises (`overflow`) where it lands outside 0001 to 9999, the
reference's timestamps (D32). Sverify reports it as an issue unless the
count's bounds rule it out, and the written SQL and the Polars plan raise at
run time. Before, such a cast was proved with no precondition (#1947).
