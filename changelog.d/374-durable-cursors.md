### Custom sources resume from the cursor their sink recorded

A sink now records the cursor of each source next to its version
(`Contract.cursors`). A `sverify.io.Source` that implements
`restore(cursor)`, the whole table as of a recorded cursor, starts there
after a restart: the stored nodes resume from their sinks, the first
refresh reads only what is new since, and the sink writes that change.
`from_query` and `from_files` implement it. A source without `restore`, or
whose cursor is gone (`restore` returns None), is read in full again and
written once, as before. `Source.snapshot` also serves the versions whose
batches the source still keeps (#374).
