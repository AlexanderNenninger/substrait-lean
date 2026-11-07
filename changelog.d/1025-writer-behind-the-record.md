### A sink no longer writes an older state over a newer record

When another process committed a later version of a node between this
refresh's read of its sources and its read of the sink, the refresh took the
higher source version on record for a table dropped and created again, and
wrote its older rows over the newer ones; the next refresh of the other
process put them back (#1025). A lower version of the same table (the same
table id) now means this refresh is behind: it skips, and the sink keeps the
later state. A source whose table id changed is still rewritten in full
(#516). Found by the test that pins `Sink._commit` to the Lean model's
`Refresh.next` (#933).
