### A sink's change lands only on the state it was computed from

When another commit of the same node reached a sink between two refreshes of
a process (a second process refreshing the same sink, or the late commit of
a crashed one after a restart resumed), the process wrote its change since
its own last state on top of that commit. On Delta a row that changed and
changed back stayed in the sink (#963). The process now writes its change
only on top of the record it wrote, skipped to or resumed from, and replaces
the rows otherwise. Found by the TLA+ model of the refresh protocol (#933).
