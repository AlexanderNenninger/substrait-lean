### An overlapping refresh that loses the commit race reports "already committed"

When two refreshes of one sink overlap and the other commits the same state first, the slower refresh returns that state as already committed instead of raising `ConcurrentWriteError`. If the sink holds a different state, the error stays (#1485).
