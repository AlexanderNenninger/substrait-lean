### Breaking: `Sink.keeps_retired` is a plain class attribute (#2081)

`keeps_retired` is the one name a custom sink sets to say it keeps the rows a
view retires (`keeps_retired = True`). The deprecated property that read the
internal `_keeps_retired` is removed; nothing changes for a sink that already
sets `keeps_retired`.
