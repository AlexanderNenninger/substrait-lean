### A source that cannot restore is told apart by its contents

A `Source` without `restore` (`from_frame`, for one) numbers its versions by
the reads of the process. Its sinks now record a digest of its contents with
the version:

- A restarted job whose first read has the recorded digest resumes from
  the sink and writes nothing, where it rewrote the whole table on every
  run (#889).
- Two processes that numbered other contents alike no longer take each
  other's commit for their own state: the second numbers its version above
  the sink's and writes its rows (#965).

A node reading a `StaticSource` resumes from its sink after a restart too:
the check of the static tables' digests compared the stored ones with none.
Found by the TLA+ model of the refresh protocol (#933).
