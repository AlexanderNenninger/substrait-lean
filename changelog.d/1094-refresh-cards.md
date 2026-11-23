### Theorem cards for the refresh protocol

`docs/theorems/` has cards for `Refresh.no_corruption`, `Refresh.record_describes_table`, `Refresh.read_is_head`, `Refresh.monotone` and `Refresh.quiet`. They say what each assumes and leaves out; the first two have a Delta example whose summaries `test_readme.py` pins: a resumed refresh, a merge, and a replace after another application wrote the sink ([#1094](https://github.com/AlexanderNenninger/substrait-lean/issues/1094)).
