### Theorem cards for the refresh protocol

`docs/theorems/refresh_no_corruption.md` and `refresh_record_describes_table.md` say what `Refresh.no_corruption` and `Refresh.record_describes_table` assume and leave out, with a Delta example whose summaries `test_readme.py` pins: a resumed refresh, a merge, and a replace after another application wrote the sink ([#1094](https://github.com/AlexanderNenninger/substrait-lean/issues/1094)).
