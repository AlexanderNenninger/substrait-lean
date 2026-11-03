### Windows over time frames recompute only the rows near the change (tested)

A node of window aggregates over bounded RANGE frames of one time column
(`range=(-ibis.interval(minutes=5), 0)`) recomputes only the output rows
whose frames a batch's rows fall in, from the input rows those frames read.
This strategy is tested, not proved: `status()` and the refresh summary say
"touched frames recomputed (tested, not proved)", and the lemma it rests on
is #458 (#294).
