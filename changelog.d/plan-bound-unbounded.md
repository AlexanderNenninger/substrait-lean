### A tolerance on a double column without a bound is no longer reported met

A stated tolerance (`sv.equivalent(floats=sv.within(...))`) on a double
column whose bound the checker can't give, such as a `SUM` of doubles without
a row cap or a value computed from one, passed as met by every engine, and
the plan reported proved. It is now refused there with the reason
(`… has no bound on its distance to the reference …`), and a run on such a
column counts as tested, not proved.
