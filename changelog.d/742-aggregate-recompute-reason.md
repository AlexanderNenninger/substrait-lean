### A recomputed aggregate names its own reason

A node whose aggregate has no delta rules, such as an AVG of integers, said
it was recomputed because it was "not incrementally maintainable (left join,
fetch or window)", operators the plan need not contain. Its status now names
the measure: "mean is a AVG of int64: only integer SUMs and DECIMAL and
DOUBLE SUMs and AVGs are kept" (#742, #248). Views that are not aggregates
keep the checker's reason.
