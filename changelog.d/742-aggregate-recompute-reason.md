### A recomputed aggregate names its own reason

A node whose aggregate has no delta rules, such as a SUM or AVG of doubles,
said it was recomputed because it was "not incrementally maintainable (left
join, fetch or window)", operators the plan need not contain. Its status now
names the measure: "total is a SUM of float64: only integer SUMs and DECIMAL
SUMs and AVGs are kept" (#742, #248). Views that are not aggregates keep the
checker's reason.
