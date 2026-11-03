### Integer overflow is an error at the declared width

Breaking: `+`, `-`, `*` and negation of integers whose result does not fit
its declared type (`BIGINT`, or `INTEGER`, `SMALLINT`, `TINYINT`) raise, on
every engine, where a plan omits `overflow` or asks for `ERROR` (#202). An
overflow `verify` cannot rule out makes the report unproved; it was a "may
wrap around" warning. Inferred bounds (#244) discharge most of these, and the
report's hint names the bound to add to `requires` for the rest. The
arithmetic sverify adds itself (0-based `row_number`, `find`, floor
division) is proved free of overflow, under the hypothesis that a window
reads fewer than 2⁶² rows (#254).
