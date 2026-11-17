### Postconditions are proved over the transformation itself

`substrait-check --contract` builds each postcondition's plan from the
request's transformation and refuses a postcondition plan that selects from
anything else, so `check_proved_sound` speaks of the transformation the report
is about (#1484, finding 2).

This fixes a soundness hole in `Report.from_substrait`. An exported plan carries
the shims the export applied, and the postconditions' plans in the export do
not. The recheck proved the postconditions of the plan without the shims and
reported them for the exported plan. It now proves each condition over the
exported plan. An export whose condition reads another relation is refused
with an error that says to verify and export again.

An Ibis condition over a transformation that ends in a join's `select` is no
longer merged into that select by Ibis.
