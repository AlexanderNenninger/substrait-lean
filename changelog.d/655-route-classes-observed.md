### Route classes: exact, observed, shim, refused (#655)

A route's class (`Route.cls`) is one of four: `exact` (every result the
engine gives is one the reference allows; was `refines`), `observed` (equal
to one up to an observation; was `refines_up_to` and `approx`, since a
tolerance is an observation of doubles), `shim` and `refused`. An observed
route keeps the observation in `Route.observation` (its components, and the
tolerance the plan's bound gives) and whether that bound is proved in
`Route.bound_proved`. Messages and docs say "observation" where they said
`q`; sverify reads a choices row's `"observation"` and `"rerun_observation"`
keys, and still the checker's `"q"` and `"rerun"`. `docs/realizability.md`
labels its cases the same way.
