### Inferred preconditions are errors by default: `on_inferred=` (#655)

A precondition sverify infers to rule out a runtime error (`amount * 2` needs
`_.amount < 2**62`, `total // qty` needs `_.qty != 0`) is no longer assumed
silently, since checking it on the data refuses batches the user never asked
to refuse. `sv.verify` and `sv.transform` take `on_inferred=`:

- `"error"` (the default): the plan is not proved without it. The report
  lists each one under `needs:` (`Report.needed`) with where it came from and
  the fixes: declare it in `requires` (each run then checks it on the data),
  or rewrite so no row needs it (filter those rows first, or a CASE). A
  transform raises `VerificationError`, and `Report.run` and `refresh` refuse
  the plan with the same text.
- `"warn"`: assumed and checked on the data as before, with an
  `InferredPreconditionWarning` naming each one.
- `"silent"`: assumed and checked as before.

`infer=False` still turns inference off: an overflow is then an error whose
hint names the bound. Declared `requires` are checked on the data as before.
`SUM`s assumed to fit and double operations assumed to stay finite
(`Report.assumed`) are not inferred preconditions and keep their run-time
checks.
