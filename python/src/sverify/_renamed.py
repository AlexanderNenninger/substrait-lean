"""The module-level public names 0.9.0 renamed or moved, each with the name
that replaces it (#2577). A public module's `__getattr__` raises
`AttributeError` with the replacement for one of these, so the old spelling
fails loudly and says what to write. None of them is an alias: each raises.

`docs/upgrading.md` has the migration note for each, with an example."""

#: Old dotted name -> the name to write instead.
RENAMED: dict[str, str] = {
    "sverify.Changes": "sverify.io.Changes",
    "sverify.from_substrait": "sverify.Report.from_substrait",
    "sverify.types.Observation": "sverify.types.Lenses",
    "sverify.types.CheckedCondition": "sverify.types.Postcondition",
    "sverify.types.RefreshReport": "sverify.types.BatchRefresh",
    "sverify.errors.SqlError": "sverify.errors.SQLError",
    "sverify.errors.Unsupported": "sverify.errors.UnsupportedError",
    "sverify.errors.NotIncremental": "sverify.errors.NotIncrementalError",
    "sverify.odcs.OdcsContract": "sverify.odcs.ODCSContract",
    "sverify.io.FlightLog": "sverify.testing.FlightLog",
}


def missing(module: str, name: str) -> AttributeError:
    """The error for `module.name` that the module does not have, naming the
    replacement where 0.9.0 renamed it."""
    message = f"module {module!r} has no attribute {name!r}"
    if (new := RENAMED.get(f"{module}.{name}")) is not None:
        message += f"; sverify 0.9.0 renamed it {new}"
    return AttributeError(message)
