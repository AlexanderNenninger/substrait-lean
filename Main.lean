import SubstraitCheck

/-! `substrait-check`, over this repository's engine profiles. The modes are
`SubstraitCheck.lean`'s. -/

def main (args : List String) : IO UInt32 :=
  Substrait.Checker.checkerMain Substrait.builtinEngines args
