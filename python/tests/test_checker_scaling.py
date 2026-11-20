"""The checker's cost stays about linear in an expression's size (#1877).

`x IN (...)` is a left-nested chain of `OR`s. `Expr.absD` once evaluated the
left operand of each `OR` several times, so the cost multiplied with every
literal: 3 s for 11 strings, minutes for 13. A list of 60 now takes well under
a second. The test runs the check in a subprocess with a timeout, so a
regression fails it rather than stalling the worker.
"""

import subprocess
import sys
import textwrap

SCRIPT = textwrap.dedent(
    """
    import ibis
    import sverify as sv

    t = ibis.table({"s": "string", "a": "int64"}, name="t")
    for lits in ([f"v{i % 3}" for i in range(60)], [f"v{i}" for i in range(60)]):
        sv.verify(t.filter(t.s.isin(lits)))
    """
)


def test_a_long_in_list_checks_quickly():
    subprocess.run([sys.executable, "-c", SCRIPT], check=True, timeout=60)
