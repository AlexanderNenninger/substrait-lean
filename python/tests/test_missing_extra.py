"""A call that needs an extra which is not installed names it (#183): the
error says `pip install 'sverify[<extra>]'`.

One subprocess stands for a bare `pip install sverify`: every module an
extra brings is missing (`sys.modules[name] = None`, which imports and
`find_spec` read as not installed), and each entry point runs in turn.
"""

from __future__ import annotations

import json
import subprocess
import sys
import textwrap

import pytest

import sverify as sv

#: The modules the extras bring, missing from a bare install.
MISSING = [
    "duckdb",
    "polars",
    "sverify_polars",
    "pyspark",
    "sverify_spark",
    "deltalake",
    "pyiceberg",
    "pyarrow.flight",
    "hypothesis",
    "yaml",
    "openlineage",
    "boto3",
    "keyring",
]

#: Each entry point, the code that calls it, and the extra its error names.
CALLS = {
    "connect polars": ("sv.connect('polars')", "polars"),
    "connect spark": ("sv.connect('spark')", "spark"),
    "connect duckdb": ("sv.connect('duckdb')", "duckdb"),
    "verify under polars": ("sv.verify(T, semantics='polars')", "polars"),
    "run on polars": ("sv.verify(T).run(None, 'polars')", "polars"),
    "dialect spark": ("from sverify.sql import dialect_of; dialect_of('spark')", "spark"),
    "delta": ("from sverify.io import DeltaSource", "delta"),
    "iceberg": ("from sverify.io import IcebergSource", "iceberg"),
    "flight": ("import sverify.io.flight", "flight"),
    "testing": ("from sverify.testing import cases; cases(None)", "testing"),
    "odcs yaml": ("from sverify import odcs; odcs.read('contract.yaml')", "odcs"),
    "secret": (
        "from sverify.io._secrets import Resolver; Resolver().value('keychain:s/a')",
        "secrets-keychain",
    ),
}

SCRIPT = """
import json, sys
for name in {missing!r}:
    sys.modules[name] = None
import ibis
import sverify as sv
T = ibis.table({{"a": "int64"}}, name="t")
out = {{}}
for name, code in {calls!r}.items():
    try:
        exec(code)
        out[name] = "no error"
    except Exception as e:
        out[name] = f"{{type(e).__name__}}: {{e}}"
print(json.dumps(out))
"""


def test_each_entry_point_names_its_missing_extra() -> None:
    code = textwrap.dedent(SCRIPT).format(
        missing=MISSING, calls={k: c for k, (c, _) in CALLS.items()}
    )
    run = subprocess.run(
        [sys.executable, "-W", "ignore", "-c", code], capture_output=True, text=True, check=True
    )
    got = json.loads(run.stdout.strip().splitlines()[-1])
    hint = {k: f"pip install 'sverify[{extra}]'" for k, (_, extra) in CALLS.items()}
    wrong = {k: got[k] for k in CALLS if hint[k] not in got[k]}
    assert not wrong, wrong


def test_a_name_that_is_no_extra_keeps_its_error() -> None:
    with pytest.raises(ValueError, match="unknown engine 'oracle'"):
        sv.connect("oracle")


def test_an_installed_engine_is_not_missing() -> None:
    """Spark runs through a session (`local=False`) and is installed all the
    same: its name names no extra, and neither does any other engine whose
    modules import here."""
    from importlib.util import find_spec

    from sverify import _engines, profiles

    for engine, p in profiles.plugins().items():
        if engine in _engines._engine_extras() and all(find_spec(m) for m in p.modules):
            assert _engines.not_installed(engine) is None, engine
    assert "spark" in _engines._engine_extras() and "all" not in _engines._engine_extras()
