"""The Lean packages' layers (#1189): the core, the analysis, engines-common,
and the engines' own packages (DuckDB's, Polars's, Spark's).

Each layer is a Lake package of its own, rooted at a prefix of its own under
the `Sverify` umbrella, and imports only the layers below it. The standalone
`lake build --wfail` of each package (CI's `lean` job) is the guard; this test
reads the same constraint from the sources, in a second, without Lean.
"""

import re
import tomllib
from pathlib import Path

import pytest

from _repo import needs_repo

pytestmark = needs_repo

ROOT = Path(__file__).resolve().parents[2]
LEAN = ("Init", "Std", "Lean")

# What an engine package may import (Fable, #1189).
ENGINE = ["core", "analysis", "frontend", "engines"]

# Each layer: its directory, package, library root and the layers it may import
# (an engine package also the frontend, which it requires only where it reads plans).
LAYERS = {
    "core": ("sverify-core", "Sverify.Core", []),
    "analysis": ("sverify-analysis", "Sverify.Analysis", ["core"]),
    "frontend": ("sverify-frontend", "Sverify.Frontend", ["core", "analysis"]),
    "engines": ("sverify-engines", "Sverify.Engines", ["core", "analysis"]),
    "engines/polars": ("sverify-polars", "Sverify.Polars", ENGINE),
    "engines/spark": ("sverify-spark", "Sverify.Spark", ENGINE),
    "engines/duckdb": ("sverify-duckdb", "Sverify.DuckDB", ENGINE),
}


def _modules(layer: str) -> dict[str, Path]:
    _, root, _ = LAYERS[layer]
    base = ROOT / layer
    return {
        ".".join(p.with_suffix("").relative_to(base).parts): p
        for p in (base / Path(*root.split("."))).rglob("*.lean")
    } | {root: base / f"{Path(*root.split('.'))}.lean"}


def _imports(path: Path) -> list[str]:
    return re.findall(r"^import (\S+)", path.read_text(), re.M)


def _lakefile(layer: str) -> tuple[str, list[list[str]], dict[str, str]]:
    """A layer's package name, its libraries' roots and its requires, from its
    `lakefile.toml`, or from its `lakefile.lean` (DuckDB's, which reads
    `check_generated` for its generated lowering)."""
    toml = ROOT / layer / "lakefile.toml"
    if toml.is_file():
        conf = tomllib.loads(toml.read_text())
        roots = [lib["roots"] for lib in conf["lean_lib"]]
        return conf["name"], roots, {r["name"]: r["path"] for r in conf.get("require", [])}
    text = (ROOT / layer / "lakefile.lean").read_text()
    [name] = re.findall(r"^package «([^»]+)»", text, re.M)
    roots = [re.findall(r"`([\w.]+)", r) for r in re.findall(r"roots := #\[([^\]]*)\]", text)]
    requires = dict(re.findall(r'^require «([^»]+)» from "([^"]+)"', text, re.M))
    return name, roots, requires


@pytest.mark.parametrize("layer", LAYERS)
def test_lakefile(layer):
    package, root, below = LAYERS[layer]
    name, roots, requires = _lakefile(layer)
    assert name == package
    # One library with the layer's root; a library of generated modules has no root.
    assert [r for r in roots if r] == [[root]]
    # Never a library rooted at the umbrella alone: it would claim every layer's modules.
    assert all("Sverify" not in r for r in roots)
    up = "../" * len(Path(layer).parts)
    allowed = {LAYERS[b][0]: f"{up}{b}" for b in below}
    # The layers directly below, required; the frontend, where the package reads plans.
    assert {k: v for k, v in allowed.items() if k != "sverify-frontend"}.items() <= requires.items()
    assert requires.items() <= allowed.items()


@pytest.mark.parametrize("layer", LAYERS)
def test_imports_stay_in_their_layers(layer):
    _, root, below = LAYERS[layer]
    allowed = (root, *(LAYERS[b][1] for b in below))
    bad = [
        f"{name} imports {imp}"
        for name, path in _modules(layer).items()
        for imp in _imports(path)
        if imp.split(".")[0] not in LEAN
        and not any(imp == a or imp.startswith(a + ".") for a in allowed)
    ]
    assert not bad, bad


@pytest.mark.parametrize("layer", LAYERS)
def test_root_imports_every_module(layer):
    _, root, _ = LAYERS[layer]
    modules = _modules(layer)
    assert set(_imports(modules[root])) == set(modules) - {root}


def test_main_package_requires_every_layer():
    lakefile = (ROOT / "lakefile.lean").read_text()
    for layer, (package, _, _) in LAYERS.items():
        assert f'require «{package}» from "{layer}"' in lakefile
