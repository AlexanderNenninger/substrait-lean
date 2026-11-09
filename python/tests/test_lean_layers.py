"""The Lean packages' layers (#1189): the core, the analysis, engines-common.

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

# Each layer: its directory, package, library root and the layers it may import.
LAYERS = {
    "core": ("sverify-core", "Sverify.Core", []),
    "analysis": ("sverify-analysis", "Sverify.Analysis", ["core"]),
    "engines": ("sverify-engines", "Sverify.Engines", ["core", "analysis"]),
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


@pytest.mark.parametrize("layer", LAYERS)
def test_lakefile(layer):
    package, root, below = LAYERS[layer]
    conf = tomllib.loads((ROOT / layer / "lakefile.toml").read_text())
    assert conf["name"] == package
    [lib] = conf["lean_lib"]
    assert lib["roots"] == [root]
    # Never a library rooted at the umbrella alone: it would claim every layer's modules.
    assert all(r != "Sverify" for r in lib["roots"])
    requires = {r["name"]: r["path"] for r in conf.get("require", [])}
    assert requires == {LAYERS[b][0]: f"../{b}" for b in below}


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
