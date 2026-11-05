"""Discovery: import a pipeline's Python file without running it, and
collect the proof of every contracted transform it applies (#744)."""

from __future__ import annotations

import importlib.util
import sys
from dataclasses import dataclass, field
from pathlib import Path
from types import ModuleType
from typing import TYPE_CHECKING, Literal

from sverify import ContractedTransform, Node
from sverify._hooks import Collected, collecting

if TYPE_CHECKING:
    from sverify import Report

Status = Literal["proved", "checked", "not_proved", "unfinished"]


@dataclass
class Checked:
    """One application of a contracted transform in the file, and its proof.

    Attributes:
        name: The transform's name.
        nodes: The file's variables that hold the node this application
            built (empty when no variable does, or it built an Ibis table).
        report: The `sverify.Report` of its postconditions; None when the
            budget ran out before it was proved.
        links: Why a precondition on another transform's result does not
            follow from that transform's guarantees, one message each.
        params: For each input table the report names, the parameter of
            the transform that reads it.
        transform: The `sverify.ContractedTransform`.
    """

    name: str
    nodes: list[str]
    report: Report | None
    links: list[str]
    params: dict[str, str]
    transform: ContractedTransform

    @property
    def status(self) -> Status:
        """`"proved"`; `"checked"`, when every postcondition it does not
        prove is checked on the data at each refresh
        (`on_unproved="runtime"`) and nothing else is missing;
        `"not_proved"`; or `"unfinished"`, when the budget ran out first."""
        r = self.report
        if r is None:
            return "unfinished"
        if self.links:
            return "not_proved"
        if r.proved:
            return "proved"
        rest = [c for c in r.ensures if not c.portable and not c.checked]
        missing = rest or r.errors or r.needed or r.transfer or r.floats_unmet
        return "not_proved" if missing else "checked"


@dataclass
class Discovery:
    """What `discover` found in a file.

    Attributes:
        path: The file.
        checked: Each application of a contracted transform, in the order
            the file made them.
        unchecked: Contracted transforms the file defines but never
            applies: without input schemas they have nothing to be proved
            on.
        nodes: The file's nodes, by variable name.
        transforms: The file's contracted transforms, by variable name.
        error: What stopped the import, if anything (a refusal,
            `sverify.errors.Unsupported`; an error of the file's own).
        module: The imported module, if the import finished.
    """

    path: Path
    checked: list[Checked] = field(default_factory=list)
    unchecked: list[str] = field(default_factory=list)
    nodes: dict[str, Node] = field(default_factory=dict)
    transforms: dict[str, ContractedTransform] = field(default_factory=dict)
    error: BaseException | None = None
    module: ModuleType | None = None
    _collected: list[Collected] = field(default_factory=list, repr=False)

    def select(self, target: str) -> list[Checked]:
        """The applications that built node `target` (a variable of the
        file) or applied the transform named `target`."""
        return [c for c in self.checked if target in c.nodes or c.name == target]

    def _finish(self) -> None:
        """Turn the collected calls into `checked`, naming nodes by the
        file's variables."""
        by_report: dict[int, list[str]] = {}
        for var, node in self.nodes.items():
            try:
                report = node.report
            except Exception:  # noqa: BLE001 - a node that cannot say is unnamed
                report = None
            if report is not None:
                by_report.setdefault(id(report), []).append(var)
        # A transform applied twice to the same inputs has one (cached)
        # report: one entry.
        seen: set[tuple[int, int]] = set()
        self.checked = []
        for c in self._collected:
            if c.report is not None:
                key = (id(c.transform), id(c.report))
                if key in seen:
                    continue
                seen.add(key)
            nodes = by_report.get(id(c.report), []) if c.report is not None else []
            links = [str(e) for e in c.links]
            self.checked.append(
                Checked(c.transform.name, nodes, c.report, links, dict(c.params), c.transform)
            )
        applied = {id(c.transform) for c in self._collected}
        self.unchecked = [
            t.name for t in dict.fromkeys(self.transforms.values()) if id(t) not in applied
        ]


def load(path: str | Path, out: Discovery | None = None) -> Discovery:
    """Import the file at `path` within `collecting`, into `out` (which
    holds what was collected so far, should the import be stopped)."""
    path = Path(path)
    out = out if out is not None else Discovery(path)
    if not path.is_file():
        raise FileNotFoundError(f"{path}: no such file")
    name = f"_sverify_cli_{abs(hash(str(path.resolve())))}"
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ImportError(f"{path}: not a Python file")
    module = importlib.util.module_from_spec(spec)
    folder = str(path.resolve().parent)
    sys.path.insert(0, folder)
    sys.modules[name] = module
    try:
        with collecting() as collected:
            out._collected = collected
            try:
                spec.loader.exec_module(module)
                out.module = module
            except Exception as e:  # noqa: BLE001 - reported, with what was found before it
                out.error = e
            finally:
                _scan(module, out)
                out._finish()
    finally:
        if sys.path and sys.path[0] == folder:
            sys.path.pop(0)
    return out


def _scan(module: ModuleType, out: Discovery) -> None:
    for var, value in list(vars(module).items()):
        if isinstance(value, Node):
            out.nodes[var] = value
        elif isinstance(value, ContractedTransform):
            out.transforms[var] = value
