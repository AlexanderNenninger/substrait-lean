"""Proposers: what proposes a precondition or a counterexample for an
obligation the checker leaves open (#2245).

Internal: not part of sverify's public API (`docs/stability.md`); it may
change in any release.

A proposer only proposes. A report relies on a proposal only once it is
confirmed: a precondition by proving the postcondition again under it
(`verify` with `infer`), a counterexample by `Rel.eval`. A proposal's
`verdict` says whether it is confirmed yet.

sverify has two proposers, and `verify` runs them itself:

- `infer`: the checker's backward interval pass (`Infer.suggest`,
  `analysis/Sverify/Analysis/Infer.lean`) proposes bounds on input columns,
  and `Infer` writes them as conditions on the tables;
- `search`: the bounded search of `sverify.counterexample` proposes small
  input tables, each one evaluated by `Rel.eval`.

A package registers a proposer of its own under the entry-point group
`sverify.proposers`, as an engine registers under `sverify.profiles`:

```toml
[project.entry-points."sverify.proposers"]
myproposer = "my_package:PROPOSER"
```

`proposers()` lists them; `verify` runs none but its own two yet (#2245).
"""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from importlib.metadata import entry_points
from typing import TYPE_CHECKING, Any, Literal, Protocol

from sverify import counterexample

if TYPE_CHECKING:
    from sverify.report import Inferred

#: The entry-point group a package registers its proposer under.
GROUP = "sverify.proposers"

Kind = Literal["precondition", "counterexample"]
"""What an obligation asks for: preconditions that would prove it, or input
tables on which it fails."""


@dataclass(frozen=True)
class Obligation:
    """What the checker leaves open, and what a proposer needs to propose
    for it."""

    kind: Kind
    schemas: Mapping[str, Any]
    """The input tables' Ibis schemas, by name."""
    data: Mapping[str, Any]
    """The rest, by kind. A precondition: `needs`, the checker's bounds
    (`{table, col, lo, hi}`, `{table, col, ne}`, `{table, col, not_null}` or
    `{table, col, text}`). A counterexample: the keyword arguments of
    `sverify.counterexample.search` after the schemas."""


@dataclass(frozen=True)
class Verdict:
    """Whether a proposal is confirmed, and by what."""

    ok: bool
    proved_by: str
    """`"Rel.eval"` for a counterexample evaluated on the plan."""


@dataclass(frozen=True)
class Proposal:
    """What a proposer proposes for one obligation."""

    proposer: str
    value: Any
    """By kind: the conditions per table (`Inferred`), or a `Counterexample`."""
    verdict: Verdict | None = None
    """None until something confirms it."""


class Proposer(Protocol):
    """Proposes for the obligations of its kinds; None where it has nothing."""

    name: str
    kinds: tuple[Kind, ...]

    def propose(self, obligation: Obligation) -> Proposal | None: ...


class Infer:
    """The checker's backward pass, written as conditions on the tables."""

    name = "infer"
    kinds: tuple[Kind, ...] = ("precondition",)

    def propose(self, obligation: Obligation) -> Proposal | None:
        conds = self.conditions(obligation.data["needs"], obligation.schemas)
        return Proposal(self.name, conds) if conds else None

    @staticmethod
    def conditions(needs: Sequence[dict], schemas: Mapping[str, Any]) -> dict[str, list[Inferred]]:
        """The conditions of the checker's bounds (column positions, integer
        codes as strings), per table."""
        from sverify.contracts import (
            _bound_conditions,
            _ne_condition,
            _not_null_condition,
            _text_condition,
        )

        out: dict[str, list[Inferred]] = {}
        for n in needs:
            schema = schemas.get(n["table"])
            if schema is None or n["col"] >= len(schema):
                continue
            col = list(schema)[n["col"]]
            have = out.setdefault(n["table"], [])
            if "text" in n:
                new = [_text_condition(col, n["text"])]
            elif n.get("not_null"):
                new = [_not_null_condition(col)] if schema[col].nullable else []
            elif "ne" in n:
                c = _ne_condition(col, schema[col], int(n["ne"]))
                new = [] if c is None else [c]
            else:
                lo, hi = (None if n[k] is None else int(n[k]) for k in ("lo", "hi"))
                new = _bound_conditions(col, schema[col], lo, hi)
            for c in new:
                c.column = col
            have += [c for c in new if c not in have]
        return {t: cs for t, cs in out.items() if cs}


class Search:
    """The bounded counterexample search. It evaluates every hit by
    `Rel.eval`, so a proposal comes confirmed."""

    name = "search"
    kinds: tuple[Kind, ...] = ("counterexample",)

    def propose(self, obligation: Obligation) -> Proposal | None:
        found = counterexample.search(obligation.schemas, **obligation.data)
        if found is None:
            return None
        return Proposal(self.name, found, Verdict(True, "Rel.eval"))


INFER = Infer()
SEARCH = Search()


def proposers() -> dict[str, Proposer]:
    """Every proposer by name: sverify's own, and those registered under
    `sverify.proposers`. A registered one with a built-in's name is skipped."""
    out: dict[str, Proposer] = {p.name: p for p in (INFER, SEARCH)}
    for ep in entry_points(group=GROUP):
        if ep.name not in out:
            out[ep.name] = ep.load()
    return out
