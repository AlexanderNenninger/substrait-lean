"""Ibis expressions to Substrait plans (protobuf JSON) for the Lean checker.

Internal: not part of sverify's public API, which is `sverify`, `sverify.io`,
`sverify.engines` and `sverify.errors`; it may change in any release.

Derived from ibis-substrait (Apache License 2.0; see `LICENSE` and
`README.md` in this directory): one translation per Ibis operation, and
field offsets threaded through join chains, follow upstream's
`compiler/translate.py`. Modified by the substrait-lean authors:

* ported from Ibis 9 to the Ibis version `sverify` pins;
* writes plain protobuf JSON with the functions and encodings
  `SubstraitLean/Parse.lean` reads, instead of resolving signatures from
  Substrait's extension YAMLs;
* every operation means what Ibis's DataFusion SQL compiler makes of it
  (`ibis/backends/sql/compilers/{base,datafusion}.py`, plus `sverify.engine`'s
  integer `//`), with Ibis's type promotions written as explicit casts;
* fixes upstream's integer `/` (it divided integers), dropped `where=`
  filters, sort keys that were always NULLS FIRST, promotions that could
  cast a double down to an integer, and timestamp literals read in local
  time;
* raises `Unsupported` for everything outside the Lean model.

`_base` holds the translators, the dispatch tables and the entry points. Each
area module (`AREAS`) holds its rules and registers them into those tables,
so a new rule goes at the end of its area's `register` call.
"""

from __future__ import annotations

from types import ModuleType

from sverify.ibis_substrait._base import Unsupported as Unsupported
from sverify.ibis_substrait._base import exact as exact
from sverify.ibis_substrait._base import to_substrait as to_substrait
from sverify.ibis_substrait._base import to_substrait_json as to_substrait_json

# The areas register their rules when imported, in this order; each imports
# only areas before it.
# isort: off
from sverify.ibis_substrait import (
    core,
    casts,
    strings,
    temporal,
    nested,
    aggregates,
    windows,
    relations,
)

# isort: on
from sverify.ibis_substrait.relations import SQLModel as SQLModel
from sverify.ibis_substrait.relations import sql_model_schema as sql_model_schema
from sverify.ibis_substrait.relations import sql_view_schema as sql_view_schema

__all__ = ["Unsupported", "to_substrait", "to_substrait_json"]

AREAS: tuple[ModuleType, ...] = (
    core,
    casts,
    strings,
    temporal,
    nested,
    aggregates,
    windows,
    relations,
)
