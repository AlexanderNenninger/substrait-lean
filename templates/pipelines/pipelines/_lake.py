"""Where the tables go: the sinks of every pipeline in this repository.

`SVERIFY_LAKE` is the folder or bucket prefix of the current stage. The
workflows set it (`.github/actions/store`):

* everything in your repository: `_data/production` or `_data/staging/pr-<n>`,
  a checkout of the `data` branch;
* for enterprise: `s3://…/production`, `gs://…`, `az://…`, with credentials
  from OIDC in the environment, which delta-rs reads.

Without it, tables go to `lake/` in the working directory, for local runs.

Each table keeps `SVERIFY_KEEP_DAYS` days of history (default 7): older
versions are vacuumed every 10 commits, and the log keeps 30 days at most.
That bounds what a `data` branch grows by between squashes.
"""

from __future__ import annotations

import os
from datetime import timedelta

from sverify.io import DeltaSink


def lake() -> str:
    """The current stage's folder or bucket prefix."""
    return os.environ.get("SVERIFY_LAKE", "lake").rstrip("/")


def sink(name: str) -> DeltaSink:
    """The Delta table `name` of the current stage, with its history capped."""
    keep = timedelta(days=float(os.environ.get("SVERIFY_KEEP_DAYS", "7")))
    return DeltaSink(
        f"{lake()}/{name}",
        checkpoint_interval=10,
        compact_every=10,
        vacuum_retention=keep,
        log_retention=max(keep, timedelta(days=30)),
    )
