"""Read a Eurostat table as a sverify source.

Eurostat's dissemination API serves each dataset as SDMX-CSV. `eurostat()`
returns a source that downloads the rows a key selects on every refresh;
sverify diffs each download against the last, so the nodes reading it see
the exact change.

With `EUROSTAT_FIXTURES` set to a folder, the source reads
`<folder>/<dataset>.csv` instead of the network: the tests and CI run on a
recorded response.
"""

from __future__ import annotations

import io
import os
import urllib.request
from pathlib import Path

import pyarrow as pa
import pyarrow.compute as pc
import pyarrow.csv as csv
from sverify.io import Source, from_frame

API = "https://ec.europa.eu/eurostat/api/dissemination/sdmx/2.1/data"


def url(dataset: str, key: str, start: str | None = None) -> str:
    """The SDMX-CSV address of the rows of `dataset` that `key` selects."""
    query = "format=SDMX-CSV" + (f"&startPeriod={start}" if start else "")
    return f"{API}/{dataset}/{key}?{query}"


def read(dataset: str, key: str, start: str | None, dimensions: list[str]) -> pa.Table:
    """Download (or read the fixture of) one selection as an Arrow table with
    the `dimensions`, `time`, `value` and `flag`."""
    fixtures = os.environ.get("EUROSTAT_FIXTURES")
    if fixtures:
        raw = (Path(fixtures) / f"{dataset}.csv").read_bytes()
    else:
        request = urllib.request.Request(
            url(dataset, key, start), headers={"User-Agent": "sverify-pipelines"}
        )
        with urllib.request.urlopen(request, timeout=120) as response:  # noqa: S310
            raw = response.read()
    text = csv.read_csv(
        io.BytesIO(raw),
        convert_options=csv.ConvertOptions(
            column_types={"TIME_PERIOD": pa.string(), "OBS_VALUE": pa.float64()},
            strings_can_be_null=True,
        ),
    )
    out = {d: text[d].cast(pa.string()) for d in dimensions}
    out["time"] = text["TIME_PERIOD"]
    out["value"] = text["OBS_VALUE"]
    flag = text["OBS_FLAG"].cast(pa.string())
    out["flag"] = pc.if_else(pc.equal(flag, ""), pa.scalar(None, pa.string()), flag)
    return pa.table(out)


def eurostat(dataset: str, key: str, *, dimensions: list[str], start: str | None = None) -> Source:
    """A source with the rows of `dataset` that the SDMX `key` selects, from
    the period `start` on. `dimensions` are the dataset's dimensions in the
    key's order, which become the table's first columns.

    The source reads nothing while `sverify check` proves the pipeline: its
    schema is declared here.
    """
    schema = pa.schema(
        [(d, pa.string()) for d in dimensions]
        + [("time", pa.string()), ("value", pa.float64()), ("flag", pa.string())]
    )
    return from_frame(lambda: read(dataset, key, start, dimensions), name=dataset, schema=schema)
