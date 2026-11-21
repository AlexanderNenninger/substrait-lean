"""SARIF 2.1.0 documents checked against the published JSON schema
(`tests/standards/sarif-schema-2.1.0.json`, #793)."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

jsonschema = pytest.importorskip("jsonschema")

_SCHEMA = json.loads((Path(__file__).parent / "standards" / "sarif-schema-2.1.0.json").read_text())
jsonschema.validators.validator_for(_SCHEMA).check_schema(_SCHEMA)
_VALIDATOR = jsonschema.validators.validator_for(_SCHEMA)(_SCHEMA)


def valid_sarif(text: str) -> dict:
    """The document in `text`, after it validates against the SARIF 2.1.0 schema."""
    doc = json.loads(text)
    _VALIDATOR.validate(doc)
    return doc
