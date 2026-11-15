"""Every option of the core is named in `docs/decisions.md` (#1446).

The reference changes only through a recorded decision, and an option enters
the core with the reference's value for it recorded as one
(`CLAUDE.md`, "The design, in one picture").
"""

import re

from _repo import ROOT, needs_repo
from sverify.routes import _options_json


@needs_repo
def test_every_option_is_named_in_the_decision_record() -> None:
    record = (ROOT / "docs" / "decisions.md").read_text()
    named = set(re.findall(r"`([a-z][a-z_0-9]*)`", record))
    options = {o["id"] for o in _options_json()["options"]}
    assert options, "the checker reports no options"
    assert not options - named, (
        f"options docs/decisions.md does not name: {sorted(options - named)}"
    )
