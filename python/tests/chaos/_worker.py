"""One process of a chaos test: build the job over a world, arm the faults
given, refresh once, and exit. Run by `_proc.run_worker`.

    python _worker.py '<json spec>'

The spec: `root`, `setup` (`_world.Setup`'s fields), `storage` (optional)
and `faults` (each `Faults.arm`'s arguments, with `point`). Exit status 0:
the refresh succeeded; 3: it raised, and the error is on stderr; a SIGKILL
fault ends the process with -9.
"""

import json
import sys
import traceback
from pathlib import Path

from _faults import Faults
from _world import Setup


class _Patch:
    def setattr(self, target: str, value: object) -> None:
        module, name = target.rsplit(".", 1)
        setattr(__import__(module, fromlist=[name]), name, value)


def main(spec: dict) -> int:
    setup = Setup(**spec["setup"])
    setup.use(_Patch())
    world = setup.world(Path(spec["root"]), storage=spec.get("storage"))
    job = world.job()
    faults = Faults()
    for f in spec.get("faults", []):
        f = dict(f)
        if f.get("barrier"):
            f["barrier"] = Path(f["barrier"])
        faults.arm(f.pop("point"), **f)
    try:
        out = job.refresh()
    except Exception:  # noqa: BLE001
        traceback.print_exc()
        return 3
    print(json.dumps({w.contract.view: w.mode for w in out.writes}))
    return 0


if __name__ == "__main__":
    sys.exit(main(json.loads(sys.argv[1])))
