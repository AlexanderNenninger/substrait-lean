"""Running `_worker.py` in a fresh process."""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

HERE = Path(__file__).parent
TESTS = HERE.parent


@dataclass
class Done:
    status: int
    out: str
    err: str

    @property
    def killed(self) -> bool:
        return self.status == -9

    def where(self) -> str:
        """The innermost frame of sverify's code in the traceback on stderr."""
        frames = re.findall(r'File ".*?/sverify/([^"]+)", line \d+, in (\S+)', self.err)
        frames = [f for f in frames if not f[0].startswith("_dev")]
        return f"sverify/{frames[-1][0]}:{frames[-1][1]}" if frames else "?"


def env() -> dict[str, str]:
    path = os.pathsep.join([str(HERE), str(TESTS), os.environ.get("PYTHONPATH", "")])
    return {**os.environ, "PYTHONPATH": path}


def start(spec: dict) -> subprocess.Popen:
    return subprocess.Popen(
        [sys.executable, str(HERE / "_worker.py"), json.dumps(spec)],
        env=env(),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )


def wait(p: subprocess.Popen, timeout: float = 300) -> Done:
    out, err = p.communicate(timeout=timeout)
    return Done(p.returncode, out, err)


def run_worker(spec: dict, timeout: float = 300) -> Done:
    return wait(start(spec), timeout)
