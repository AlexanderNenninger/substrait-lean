"""Check a dbt project's tests and model contracts with sverify, before the
models run.

    import sverify_dbt

    result = sverify_dbt.check("path/to/project")   # after `dbt compile`
    print(result)
    result.write_selectors("path/to/project/selectors.yml")

Each model's compiled SQL is proved with `sverify.verify` against the tests
on the models and sources it reads. A test proved there holds on every run
whose inputs pass their tests, so `dbt build` may skip it
(`dbt build --exclude selector:sverify_proved`).
"""

from importlib.metadata import PackageNotFoundError, version

import sverify

try:
    __version__ = version("sverify-dbt")
except PackageNotFoundError:  # run from a source tree, not installed
    __version__ = sverify.__version__
if sverify.__version__ != __version__:
    raise ImportError(
        f"sverify-dbt {__version__} needs sverify {__version__}, found {sverify.__version__}: "
        f"pip install sverify-dbt=={__version__} sverify=={__version__}"
    )

from sverify_dbt.check import check  # noqa: E402
from sverify_dbt.manifest import Project, ProjectError, load
from sverify_dbt.result import CheckResult, ContractIssue, ModelResult, NeededTest, TestResult

__all__ = [
    "__version__",
    "CheckResult",
    "ContractIssue",
    "ModelResult",
    "NeededTest",
    "Project",
    "ProjectError",
    "TestResult",
    "check",
    "load",
]
