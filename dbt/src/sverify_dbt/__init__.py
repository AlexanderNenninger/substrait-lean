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

from sverify_dbt.check import check
from sverify_dbt.manifest import Project, ProjectError, load
from sverify_dbt.result import CheckResult, ContractIssue, ModelResult, Needed, TestResult

__all__ = [
    "CheckResult",
    "ContractIssue",
    "ModelResult",
    "Needed",
    "Project",
    "ProjectError",
    "TestResult",
    "check",
    "load",
]
