# sverify check

A composite GitHub Action that runs `sverify check --format sarif` on each target with the default
30 s timeout, merges the logs into one SARIF run and uploads it to code scanning. The job exits
with the worst code of the targets'. [Checking without running, and the command line](../../docs/how-to-command-line.md#in-github-actions)
has an example and the inputs.

## Versions

`version` is the sverify the action installs from PyPI. It defaults to the latest release; the
action and the package are tagged together at 1.0.

| Input | Needs sverify |
|---|---|
| `targets`, `timeout`, `extras`, `upload` | 0.8.0 |
| `require-proved` | 0.9.0 |

`require-proved` checks the installed version first and fails once, naming the minimum, where the
CLI would exit 2 for every target. `source` installs something else (a wheel or a checkout), for
testing a build.
