---
name: release-sverify
description: Release a new version of sverify and sverify-dbt to PyPI, at one version, with the docs site and molab notebooks. Use when asked to release, publish or tag a version (e.g. "release 0.3.0", "cut a release", "publish to PyPI"), or to check on or repair a release that's in progress. Covers the readiness check, the version-bump PR, the v* tag that triggers the Wheels and Docs workflows, and the checks afterwards.
argument-hint: "Optional: the version to release (e.g. 0.3.0)"
---

# Release sverify

A release is a `v<version>` tag on a release branch, `release/<major>.<minor>`, cut from `main`. It releases two packages at that one version: `sverify` (`python/`) and `sverify-dbt` (`dbt/`, #732), which pins `sverify==<version>`. The tag triggers two workflows:

- **Wheels** (`.github/workflows/wheels.yml`):
  1. `build` builds sverify's wheels for Linux and macOS and an sdist; `build-dbt` builds sverify-dbt's sdist and wheel (pure Python) and runs its CLI against the Linux sverify wheel.
  2. `test-pythons` tests the installed wheel on Python 3.12–3.15.
  3. `publish` uploads both packages to PyPI (`pypi` environment), after checking that the tag matches `python/pyproject.toml`'s version, and that `dbt/pyproject.toml` has the same version and pins `sverify==<version>`.
  4. `publish-notebooks` rewrites the notebooks to pin that version from PyPI, runs them, and commits them to the `published` branch, where the README's molab links point.
- **Docs** (`.github/workflows/docs.yml`): builds the Great Docs site (API reference, agent skills, `llms.txt`) and deploys it to GitHub Pages.

**Publishing to PyPI can't be undone:** a version number can never be uploaded again. Never push a tag without the user's explicit go-ahead in this conversation.

## 1. Readiness check

Report each of these to the user before going on:

```bash
git fetch origin --tags
git tag --list 'v*' | sort -V | tail -3                       # last releases
sed -n 's/^version = "\(.*\)"/\1/p' python/pyproject.toml     # current version (on main)
gh pr list --state open                                       # anything meant to be in it?
gh run list --workflow ci.yml --branch main --limit 1         # main green?
gh api repos/AlexanderNenninger/substrait-lean/pages --jq .build_type   # "workflow"
gh api repos/AlexanderNenninger/substrait-lean/environments/github-pages/deployment-branch-policies \
  --jq '.branch_policies[]|"\(.type) \(.name)"'                  # must include "tag v*"
```

- **Open PRs:** ask which belong in the release. Those must merge first.
- **`main`'s CI** must be green on the commit that will be tagged.
- **`CHANGELOG.md`** gets the release's section from the fragments in `changelog.d/` (one file per PR; see its README), plus anything already under `## Unreleased`. Check them against what's merged since the last tag (`git log v<last>..origin/main --merges --oneline`). If the release breaks the public API, the section lists the moves.
- **Pages** must be turned on with "GitHub Actions" as the source. If `build_type` isn't `workflow`, ask the user to turn it on. Its `github-pages` environment must also allow `v*` tags to deploy: GitHub's default allows only `main`, and the deploy then fails with "Tag … is not allowed to deploy to github-pages due to environment protection rules". If the `tag v*` policy is missing, ask the user before adding it with `gh api -X POST …/environments/github-pages/deployment-branch-policies -f name='v*' -f type=tag`.
- **PyPI for sverify-dbt:** its first release needs a trusted publisher for the project `sverify-dbt` on PyPI (this repository, workflow `wheels.yml`, environment `pypi`), as `sverify` has; a pending publisher works before the project exists. Ask the user to add it if `pip index versions sverify-dbt` finds nothing and they haven't.
- **Engine packages** (`engines/<engine>/`, #1189): each goes out at sverify's version, and sverify's extras pin it (`sverify[polars]` pins `sverify-polars`), so a release whose engine packages are not on PyPI ships extras that cannot install. Refuse to tag until the repository variable `PUBLISH_ENGINES` is `true` (`gh variable get PUBLISH_ENGINES`): it says the user has added a trusted publisher on PyPI for each engine project, each with an environment of its own, since PyPI takes one pending publisher per repository, workflow and environment: `sverify-polars` → `pypi-polars`, `sverify-spark` → `pypi-spark`, `sverify-duckdb` → `pypi-duckdb` (owner `AlexanderNenninger`, repository `substrait-lean`, workflow `wheels.yml`; a pending publisher works before the project exists). `publish` uploads sverify from `pypi`, then `publish-engines` each engine package from its environment. If it is unset, tell the user which projects need a publisher, and set the variable only after they say it's done (`gh variable set PUBLISH_ENGINES --body true`). `publish` checks it too: without it, the tag publishes nothing.
- **Stability** ([docs/stability.md](../../../docs/stability.md)): every entry under "Breaking changes" has a migration note, what to write instead with an example, and a unit test of the old form; every soundness fix that refuses a proof names an engine fact or an upstream record. Within 1.x a break of the formats or a tightening of the reference semantics waits for 2.0, so hold back a PR that does either and tell the user.
- **Version:** if the user gave none, propose one by [semver](https://semver.org) for 0.x: minor for new features or breaking changes, patch for fixes only.

## 2. Release branch and version bump

Main never freezes for a release. Cut a release branch from main, and do all the release work there:

```bash
git fetch origin
git push origin origin/main:refs/heads/release/<major>.<minor>   # e.g. release/0.8
```

CI treats `release/*` as main: pushes to it and pull requests into it run everything. The batch merger keeps merging into main meanwhile; nothing reaches the release branch unless a PR targets it.

The version bump is a PR into the release branch:

```bash
git switch -c release-<version> origin/release/<major>.<minor>
# python/pyproject.toml: version = "<version>"
# dbt/pyproject.toml: version = "<version>", and the dependency "sverify==<version>"
# engines/polars/pyproject.toml: version = "<version>", and "sverify==<version>";
#   python/pyproject.toml's `polars` extra: "sverify-polars==<version>"
# CHANGELOG.md: rename "## Unreleased" to "## <version> (<YYYY-MM-DD>)", append the
#   changelog.d/*.md fragments (file-name order) under it, then git rm the fragments
#   (keep changelog.d/README.md)
cd python && uv lock && uv sync      # updates only sverify's own version in uv.lock
uv run python -m sverify_dev.formats tests/formats/<version>   # the formats this release writes
uv run pytest tests/test_formats.py && cd ..                     # every earlier release's still read
git add python/tests/formats/<version>
cd dbt && uv lock && cd ..           # sverify-dbt's and the sverify it pins
git diff --stat                      # these six files, the removed fragments and the fixtures
git commit -am "Release <version>"
git push -u origin release-<version>
gh pr create --base release/<major>.<minor> --title "Release <version>" --body "…"
```

A pull request into `release/*`, or from a `release-*` branch, runs the Wheels workflow's whole installed-wheel test, so a test the wheel fails shows up here. Merge the PR once it's green. Fixes the release needs go to the release branch the same way, as PRs into it.

## 3. Dry run, then tag

Before tagging, run the Wheels workflow by hand on the release branch. A manual run builds and tests every platform and Python version as a tag does, but never publishes, because only `v*` tags publish:

```bash
gh workflow run wheels.yml --ref release/<major>.<minor>
gh run list --workflow wheels.yml --branch release/<major>.<minor> --limit 1   # wait until green
```

Only after the user says to release, and with the dry run green:

```bash
git fetch origin
git show origin/release/<major>.<minor>:python/pyproject.toml | grep '^version'   # must be <version>
sha=$(git rev-parse origin/release/<major>.<minor>)
git tag -a v<version> "$sha" -m "sverify <version>

See CHANGELOG.md."
git push origin v<version>
gh run list --branch v<version>                                # Wheels and Docs started
```

Tag the commit the dry run tested.

Then merge the release branch back into main, so main gets the version, the folded changelog and any release fixes: open a PR from `release/<major>.<minor>` into `main` and merge it with a merge commit (it goes through a batch like any other). Keep the branch for patch releases (`<major>.<minor>.<patch+1>`): their fixes go into it by PR, and the same steps follow.

## 4. Afterwards

The macOS wheel jobs can wait a long time for runners, so the publish may take a while. Don't poll in a loop. Check when asked, or on the next wake-up.

- **Wheels:** every job green, then `pip index versions sverify` and `pip index versions sverify-dbt` (or <https://pypi.org/project/sverify/>, <https://pypi.org/project/sverify-dbt/>) show the version.
- **Notebooks:** the `published` branch has a commit for the version. Ask the user to open one notebook from it on molab and press Run, since CI can't check that molab installs and runs it.
- **Docs:** <https://alexandernenninger.github.io/substrait-lean/> shows the version, and its Skills page lists the skills.
- Optionally create the GitHub release from the changelog section: `gh release create v<version> --notes-file <section>`. Ask first, since it notifies watchers.

## When something fails

- **`publish` says `dbt/` is at another version, or doesn't pin this sverify:** the bump missed `dbt/pyproject.toml`. Nothing was uploaded; handle it as a tag that doesn't match.
- **`publish` says the tag doesn't match the version:** the bump didn't land in the tagged commit. Nothing was uploaded. Delete the tag (`git push origin :refs/tags/v<version>` and `git tag -d v<version>`), fix it, and tag again. Ask the user first, since deleting a pushed tag is visible.
- **`build` or `test-pythons` fails:** nothing was uploaded. If the failure is a flaky test and the tagged code needs no change, re-run the failed jobs (`gh run rerun <run> --failed`); a passing re-run publishes. Otherwise fix it on the release branch through a PR, run the dry run again, and tag the next patch version there. Don't move a tag that others may have fetched without asking.
- **`publish` succeeded but `publish-notebooks` failed:** PyPI already has the version, so don't re-tag. Re-run only the notebook publish with **Actions → Wheels → Run workflow** and `notebooks: <version>` (`dry_run: true` first, to check without pushing).
- **Docs failed:** re-run the Docs workflow on the tag (`workflow_dispatch`). The package itself is unaffected.
- **A broken release is already on PyPI:** release a fixed patch version. Yanking (`pip`'s yank on PyPI) is for the user to decide.
