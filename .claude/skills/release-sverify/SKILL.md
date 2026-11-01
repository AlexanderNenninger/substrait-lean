---
name: release-sverify
description: Release a new version of sverify to PyPI, with its docs site and molab notebooks. Use when asked to release, publish or tag a version (e.g. "release 0.3.0", "cut a release", "publish to PyPI"), or to check on or repair a release that's in progress. Covers the readiness check, the version-bump PR, the v* tag that triggers the Wheels and Docs workflows, and the checks afterwards.
argument-hint: "Optional: the version to release (e.g. 0.3.0)"
---

# Release sverify

A release is a `v<version>` tag on `main`. The tag triggers two workflows:

- **Wheels** (`.github/workflows/wheels.yml`):
  1. `build` builds the wheels for Linux and macOS and an sdist.
  2. `test-pythons` tests the installed wheel on Python 3.12–3.15.
  3. `publish` uploads to PyPI (`pypi` environment), after checking that the tag matches `python/pyproject.toml`'s version.
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
```

- **Open PRs:** ask which belong in the release. Those must merge first.
- **`main`'s CI** must be green on the commit that will be tagged.
- **`CHANGELOG.md`** has an `## <version> (unreleased)` section covering what's merged since the last tag (`git log v<last>..origin/main --merges --oneline`). If the release breaks the public API, it lists the moves.
- **Pages** must be turned on with "GitHub Actions" as the source. If `build_type` isn't `workflow`, ask the user to turn it on.
- **Version:** if the user gave none, propose one by [semver](https://semver.org) for 0.x: minor for new features or breaking changes, patch for fixes only.

## 2. Version-bump PR

`main` only accepts changes through PRs with a passing `qa` check, so the bump is a PR:

```bash
git switch -c release-<version> origin/main
# python/pyproject.toml: version = "<version>"   (the only place the version is written)
# CHANGELOG.md: "## <version> (unreleased)" -> "## <version> (<YYYY-MM-DD>)"
cd python && uv lock && cd ..        # updates only sverify's own version in uv.lock
git diff --stat                      # exactly these three files
git commit -am "Release <version>"
git push -u origin release-<version>
gh pr create --base main --title "Release <version>" --body "…"
```

In the PR body, say what the tag will trigger. Once `qa` is green, merge it (`gh pr merge <n> --merge`), or ask the user to.

## 3. Tag

Only after the user says to release:

```bash
git fetch origin
git show origin/main:python/pyproject.toml | grep '^version'   # must be <version>
gh run list --workflow ci.yml --commit "$(git rev-parse origin/main)"
git tag -a v<version> <merge-commit-sha> -m "sverify <version>

See CHANGELOG.md."
git push origin v<version>
gh run list --branch v<version>                                # Wheels and Docs started
```

Tag the release PR's merge commit by its SHA, not whatever `main` is by then. If CI on the merge commit is still running, it's acceptable to tag when the commit before it passed and the merge only changes the three version files. Say so to the user.

## 4. Afterwards

The macOS wheel jobs can wait a long time for runners, so the publish may take a while. Don't poll in a loop. Check when asked, or on the next wake-up.

- **Wheels:** every job green, then `pip index versions sverify` (or <https://pypi.org/project/sverify/>) shows the version.
- **Notebooks:** the `published` branch has a commit for the version. Ask the user to open one notebook from it on molab and press Run, since CI can't check that molab installs and runs it.
- **Docs:** <https://alexandernenninger.github.io/substrait-lean/> shows the version, and its Skills page lists the skills.
- Optionally create the GitHub release from the changelog section: `gh release create v<version> --notes-file <section>`. Ask first, since it notifies watchers.

## When something fails

- **`publish` says the tag doesn't match the version:** the bump didn't land in the tagged commit. Nothing was uploaded. Delete the tag (`git push origin :refs/tags/v<version>` and `git tag -d v<version>`), fix it, and tag again. Ask the user first, since deleting a pushed tag is visible.
- **`build` or `test-pythons` fails:** nothing was uploaded. Fix it on `main` through a PR, then either re-run the workflow, if the fix doesn't change the tagged code, or release the next patch version. Don't move a tag that others may have fetched without asking.
- **`publish` succeeded but `publish-notebooks` failed:** PyPI already has the version, so don't re-tag. Re-run only the notebook publish with **Actions → Wheels → Run workflow** and `notebooks: <version>` (`dry_run: true` first, to check without pushing).
- **Docs failed:** re-run the Docs workflow on the tag (`workflow_dispatch`). The package itself is unaffected.
- **A broken release is already on PyPI:** release a fixed patch version. Yanking (`pip`'s yank on PyPI) is for the user to decide.
