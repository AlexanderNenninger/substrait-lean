# Changelog fragments

Each PR that changes something a user notices adds **one file here** instead of
editing `CHANGELOG.md`, so parallel PRs don't conflict at the top of the
changelog.

- **Name:** `<issue or PR number>-<short-slug>.md`, for example `257-no-new-nans.md`.
- **Content:** the entry exactly as it should appear under the release's
  heading, starting with a `### Title` line, in the CHANGELOG's style (what
  changed for the user, with issue links).
- **At release** (`.claude/skills/release-sverify/SKILL.md`): the fragments
  are appended in file-name order under the release's section of
  `CHANGELOG.md` and then deleted, in the version-bump PR.
