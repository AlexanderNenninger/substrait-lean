# Pipelines

[![Open in GitHub Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/AlexanderNenninger/sverify-pipelines)

Data pipelines you can build from your phone and trust to run. You ask for
a table, Claude writes the pipeline and opens a pull request, and
[sverify](https://github.com/AlexanderNenninger/substrait-lean) proves its
contract before any data moves. Merging deploys it; GitHub Actions refresh
it on a schedule and publish a catalog of what's stored. Everything runs on
GitHub.

The worked example, [`pipelines/gdp.py`](pipelines/gdp.py), keeps GDP and
its components from Eurostat's `nama_10_gdp` up to date, with a key of
`(geo, unit, na_item, time)` and the values and flags checked on every
refresh.

## First run

1. Use this template (the green button) to create your repository.
2. Settings, Pages, Source: GitHub Actions.
3. Actions, refresh, Run workflow. It writes the tables to the `data`
   branch, then the `pages` workflow publishes the catalog at
   `https://<you>.github.io/<repository>/`, one page per table with what
   sverify proved, its lineage, its freshness, a chart and a query box.
4. Protect `main`: Settings, Rules, a ruleset for the default branch that
   requires a pull request and the `check` status check. Merging is then
   the approval of a proved contract.

From then on, `refresh` runs daily ([`refresh.yml`](.github/workflows/refresh.yml)),
and a failed refresh opens an issue labelled `pipeline-alert` that the
next good refresh closes ([`alerts.yml`](.github/workflows/alerts.yml)).

## A pipeline from your phone

Open Claude Code in the Claude app, pick this repository and ask: "Add a
pipeline for Eurostat's unemployment rate by country, `une_rt_a`, with one
row per country, age, sex, unit and year." Claude probes the source, writes
`pipelines/<name>.py`, runs `sverify check` until it is proved, and opens a
pull request. On the pull request:

- `check` comments the contract in plain words: what the output guarantees,
  what each refresh checks on the data, and what is not proved;
- `preview` runs the pipeline on the real source into `staging/pr-<n>/` and
  links a preview catalog. Its data goes when the pull request closes.

Merge it, and the next `refresh` builds the production tables from `main`.
When an alert issue opens, ask Claude to fix it from the issue's link.

## Using Claude

- Claude Code in the Claude app (mobile and web), the primary path:
  connect GitHub once and Claude Code works on this repository in a cloud
  sandbox. It comes with paid Claude plans and needs no API key.
  [`CLAUDE.md`](CLAUDE.md) and the skills in [`.claude/skills/`](.claude/skills)
  teach it the loop: probe, write, `sverify check --json`,
  `sverify check --fix`, summary, pull request. Give the cloud
  environment network access to your sources.
- The Claude GitHub app and Action, the secondary path: mention `@claude`
  in an issue or pull request ([`claude.yml`](.github/workflows/claude.yml)).
  Install the app and add a repository secret, `ANTHROPIC_API_KEY` or
  `CLAUDE_CODE_OAUTH_TOKEN`.

Without Claude, everything else runs on pipelines you write: check,
preview, refresh, alerts and the catalog. Run `pytest` before a pull
request; [`tests/`](tests/test_pipelines.py) runs the workflows' steps on
a recorded response.

## Where the data lives

Everything in your repository, the default: Delta tables on the `data`
branch, `production/` and `staging/pr-<n>/`. It suits small public
datasets. Its limits:

- GitHub refuses files over 100 MB and asks to keep a repository under a
  few GB ([GitHub's limits](https://docs.github.com/en/repositories/working-with-files/managing-large-files/about-large-files-on-github));
- each refresh adds a commit. The `data` branch is squashed into one commit
  after 30 (`SVERIFY_SQUASH_AFTER`), and each table keeps 7 days of Delta
  history (`SVERIFY_KEEP_DAYS`);
- the tables are as public as the repository. A public repository's
  catalog reads the `data` branch's files; a private one's carries a copy.

For enterprise: your store, your catalog, your orchestrator, with GitHub
as the control plane for pull requests, checks, approvals and alerts. Your
bucket on S3, R2, GCS, Azure or MinIO is reached through OIDC with
short-lived credentials, switched by the repository variables
`SVERIFY_STORE` and `SVERIFY_BUCKET`. Same workflows, same catalog.
[`docs/for-enterprise.md`](docs/for-enterprise.md) has the setup, and the
variants coming next: AWS, Google Cloud and Azure end to end, and the
refresh as a job in your cloud next to the bucket (`where: cloud-job` in
[`refresh.yml`](.github/workflows/refresh.yml), once the sverify container
image exists, [#770](https://github.com/AlexanderNenninger/substrait-lean/issues/770)).

## Stages and credentials

- The pull request branch is staging. `preview` runs in the GitHub
  environment `staging`, whose credentials write only `staging/`.
- Merging into `main` is the promotion. `refresh` runs the same code from
  `main` in the environment `production`, the only one that writes the
  production tables. Add required reviewers to `production` to approve
  each run from the GitHub app.
- A Claude Code session holds no lake credentials and reads only public
  sources while it probes.

## Files

- `pipelines/`: the pipelines; `_eurostat.py` and `_lake.py` are helpers.
- `pipelines.toml`: what `refresh` runs and what the catalog says.
- `scripts/lake.py`: the steps the workflows run (check, refresh, catalog).
- `catalog/`: the catalog's style and its DuckDB-WASM query box.
- `tests/`: the workflows' steps on recorded data.
