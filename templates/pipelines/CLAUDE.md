# Pipelines with sverify

This repository holds data pipelines that sverify proves before they run.
Each file in `pipelines/` reads sources, applies transforms with contracts
(`@sv.transform(requires=..., ensures=...)`) and stores the results in Delta
tables (`sink(...)` from `pipelines/_lake.py`). GitHub Actions prove them on
every pull request, preview them on staging data, refresh them on `main` and
publish a catalog. The skills in `.claude/skills/` document sverify's API:
read `sverify` first, `sverify-pipelines` for sources, sinks and refresh.

## The loop

When asked for a pipeline or a change to one:

1. Probe the source. Fetch a small sample (a few hundred rows) and look at
   its columns, types, keys, NULLs, ranges and odd values. Write down what
   the data guarantees; these become `requires=`.
2. Write the pipeline in `pipelines/<name>.py`: a source, one or more
   `@sv.transform`s, `.write(sink("<table>"))` for each stored table. Follow
   `pipelines/gdp.py`. State in `ensures=` what consumers rely on: keys
   (`sv.unique(...)`), NOT NULL, ranges, allowed values.
3. Register it in `pipelines.toml`: a `[[pipeline]]` with the file and the
   nodes to refresh (the last stored node of each chain), and a
   `[table.<name>]` with a title, a description, the source and a chart.
4. Run `sverify check pipelines/<name>.py --json`. Exit 0 means proved.
   Otherwise read each finding's `code` (`sverify explain <code>`):
   - `needs`: run `sverify check pipelines/<name>.py --fix`, which adds
     the preconditions the proof needs to `requires=`. Keep only those the
     source really guarantees (step 1); otherwise change the transform.
   - `may_be_false` with a counterexample: the transform can break its
     promise on such rows. Fix the transform (filter, coalesce, bound) or
     weaken `ensures=` if the promise was wrong.
   - `unsupported` (exit 3): a construct sverify can't prove; rewrite it
     with the constructs the `sverify` skill lists.
   Repeat until it exits 0.
5. Add a recorded sample of the source to `tests/fixtures/` and run
   `pytest` (it runs the workflows' steps offline, `EUROSTAT_FIXTURES`
   style: a source reads its fixture when an environment variable is set).
6. Open a pull request. Its description is the contract in plain words:
   what the output guarantees, what each refresh checks on the data, and
   what is not proved. The `check` workflow comments the same, and
   `preview` runs the pipeline on the real source into staging.

## Rules

- Never put a `refresh()` call at a file's top level: `sverify check`
  imports the file. Use `if __name__ == "__main__":` for local runs.
- Declare each source's schema, so `sverify check` reads no data.
- Don't write credentials into files. Stores and their credentials come
  from the environment (`SVERIFY_LAKE`, OIDC in the workflows). A source
  that needs a token names it: a line in `.github/workflows/lake.yml` maps
  the secret to an environment variable, and the pipeline reads it by
  name (docs/for-enterprise.md, "Source tokens").
- This session has no lake credentials: probe public sources only, and let
  the `preview` workflow run the pipeline.
- Don't edit `_data/` or the `data` branch by hand; the workflows own them.
- An alert issue (label `pipeline-alert`) carries the failing refresh's
  error. Reproduce it with the fixture or a fresh sample, fix the pipeline
  or its `requires=`, and open a pull request that closes the issue.
