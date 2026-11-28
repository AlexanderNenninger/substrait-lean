# Document types

Sverify's docs follow Diátaxis: each page is one of four kinds, plus the
READMEs that open each part. `docs/README.md` maps every page of `docs/` and
every notebook to its kind, once, and `tests/test_docs_pages.py` checks the
map. Pick the kind before drafting and keep the page to it.

## README

The entry to a part of the repository: `python/README.md` for users (the
site's landing page), `README.md` for contributors, `dbt/README.md` for
sverify-dbt, `templates/pipelines/README.md` for platform teams.
`python/README.md` stays under 90 lines, two screens (`tests/test_readme.py`).

- What the part does, in two or three sentences, for its reader.
- Install and a first working example with its output.
- Links into the tutorial, the how-to guides and the reference. The details
  live there.

## Tutorial

Teaches by doing, start to finish: `docs/getting-started.md` and the tour
(`notebooks/0*.py`).

- One path that works, from a clean start to a result the reader sees.
- Every step runs, and shows its output.
- No choices and no alternatives along the way.
- A tutorial links out for explanations. The why goes to an
  explanation page, the options to the reference.
- It ends with what the reader can now do and the next page.

## How-to guide

Solves one task for a reader who already knows the basics:
`docs/how-to-*.md`, indexed by `docs/tasks.md`.

- The title names the task.
- What the reader needs first, then the steps in order, each condition
  before its instruction.
- The common errors and their fixes.
- No teaching and no background beyond a link.
- At most 600 lines, as a tutorial page; `tests/test_readme.py` runs the
  page's Python examples and checks the length.

## Reference

States the facts, to look up: the API reference (built from the
docstrings), `docs/reference-semantics.md`, `docs/stability.md` and the
ledgers.

- Complete and accurate, in the order a reader looks things up (by name,
  by function, by engine).
- Structure mirrors the thing described; one entry has one shape.
- Short examples of use, no walkthroughs.
- Generated parts are edited at their source (CLAUDE.md, "Generated files").

## Explanation

Says how and why: the design, the core and its profiles, what the checker
proves (`docs/core-and-profiles.md`, `docs/what-sverify-proves.md`,
`docs/engine-profiles.md`). The pages for contributors
(`docs/core-semantics.md`, `docs/decisions.md`) are explanations too.

- Context, reasons and the alternatives weighed, with links to the
  decisions and the proofs.
- No step-by-step instructions; link the how-to guide.
- The pages for contributors keep decision numbers and issue links, as
  records of the design. The user pages leave them out.
