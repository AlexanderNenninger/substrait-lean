---
name: write-docs
description: Write, edit, review or audit sverify's documentation so it is accurate, consistent across pages and easy to follow. Use for any change to a README (`README*`, `*/README.md`), a page in `docs/`, a markdown cell of the tour's notebooks (`notebooks/`), or a Python docstring (Great Docs builds the API reference from them). Covers the reader and task, the document type, one home per concept, verifying claims, the voice, a fresh review and the checks before handing back. Not for the generated tables CLAUDE.md lists, or for upstream reports (`upstream-report`).
---

# Write docs

Sverify's docs serve a data engineer who wants a plan proved before it runs,
and the contributors who extend the model. This skill holds the workflow; the
rules it applies are in three reference files:

- [reference/voice.md](reference/voice.md): voice, headings, formatting and
  notebooks. This is the one copy of the voice rules; CLAUDE.md's Voice
  section points here.
- [reference/words.md](reference/words.md): words and patterns to remove.
- [reference/document-types.md](reference/document-types.md): README,
  tutorial, how-to, reference and explanation (Diátaxis), and what each
  holds.

## Scope

In: the READMEs, `docs/*.md`, the tour's markdown cells (`notebooks/0*.py`)
and docstrings, which are the API reference's source.

Out:

- the generated sections CLAUDE.md lists under "Generated files" (the
  coverage table, the catalogue stats, `docs/realizability.md`,
  `upstream/REPORT.md`, `docs/ledger.md`, the replay summary). Edit their
  sources, never the output;
- upstream bug reports and community posts: the `upstream-report` skill;
- `CHANGELOG.md`: a feature PR adds a fragment to `changelog.d/` (its README).

## Workflow

### 1. Reader and task

Write one sentence before drafting: who reads this page and what they can do
once they have read it. "A data engineer with a dbt project checks its tests
with sverify-dbt." Every paragraph serves that sentence; one that serves
another reader goes to another page.

### 2. Document type

Pick one type from [reference/document-types.md](reference/document-types.md)
and keep the page to it. A tutorial links out for explanations, a reference
page gives no walkthrough. A page that mixes two types is two pages.
`docs/README.md` maps every page of `docs/` and every notebook to its type,
once: a new page gets its row there (`tests/test_docs_pages.py` checks it).

### 3. Search for existing coverage

Before writing a concept, find where it is already said:

```bash
git grep -n -i "<term>" -- README.md '*/README.md' docs/ notebooks/ python/src/sverify
```

Search for the synonyms too, and read `docs/README.md`'s map for the page
that should be the concept's home.

### 4. One home per concept

Each concept has one home page, which states it in full. Elsewhere:

- link to the home page where a link serves the reader;
- restate it only when this page's reader needs it here, at a different
  depth, framing or example, with a link to the home page;
- every instance agrees with the home page. A change to a fact updates every
  instance in the same change.

### 5. Terminology

`docs/core-semantics.md`'s [Terminology](../../../docs/core-semantics.md#terminology)
section is the one home of sverify's terms: the core, the reference
profile, engine profiles, the Substrait profile, translations. Use one word
per concept, the word that section uses, in Lean, Python, docs and messages
alike. A term missing there goes to the coordinator, who decides whether it
joins that section; don't start a second list. A term the code spells
differently from the docs is a mismatch to report (step 6).

### 6. Verify every claim

Code, tests and CI are the source; the docs follow them.

- Run every example and paste its real output. Never write output by hand.
- Copy identifiers, flags, paths and messages from the source itself.
- Link a claim about an objective fact to what supports it: a doc, test,
  issue, table or number.
- Add no fact you cannot support. State a limit as a fact with its link
  ("Sverify refuses window frames over `RANGE` of doubles (#NNN)").
- A statement bound to a version or date carries it ("DuckDB 1.4").
- Where code and docs disagree, report it to the coordinator with both
  sides. Don't decide which one is right in a docs change.

### 7. Draft

Write in the voice of [reference/voice.md](reference/voice.md). A page helps
its reader when it:

- says first what the reader gets and what they need;
- gives a working example early, with the expected output after each command;
- runs its steps in the order the reader takes them, with each condition
  before its instruction ("If the plan reads Parquet, …");
- has headings a reader can scan to find their part;
- names the common errors and their fixes;
- keeps one idea per sentence;
- ends with the next step.

Then strike what [reference/words.md](reference/words.md) lists.

### 8. Fresh review

Hand the draft to a reviewer who has not seen your reasoning: a subagent
given only the three reference files, this workflow's step 7 and the page
(or the diff). It marks each problem with its line and the rule it breaks,
and changes nothing. Rewrite from its marks; where you disagree with a mark,
keep your text and say why in your report.

### 9. Checks

Run the docs tests before handing back, from `python/`, through `local-run`
(CLAUDE.md, "Check capacity"):

```bash
.venv/bin/pytest tests/test_docs_pages.py tests/test_retired_phrases.py -n 0
```

`test_docs_pages.py` checks the site's pages, their links and
`docs/README.md`'s map; `test_retired_phrases.py` that no page repeats the
wording of a superseded decision. Where the change touches more, run its
checks too:

- a page with Python examples: `tests/test_readme.py`, which runs them and
  checks the page's length;
- a docstring or a notebook: `.venv/bin/poe fmt` and `.venv/bin/poe lint`;
- a notebook: `.venv/bin/poe notebooks`, which checks the tour with marimo
  and runs each notebook headless.

### 10. Checklist and report

Before handing back, check each item:

1. The reader-and-task sentence holds for every section.
2. The page keeps to one document type.
3. Each concept has one home; every restatement links to it and agrees.
4. Every term is the one `docs/core-semantics.md`'s Terminology uses.
5. Every example ran, and its output is pasted from the run.
6. Every identifier is copied from the source; every factual claim links its support.
7. The voice rules hold, and nothing from the word list remains.
8. Headings and formatting follow [reference/voice.md](reference/voice.md).
9. A notebook keeps its opening, its "we" and "you", and its closing link.
10. The fresh reviewer's marks are resolved or answered.
11. The docs tests pass.

Then report: what changed and why, the pages touched, the duplicates cut or
kept (with the reason for each kept one), and anything not verified.

## Auditing pages

An audit (for example a voice pass over every page, #754) proposes before it
changes:

1. List the pages and the type of each.
2. Map each concept to the pages that state it, and note what each instance
   adds.
3. Mark the instances that add nothing, disagree with the home page or lack
   a link to it.
4. Give a table: concept, home, instances, what each adds, action.
5. After approval, apply one concept at a time. Move a fact found only in an
   instance to the home page before cutting the instance.

## Questions

Terminology choices, a code and docs disagreement, or a page whose home is
unclear go to the coordinator. Look up a decision in `docs/ledger.md` first.
