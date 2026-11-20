# How this project is built

Almost all of the code, the proofs and the text in this repository were
written by Claude Code, Anthropic's coding agent. One maintainer sets the
direction, decides what the reference semantics does, reports bugs upstream
and merges. This page says who does what, what you can check without
trusting either, where a person's judgement enters, and how to disagree.

## Who does what

The maintainer decides what sverify is for and signs every decision that
changes the reference semantics. Each is an entry of the
[decision log](decisions.md), with its date and its reasoning. The
maintainer also files each [upstream report](../upstream/README.md) and
merges the pull requests.

Claude Code sessions write the Lean definitions and proofs, the Python,
the engine facts and the docs. A coordinator session assigns work to the
others and merges green pull requests through batches. A theory advisor
session answers design questions about the semantics, and reviewer
sessions read each pull request before it merges. A session starts from an
issue with an acceptance, and its pull request says what it measured
before and after ([CLAUDE.md](../CLAUDE.md) holds the rules every session
follows).

Most of the text here was written by agents. Read it as you would read a
colleague's draft: the claims worth relying on link to something you can
check.

## What you can check without trusting anyone

- The theorems. The Lean kernel checks every proof. [trusted-base.md](trusted-base.md)
  lists what it does not check: the project's one axiom, the `opaque` and
  `implemented_by` constants, what tests cover and what nothing covers. A
  test fails when a new one appears without a row there.
- The engine facts. Each fact records its evidence (a probe, a fuzz run, an
  engine test or the source) with the engine's version, and
  [`sverify_dev.facts`](../python/tools/sverify_dev) checks the documents and which rows of the
  engine tables they settle (`tests/test_facts.py`).
- The goldens. The checker's answers to contract requests and the plans it
  writes are pinned in [`tests/`](../tests), and CI runs them on every pull
  request that can change them.
- The upstream ledger. Each entry in [upstream/](../upstream/REPORT.md)
  names the version it reproduces on and carries the repro.

## Where a person's judgement enters

- The decisions. Where the reference could take two values, a person
  chooses and the log says why ([decisions.md](decisions.md)).
- The engine facts' provenance. A fact says whether it was probed, read
  from documentation or inferred, and a person decides which evidence wins
  when they disagree.
- What sverify refuses. A construct the proof can't cover is refused with
  its exit; a person decides which refusals stay short and enumerable
  ([rejections.md](rejections.md)).

## How a change lands

1. An issue states the change and its acceptance.
2. A pull request carries the change, the measured improvement to the area
   it touches, and an answer to "how do we teach this" ([the template](../.github/pull_request_template.md)).
3. CI builds the proofs with warnings as errors, runs the tests, the engine
   jobs and the notebooks.
4. A reviewer session labels the pull request, and the coordinator merges
   it in a batch.
5. Generated tables are rewritten on main after each merge.

## How to disagree

If a theorem says less than its name suggests, a fact is wrong or a
decision looks wrong, open an issue and name the page. A theorem that turns
out false is not weakened until it passes: the statement is corrected with
a side condition named as a predicate, and the pull request says what was
false. A wrong fact is superseded by a new one that records the old. A
wrong decision gets an `Amended` or `Superseded` line in the log, and the
rule is stated once, in the later decision.
