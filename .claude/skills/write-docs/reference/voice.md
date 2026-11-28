# Voice

The READMEs, `docs/`, the tour's markdown cells (`notebooks/`) and the
docstrings share one voice: light, direct and concise. This file is the one
copy of the rules; CLAUDE.md's Voice section summarizes them and points here.

## Sentences

- Sverify is the subject ("Sverify proves…"). Write "Sverify" at the start of
  a sentence and `sverify` for the package elsewhere.
- Present tense and active voice: "The checker refuses the plan".
- Plain verbs: "is", "are", "has". Drop "serves as", "stands as",
  "boasts", "features" and "offers".
- No bold, emojis, exclamation marks, "simply" or "just".
- No filler and no hedges. A claim that holds under a condition states the
  condition.
- No opposing pairs ("X, not Y", "proved, not tested", "instead of"). State
  the claim and stop.
- Claims about objective facts link to what supports them: a doc, test,
  issue, table or number.
- Keep every fact, identifier, link and number when rewriting.
- Dashes only in code and ranges (`1–3`). Use a comma, colon, semicolon or
  parentheses in prose.
- Vary sentence length. A run of sentences of one length and one shape
  reads as a template.

## Headings

- Sentence case: "Running it in production".
- A heading names what its section holds. No heading starts with "The".
- One top-level heading per page, and the first sentence doesn't repeat it.
- No horizontal rules between sections.

## Formatting

- Code font for identifiers, paths, commands, flags, options and UI names.
- Prose when a list would only hold labels. A list holds parallel items of
  a sentence or more, or steps in order.
- Link text says where it goes: "[the reference's tie order](…)", never
  "here" or "this page".
- Code blocks carry their language (`bash`, `python`, `sql`, `text` for
  output). An example a reader copies is run by a test or comes from one.
- Images have alt text that says what the image shows.
- Straight quotes (`"`, `'`).

## Docstrings

Docstrings are the API reference (Great Docs builds it from them,
`python/great-docs.yml`). The voice applies, with these additions:

- The first line says what the function does or what the object is, in one
  sentence.
- Parameters, return value and raised errors go in Google-style `Args:`,
  `Returns:` and `Raises:` sections, as the package's docstrings do. Copy the
  names from the signature.
- User-facing docstrings carry no D-numbers or internal issue history; they link
  to the user doc.

## Notebooks

The tour (`notebooks/0*.py`) speaks to the data engineer with a stake in the
outcome.

- An opening of two or three sentences in the second person that sets the
  scene and the stakes (the customer charged twice, whoever gets paged at
  3 a.m.), then the rule or feature.
- Walkthrough steps say "we": "We'll write the rule in Ibis, state what it
  assumes and what it promises, and have the checker prove it before any data
  runs." Openings and recaps speak to the reader as "you".
- A closing paragraph about what the reader can now do, leading into the
  next notebook with its link. No humour.
- Prose cells point to the reference page for the details.
- Each notebook runs headless from a fresh start (`poe notebooks`).

An opening: "Say you're on the payments team. A customer was charged twice for
the same coffee, and by the time support hears about it, they've already
tweeted. You want to catch these double charges, the same card paying the
same amount at the same merchant twice within five minutes, and refund them
first."
