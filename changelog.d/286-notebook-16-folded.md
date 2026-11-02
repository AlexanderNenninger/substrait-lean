### Chapter 16 of the tour folded into chapter 17

The tour's appendix on DataFusion's quirks (`16_datafusion_semantics.py`)
described DataFusion as the SQL frontend it no longer is (#211). Its parts
that still matter now live in chapter 17 (`17_backend_semantics.py`), as a
new section 8 on DataFusion as a backend: when DataFusion evaluates an
expression (E1–E5), and the soundness gaps found while sverify planned SQL
with DataFusion (D1–D11), each re-checked live against `verify` and the
model and ranked most severe first. Most of those gaps closed with the lift;
what remains is that DataFusion wraps integer overflow silently where the
model raises, which `verify` reports as `may fail: overflow`.
`catalogue/pitfalls.toml`'s `quirks` now name chapter 17's entries.
