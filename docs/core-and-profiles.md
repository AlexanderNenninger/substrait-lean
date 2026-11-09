# The core and the profiles

Sverify proves things about an idealised machine, the core. Every real
system it knows, the reference, each engine and Substrait, is that machine
with its options narrowed: a profile. This page says what the core is, which
profiles sverify ships, and how they relate.
[reference-semantics.md](reference-semantics.md) states what each option
does under the reference.

## The core: an abstract machine

The core runs no plan. It is a specification of every behaviour sverify
admits: every point where engines or Substrait differ is an option, and the
core allows every value of every option at once. Integer overflow may
raise, wrap or saturate there; `-0.0` and `0.0` may be one value or two;
a sum of doubles may add in any order.

The core works on the full value space. A double is an IEEE 754 binary64
code, `-0.0` and the negative NaN included, and `+ - × ÷` are the exact
result rounded once. The core is a formal Lean specification in `core/`,
and it holds no engine's workaround: no shim, no quirk, no engine version.

## A profile: the core narrowed

A profile picks, for each option, the behaviours it allows: whether
`-0.0` is a value of its own (`zero_sign`), how NaN compares
(`nan_equality`, `nan_order`), what a sum of doubles may return
(`sum_order`), and so on. Every result a profile allows, the core allows,
and Lean proves it ([the proofs](proofs.md)), so a fact proved under the core holds under every
profile.

Some options stay open in a profile too. The reference fixes no order
among tied rows (`tie_order`, `tie_pick`) and no order of a sum of doubles
(`sum_order`); a result under it is any one the open options allow. Sverify
proves that a result is among the allowed ones, and a contract over a plan
with open options holds for every one of them.

## The reference profile

The reference is the profile plans are verified under
by default. It belongs to no engine.

- It is strict where engines disagree. Integer overflow, division by zero,
  a domain error, a double operation that overflows to `±∞` or creates a
  NaN, an out-of-range cast or date: each raises. A proved plan's
  preconditions, stated or inferred, rule these out, so the plan never
  reaches them on any engine.
- Where it picks a value, it picks one every engine gives natively or with
  a cheap shim: one zero, one NaN that equals itself and sorts above every
  number, NULLs last in both directions where a sort key states no NULL
  order, truncating integer division.

Because the reference is strict, one proof carries to every engine:
sverify writes the plan for each engine with a shim wherever the engine's
value differs from the reference's, and the shims are proved
([Verifying: the two paths](verifying.md)).

## Engine profiles

Each engine has a profile of its own, stating what that engine computes,
built from its facts ([the ledgers](https://alexandernenninger.github.io/substrait-lean/ledgers/)).
The engine profiles are siblings: none refines another, and none refines
the reference.

| Profile | What it computes | Facts |
|---|---|---|
| DuckDB's | The reference's functions, except where DuckDB 2.0 was probed to differ on doubles and integers, under DuckDB's settings | [`engines/duckdb/facts/`](../engines/duckdb/facts/) |
| Polars's | The reference's functions, except integer `//` and `%`, which floor | [`engines/polars/facts/`](../engines/polars/facts/) |
| Spark's | The reference's functions, as the reference evaluates them; Spark's choices of the open options come from its facts | [`engines/spark/facts/`](../engines/spark/facts/) |

Snowflake has no profile in sverify: it runs the SQL sverify writes
([the engines](stability.md#engines)).

`semantics="duckdb"`, `"polars"` or `"spark"` verifies a plan under that
engine's profile. Under Spark's profile that is the same proof as under
the reference; what it changes is the route, which runs the plan on Spark
natively.

## Substrait's profile

Substrait's profile states Substrait's semantics as its extension YAMLs
give them: where a YAML lists the values of an option, the plan's choice
among them, or any of them where the plan states none; IEEE's two zeros and
signed NaNs; and the core's looseness wherever the YAMLs say nothing.
It is a sibling of the reference: the reference overrides Substrait in
places ([Overrides](reference-semantics.md#overrides)), so neither refines
the other. Lean proves that Substrait's profile refines the core
([the proofs](proofs.md)).
`semantics="substrait"` verifies a plan under it, and the
[spec-gap ledger](https://alexandernenninger.github.io/substrait-lean/ledgers/spec-gaps.html)
lists the options Substrait leaves open.

## Where engine behaviour lives

An engine's behaviour is stated once, in its profile and its facts. The
translation from the reference to an engine lives in that engine's
lowering, and a compensation in its shims. The core never mentions an
engine, so adding an engine adds a profile and its facts, and
changes no proof about the core.

[trusted-base.md](trusted-base.md) lists what each result rests on;
[engine-profiles.md](engine-profiles.md) has each engine's translation and
shims.

