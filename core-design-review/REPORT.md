# The core design, read against the literature: gaps and how to close them

A review of the core design work of 2026-11-05/06, done on 2026-11-06 against
main `dbb8466d` plus origin/main `e1283475` (EPIC1 steps 1 and 2 merged).
Read: the dossier #936, the review #893, the epics #906, #907, #919, #926 and
their steps, the design issues #928 to #933, the incremental epic #869, the
decisions D25 to D28 (#922), the eight literature notes of the coordinator
(`lit-*.md`), and the Lean behind them (`Incremental.lean`, `Weighted.lean`,
`IncrementalAgg.lean`, `Ties.lean`, `Allowed.lean`, `Aggregate.lean`, and
`ObsEquiv.lean` on origin/main). Six literature searches were run today on
the questions the notes left open; their sources are cited inline, and
anything a search could not confirm says so.

The rule of this review: a gap is closed where a source, a calculation or a
Lean check settles it. What is settled is in section 2, with the evidence.
What stays open is in section 4, stated as new work. Section 3 has the
improvements to the epics that need no literature. Section 6 has the text to
put into the issues. The Lean check of 2.1 is [`WSetGeneric.lean`](WSetGeneric.lean),
compiled against the project's build.

## 1. Verdict

The design is right and the literature agrees with it at every load-bearing
point: K-relations for the core, Z-sets for maintenance, rounding as an
observation on an exact linear part, the metric with the triangle rule,
certificates that Lean replays. The eight notes are thorough; four of their
"no source found" verdicts are confirmed by today's searches (incremental
provenance, error propagation through a plan, a verified refresh protocol,
a mechanised ε-refinement) and two are overtaken: tie nondeterminism has a
2026 Rocq precedent (2.5), and the TLA+-first recommendation predates a
Lean-native model checker (2.2). The findings are not errors. They are places where the plan
proves more than it needs (2.1, 2.4), where a tool that did not exist when
the note was written removes a phase (2.2), where a row of a table is unsound
as written (3.2), and where the dossier has no issue for work it says lands
before 1.0 (3.3).

## 2. Gaps closed

### 2.1 Provenance (#905): the instance is ℕ[X], the delta theorem is free, and ℤ[X] gives provenance of deltas

Three findings, one Lean check.

The semiring #905 calls `Why` is ℕ[X]. `List (List (String × Nat))` with
`++` as `+` and pairwise `++` as `·`, read up to `Perm` at both levels, is a
multiset of multisets of row ids: a polynomial with natural coefficients
whose monomials are multisets of variables. That is the free commutative
semiring on the ids, ℕ[X], the most informative provenance semiring (Green,
Karvounarakis, Tannen, PODS 2007; Green, TOCS 2011 §4 for the hierarchy).
Why(X) is `P(P(X))` with `∪` at both levels (Green 2011 Def. 4.6): idempotent
in both operations, a proper quotient of ℕ[X]. No source states the
list-of-lists identification; it is folklore (free commutative monoid of free
commutative monoids), to be cited as Green 2011 §4. Consequences: the name
should be `NX` or `Prov`, `lineage_sound` and `lineage_complete` hold as
stated, and the dossier's "`Why`/`𝔹` lineage covers the positive fragment
only" is true of Why and false of ℕ[X], because ℕ[X] embeds in the ring ℤ[X].

The delta theorem needs no semiring law. `ZSet.cross_add` (the bilinearity
behind `Rel.delta_correct`) is a `Perm` of weighted lists whose weights are
formed by `*` pointwise; its proof uses `List.flatMap_append` and
permutation lemmas, nothing about `*`. [`WSetGeneric.lean`](WSetGeneric.lean)
restates it for `WSet K := List (Row × K)` with `[Mul K]` only, with the
existing proof text unchanged, and instantiates it at `Int`, `Nat` and a
polynomial type. So #905's "`ZSet.cross_add`/`delta_correct`/`zeval_add` are
re-proved once from `CSemiring.left_distrib`" asks for more than the theorem
needs: `delta_correct` and `zeval_add` hold for any `Mul K`; the semiring
laws enter only where lists are read as K-relations, that is in
`consolidate`, `weight`, `evalK_lift` and the aggregate and `distinct` state
theorems. Stating it this way shortens the class and makes the next point a
corollary.

Provenance of deltas is free. Run `Rel.delta` over `WSet ℤ[X]` with the
change tables annotated by their own ids (`+x` for an insert, `−x` for a
delete) and the delta's weights are polynomials with integer coefficients
whose monomials name the source rows behind each insertion and retraction.
The prototype's example: a join whose left side gains a row and whose right
side loses one gives, for the output row the deleted right row produced,
the weight `−x_{L+,0}·x_{R−,0} − x_{L,0}·x_{R−,0}`: retracted once through
the new left row, once through the old one. This is what the quarantine and
the alert of a refresh need ("these changed source rows made this output
row violate"), and it costs no proof: `delta_correct` at `K := ℤ[X]`. Today's
search confirms no source does this: Amsterdamer, Deutch, Tannen (PODS 2011,
§1) remark that ℤ[X] handles deletions as "setting variables to 0" and
relate it to the counting algorithm; Green, Ives, Tannen (TOCS 2011)
introduce Z-relations without provenance; Chothia, Liagouris, McSherry,
Roscoe (PVLDB 2016) do lineage on differential dataflow by per-operator
reverse maps, not annotations; Chmielewski, Draghici, Olteanu, Zhang (arXiv
2606.07795, 2026) treat IVM over semirings insert-only and exclude ℤ.
Senellart's `provenance-lean` (Lean 4, Mathlib) cannot host ℤ or ℤ[X]: its
`SemiringWithMonus` extends `CanonicallyOrderedAdd`. So the ring route is
complementary to it, not a duplicate.

What stays as #905 says: Suciu's Lemma 2 (no ring difference for idempotent
K), δ as a non-equational operator with `δ(w) = [w > 0]` on Z-sets, left join
in the guarded form, `EXCEPT ALL` as a monus.

### 2.2 The refresh protocol (#933): Lean-first, no TLA+ phase

The note of 2026-11-06 recommended TLA+ with TLC first because exhaustive
small-scope checking finds interleaving bugs fast and a Lean attempt "stalls
on lemmas", and accepted the drift between two models as the cost. That
trade-off has changed. Veil (Pîrlea, Gladshtein, Kinsbruner, Zhao, Sergey,
CAV 2025, LNCS, doi 10.1007/978-3-031-98682-6_2; github.com/verse-lab/veil;
veil.dev) is a Lean 4 framework for transition systems: an Ivy-style DSL
(`relation`, `action`, `require`, `assert`), a verification-condition
generator proved sound in Lean, `#check_invariants` with per-action
counterexamples to induction, symbolic bounded model checking (`sat trace`,
`unsat trace … by bmc`), and, in the 2.0 pre-release of November 2026, an
explicit-state model checker in the TLC style (`#model_check`, counterexample
traces, `#simulate`; Pîrlea et al., "Lessons from Building an Auto-Active
Verifier in Lean", Dafny'26 workshop; Sergey's blog of 2026-02-09). No
Mathlib; Lean v4.32; needs a cvc5 binary. Refinement is not a Veil command,
but Veil definitions are plain Lean, so the refinement theorem of #933 is an
ordinary theorem over them. Liveness is unsupported, as #933 already defers
it.

The drift the note feared is documented in practice: Konnov's port of a
two-phase-commit invariant from Apalache to Lean (protocols-made-fun.com,
May 2025; github.com/konnov/leanda) took about 29 hours and left the
equivalence of the TLA+ and Lean specs unproved. With Veil, #933's step 1
(2 epochs, 2 writers, 1 zombie, 1 lost ack; the #889 scenario as a property)
runs as `#model_check` on the same file that later carries the invariants
and the refinement, and `Refresh.next` is extracted from the same
definitions. Trace validation stays TLA+-centred in the literature (Cirstea
et al. 2024; OmniLink, arXiv 2601.11836, 2026); against a Lean spec it is a
replay of logged events through the `next` relation by `decide`, which the
chaos suite can do without a second tool. Alternatives seen: Leslie
(rupakm, a TLA shallow embedding in Lean 4 with refinement mappings), not
yet a checker; LeanAction and Lasso, pre-alpha.

Also confirmed: no Jepsen analysis of Delta, Iceberg, Hudi or Paimon exists
(jepsen.io/analyses checked); Vanlightly's models (TLA+ for Delta and Hudi,
Fizzbee for Iceberg and Paimon) cover multi-writer commits and compaction,
not `txn(appId, version)`, lost acknowledgements or zombie writers; the
delta-rs Stateright model (DAIS 2022) covers the S3 lock. The lost-ack plus
zombie plus compare-and-swap model of #933 has no public precedent.

Decision to record in #933: Lean-first with Veil; the TLA+ step is dropped;
the toolchain gap (project at v4.35.0, Veil at v4.32.0) is the one thing to
check before starting.

### 2.3 Tolerance composition (#929): the metric exists, the comparison is right, the sum row has its constant

Four things the issue can take as settled.

The metric is in the tree. #896 landed `Relation.Near kind t a b :=
Relation.Equiv {rows := .multiset, floats := .within "plan"} (ObsCtx.ofTol
kind t) a b` with `Tol := Nat → Option Nat`, `Relation.Near.refl`, `.symm`,
`Near_add` (the triangle rule, tolerances adding columnwise) and `Near_mono`
(`ObsEquiv.lean` on origin/main, lines 698 to 775). #929 step 2 is done.

The definition is the right one and the Python already implements it.
`Relation.Equiv` at `.multiset` is "there is a permutation after which rows
are pairwise within tolerance": a bijection between the two bags with every
matched pair within ε per double column, exact elsewhere. That is bottleneck
matching under a weighted Chebyshev metric (∞-Wasserstein at equal mass).
Sorting both results and comparing positionally, which PolySQL (arXiv
2605.07796) and ERIQ (arXiv 2608.30385) do, is unsound when a perturbation
flips the order of near ties. `sverify.testing.allows_rows` already decides
membership by a bipartite matching (Kuhn's augmenting paths, `testing.py`
line 299), so the Lean definition and the Python check agree. Worth a
sentence in #929 and a test that pins the agreement on a near-tie case.

The `M₁` norm is not an observation. #929 wants two norms, per cell (`M∞`)
and summed over rows (`M₁`, what a downstream `SUM` sees). `Relation.Near`
is `M∞`; `M₁` cannot be an `Obs` component because it is a bound on a sum
over the matching, not a per-cell relation. Define `Relation.NearL1 kind
(ε : Nat → Option Nat) a b := ∃ matching, ∀ column, Σ over matched pairs
|a − b| ≤ ε column`, with the same triangle rule (compose the two matchings;
the sum of two sums bounds the sum). Both are instances of one shape, a
quantale-valued relation (Lawvere 1973; Mardare, Panangaden, Plotkin, LICS
2016), and the composition in `ObsCtx.Comp` is composition in that
quantale. Today's search finds no mechanised ε-indexed refinement with a
triangle rule in any proof assistant (the quantitative equational logic
line is paper-only through J.ACM 2026; Fuzz's metric preservation, POPL
2017, likewise), so this is a first and `docs/proofs.md` can say so.

The architecture has a name. NumFuzz (Kellison, Hsu, PLDI 2024, arXiv
2405.04612) types rounding error with a graded monad `M_r` ("may round, error
at most `r`") over sensitivity-graded contexts, with the bind rule `v : M_r
σ`, continuation `s`-sensitive with error `q` gives `M_{s·r + q} τ`. That is
`εₖ = Lₖ·εₖ₋₁ + rₖ` exactly, with a soundness theorem (Cor. 4.20). It is
first-order, over positive reals in Olver's relative-precision metric, with
no collections and no mechanisation, so it is a pattern to transcribe, not
a library to reuse; cite it as the type-theoretic statement of the table.
Bean (PLDI 2025) is backward error and does not apply.

The `SUM` row's constant. For `n` doubles added in any order, with any
nearest rounding and no underflow, `|fl(Σ) − Σ| ≤ (n − 1)·u·Σ|xᵢ|` with no
restriction on `n` (Jeannerod, Rump, SIMAX 34(2), 2013, doi
10.1137/120894488; Rump, "Error bounds for computer arithmetics", ARITH
2019, Table I). This replaces Higham's `γₙ = nu/(1 − nu)` in the row and
drops its `nu < 1` side condition. Lange and Rump (2017, 2019) sharpen it
only under a bound on `n`; the probabilistic `√n·u` constants (Higham, Mary,
2019; Connolly, Higham, Mary, 2021) are not certificates. The only prior
per-aggregate forward-bound oracle for SQL is Mandarapu and Kunkunuru (arXiv
2609.00381, 2026), single-operator and Higham-based; cite it as the practice
the table generalises, and Müller et al. (ICDE 2018) as the
reproducibility-by-construction alternative.

### 2.4 K-aggregation (#905 "out of scope"): for a ring K it is one line

#905 leaves aggregates over `K` out, citing the tensor `K ⊗ M` of
Amsterdamer, Deutch, Tannen (PODS 2011). For sverify's two instances that
machinery is not needed. `IncrementalAgg.lean`'s `ZSet.lin g z = Σ w · g(row)`
is already the K-semimodule map at `K = ℤ`, `M = ℤ`. For any ring `K` and an
integer-valued measure (`COUNT`, integer `SUM`, and after D25 a double `SUM`
as its exact scaled integer), the aggregate over a `WSet K` is `Σ (g row) •
w`, which lands in `K` itself (`ℤ ⊗ K ≅ K`). At `K = ℤ[X]` the `SUM` of a
group is the polynomial `Σ valueᵢ · xᵢ`: the aggregate provenance of ADT
2011's running example, with the values as coefficients, and it is a
ℤ-module map, so `aggregate_maintained` generalises by the same proof. The
restriction to rings costs nothing (ℕ embeds in ℤ) and sidesteps ADT's
compatibility theorem (non-idempotent monoids need a homomorphism to ℕ),
which is about semirings that are not rings. `MIN`/`MAX`, `DISTINCT` and
`AVG`'s division stay with their state theorems. Today's search finds no
delta treatment of aggregate provenance anywhere (ADT 2011 has none; the
HAVING-with-monus paper of 2026 and ProvSQL are not incremental; F-IVM's
ring payloads carry no provenance), so this corollary is new as well.

### 2.5 The ordered seam (#928): a precedent exists, and the framework has a name

#928 and `lit-order.md` say "no paper gives a K-relation account of ORDER
BY, LIMIT or windows; the seam is new" and "ties as nondeterminism is not
formalized in the literature". Today's search corrects both.

The direct precedent is Logos (Ke, Li, Li, "Certified Order-Sensitive SQL
Rewrites with Mechanized Semantics and LLM Guidance", arXiv 2608.15709,
August 2026; code github.com/WindOctober/FormalSQL, Rocq). Its semantics is
a relation `(D, ρ) ⊢ q ⇓ o` whose denotation is the outcome set; `ORDER BY`
yields any list `ℓ` with `Rows(bag ℓ₀, ℓ) ∧ sorted_K ℓ` ("no order is
imposed between rows that tie on all keys"), which is `Lin keys R`;
`OFFSET`/`FETCH` act on whichever list the child produced, so tie-sensitive
top-k differences propagate, which is `Sem`; unordered operators take `bag`
of each child outcome and emit any ordered representative, which is
`fromList` and the `Set` lifting. Its Definition 8 (bag closure) and Theorem
9 (bag-to-list lifting: for closed outcome sets, ordered equivalence is bag
equivalence plus error equivalence) is #928's lifting lemma. It covers
`row_number`, prefix and whole-partition window aggregates, and runtime
errors as outcomes; not `WITH TIES`, ordered aggregates (`string_agg`),
`RANGE`/`GROUPS` frames or peers, K-relations, or contracts on every
outcome. So #928 should cite Logos and state what it adds: the K-relation
carrier, `WITH TIES`, ordered aggregates, window peers, the exactness
theorem for the `Set (KRel ℕ)` re-injection, and "a contract holds on every
linearisation" (certain answers) rather than rewrite equivalence. The
`lit-order.md` sentence becomes "no treatment before August 2026, and none
for K-relations or window peers".

The framework is incomplete information. `OrderAllowed` is a representation
system in the sense of Green and Tannen ("Models for incomplete and
probabilistic information", 2006, Def. 2: tables plus a `Mod` map to sets of
instances); the pointwise lifting of an operator to a set of worlds is
Koch's world-set algebra (ICDT 2009: "all operations are evaluated in each
possible world individually", closure under composition proved); "the
representation is closed under `op`" is Green-Tannen Def. 10, and
re-injecting an ordered result as a set of K-relations is their Def. 13,
algebraic completion. A contract that holds on every member is a certain
answer; for monotone contracts, Gheerbrant, Libkin, Sirangelo (TODS 2014)
characterise when naive evaluation computes them. The nearest treatment of
order itself is Amarilli, Ba, Deutch, Senellart (TIME 2017; TCS 2019, arXiv
1801.06396): po-relations whose possible worlds are the linear extensions,
`POSS` NP-complete and `CERT` coNP-complete in general, PTIME for positive
RA without accumulation, and their Prop. 8.1, that forgetting order commutes
with positive queries, is #928's "unordered theorems lift unchanged". Their
§7 shows duplicate elimination and group-by over contradictory orders give
an empty world set, which is exactly why #928's re-injection must be a set
of K-relations and not one po-relation; Amarilli's model cannot represent
worlds with different bags (tie-sensitive top-k), which #928's can. Feng,
Glavic, Kennedy (PVLDB 2023, arXiv 2302.08676) approximate certain and
possible answers for sort, top-k and window queries and force determinism
by extending the sort key with every remaining column, the engineering
precedent for D24's deterministic profile.

Two observations from the code. `Measure.OrderAllowed` (`Ties.lean` line 54) already has the `Lin`/`Sem`
shape: `∃ s, s.Perm rows ∧ s.Pairwise (sortLe m.sort) ∧ v = if m.fn.sorts
then m.eval s else m.eval rows`. The lifting lemma of #928 step 1 ("if `op`
factors through the multiset, `Sem` is a singleton") is `Measure.allowed_eq`
and `aggAllowed_eq` (`Allowed.lean` lines 104, 127) generalised from
measures to operators. Step 1 is a refactor with a theorem already in the
tree; the content of #928 is steps 3 to 5.

`evalK` should not contain `orderBy`. `Rel.zeval` sorts its Z-set at an
`orderBy` and `Rel.delta` keeps the sort (`Incremental.lean`: `.orderBy r
keys => .orderBy (r.delta δ) keys`), so every delta term is sorted before the
engine sums its weights, which the sink then consolidates unordered. In the
seam's own terms order is an effect on top of the K-relation, so `evalK`
treats `orderBy` as the identity and `Rel.delta` drops it (with
`delta_correct` up to `Perm`, as `incremental_sound` already is). That is
the measured optimization CLAUDE.md asks of #905's PR: one `ORDER BY` fewer
per delta term, on the catalogue's sorted incremental queries.

### 2.6 D25's text (#913, #914): what to cite, and the cases to state

IEEE 754 does not define the sum D25 wants. Clause 9.4 (reduction
operations: `sum`, `dot`, `sumSquare`, `sumAbs`) is recommended, not
required, and leaves the finite result unspecified: implementations "may
associate in any order or evaluate in any wider format" (clause text as
quoted by Dickinson, CPython tracker 2013, and WG14 N3173); the only
specified finite result is that the sum of zero numbers is `+0` (Lefèvre,
IEEE TC 2017, §1). Clause 11 (reproducibility) does not cover reductions.
The 2019 augmented operations were added "to support reproducible
reductions" and may become required later (IEEE 754-2019 background page;
Riedy, Demmel, ARITH 2018). The one standard that requires a correctly
rounded sum is IEEE 1788-2015 (interval arithmetic), clause 12.12.12, for
the four reductions of 754 §9.4 (text confirmed through Lefèvre, final
wording unconfirmed). The operational specification to cite is MPFR's
`mpfr_sum` (Lefèvre, "Correctly rounded arbitrary-precision floating-point
summation", IEEE TC 66(12), 2017): correctly rounded, with the special cases
"the same as a succession of additions in infinite precision", in order:
any NaN gives NaN; a `+∞` and a `−∞` give NaN; any `∞` gives that `∞`; an
exact zero has the inputs' sign if all inputs share it, else `+0` (under
round-to-nearest); the empty sum is `+0`. This matches `lit-floatsum.md`
§3.3 and the IEEE two-operand rule, so D25 can adopt it verbatim. Overflow
is a read-time condition: the correctly rounded sum is `±∞` when the exact
sum is at or above `2¹⁰²⁴·(1 − 2⁻⁵⁴)` in magnitude.

One difference from the code to decide: `floatSum` folds from `+0.0`
(`Aggregate.lean` line 135), so an all-`−0.0` group gives `+0.0` today,
where `mpfr_sum` gives `−0.0`. Under the default observation `canon` makes
the sign unobservable; D25 should still say which it is. The `mpfr_sum`
rule is the one every evaluation order agrees with when there is no seed.

Variance and standard deviation. No paper defines a correctly rounded
variance; the precedent is CPython's `statistics` module (bpo-45876, 2021):
exact rational moments, one rounding for the variance, and the standard
deviation as the correctly rounded square root of the exact variance
(`_float_sqrt_of_frac`), because `RN(√RN(var))` can differ from
`RN(√var)` by an ulp (double rounding). D25 should define `STDDEV` as
`RN(√var_exact)` and `VAR` as `RN(var_exact)`, and name that they are not
`RN` of each other.

`AVG` is one rounding of the exact mean; engines do two (`fl(fl(Σ)/n)`), so
`floatAvgCR`'s `epsilon` term carries the second rounding; #914 should name
it.

Words for the docs: distinguish reproducible (Demmel, Nguyen; ReproBLAS:
bitwise identical, error proportional to `max|xᵢ|`, not correctly rounded)
from correctly rounded (one order-free value); Materialize's `i128` fixed
point at `2⁻²⁴` for float sums (discussion #39315, September 2026; `0.1`
sums to `0.09999996423721313`) is the lossy version of #918's accumulator,
and a good contrast; Feldera recomputes float aggregates ("non-linear when
applied to DOUBLE or FLOAT"); Spark removed float sums from its
order-insensitive aggregates in 2019 (SPARK-29343) and has an open ticket
on silent errors from nondeterministic float sums on retry (SPARK-47520).

For the Lean side (#916, #893 3.7): Lean core's `Float.Model` (since v4.33)
ships no theorems by design ("not a goal … to have any direct lemmas
written about it at all", reference manual 4.35), so retiring the float
axioms through it means a bridge to a lemma library: flean (MinusGix,
sorry-free, with rounding monotonicity for every mode and a Kahan proof) is
the candidate, FloatLib and FloatSpec the alternatives. Mechanised
correctly rounded sums exist for three addends by round-to-odd (Boldo,
Melquiond, IEEE TC 2008, Coq) and for expansion renormalisation (Boldo,
Joldes, Muller, Popescu, ITP 2017); no Kulisch, superaccumulator or xsum
proof exists in any assistant, so #918's accumulator proof would be the
first.

### 2.7 Incremental windows (#928 step 5, #869) and plan equivalence (#893 3.2)

Windows. No engine publishes a delta rule for a `ROWS` frame as `D ∘ Op ∘
I` with its state: Feldera reduces `ROWS BETWEEN` to `ROW_NUMBER` per
partition and documents ranking as "very expensive" (one change renumbers
the rows after it), Materialize recomputes the whole partition on any
change and recommends rewrites, RisingWave recomputes the affected range,
and Databricks' Enzyme (arXiv 2603.27775, 2026) recomputes partitions and
names "window functions with ordering clauses, where ties may be broken
arbitrarily" as a nondeterminism hazard without solving it. The DBSP
journal version (VLDB J. 34(4), 2025, §7.3.4) says only that `LAG` and
`RANGE` "can be implemented using highly efficient incremental DBSP
operators". The one mechanised sliding-window proof is Heimes, Traytel,
Schneider's Isabelle AFP entry (2020, revised 2025) for Basin, Klaedtke,
Zălinescu's greedy associative algorithm (IPL 2015), worth reading for the
invariant style; Two-Stacks, DABA, FiBA and the reactive aggregator have
paper proofs only. So #928 step 5 (one `ROWS` frame rule proved against
`Sem`) and the refinement statement "the incremental ranked output is
always one allowed batch output, and reproducible under a stable
tie-break" are both unclaimed.

Equivalence. What `sv.same` can state as settled: conjunctive queries are
bag-equivalent iff isomorphic (Chaudhuri, Vardi, PODS 1993); unions of
conjunctive queries (`UNION ALL`) likewise, GI-complete, by Green (ICDT
2009, §7.5, via Cohen, Nutt, Serebrenik 1999); bag containment of unions is
undecidable (Ioannidis, Ramakrishnan, TODS 1995) and of conjunctive queries
with inequalities too (Jayram, Kolaitis, Vee, PODS 2006); bag containment
of plain conjunctive queries is open in 2026 (Marcinkowski, Orda, PODS
2024; Marcinkowski, Ostropolski-Nalewaja, PODS 2026). New and directly
useful: Cohen, "Few Rows Tell Them Apart" (arXiv 2609.09978, September
2026) gives computable bounds on the database size that separates two
non-equivalent queries for conjunctive fragments under set, bag and
bag-set semantics, which turns the bounded counterexample search into a
complete decision procedure on those fragments and gives `EqualUpTo(k)` a
`k` with a theorem behind it. No 2025 or 2026 equivalence tool has a
mechanised soundness proof (QED, SQLSolver, VeriEQL, Polygon, SpotIt are
all SMT-based, none with windows); UDP's Lean 3 procedure and HoTTSQL
remain the precedents, so a Lean 4 `sv.same` would be the first since
2018.

## 3. Improvements to the epics that need no literature

### 3.1 The `x · y` row of #929 is unsound as written

The issue's row gives `M∞ = |y|·εx + |x|·εy`. The error of a product of two
perturbed values has the second-order term `εx·εy`, which the note's own
table (`lit-sensitivity.md` A8) includes and the issue dropped. Either keep
the term or state the magnitude bounds `|x| ≤ X`, `|y| ≤ Y` as bounds on
both the reference and the engine values (the declared range widened by ε),
in which case `Y·εx + X·εy` is sound. The same care applies to `x / y`:
`|y|` bounded away from zero must hold for the engine's `y`, that is `Y_min −
εy > 0`.

Rows to add: `CASE`/`IF` and `NULLIF` on a tolerated double are discontinuous
(no constant, as the filter row); `COALESCE`, `abs`, `greatest`, `least` are
1-Lipschitz; a cast to decimal or integer is discontinuous (listed), a cast
double to float32 adds a rounding term `r`.

### 3.2 Two pieces of #893 the dossier says land before 1.0 and has no issue for

#936 says "all of it lands before 1.0" and lists six design issues. #893's
ranking also has 3.2, plan equivalence (`sv.same`), and 2.5, the
difference-bound domain, and the coordinator wrote the literature for both
(`lit-equivalence.md` with a full architecture and benchmark plan;
`lit-metric-domains.md` Part B with the zone-domain recommendation). Neither
has a design issue. The text for both is in section 6; `sv.same` is, as
#893 says, the most asked-for guarantee in the field, and the equivalence
note's architecture (proved normal form, evaluator-checked counterexample,
`EqualUpTo(k)` never collapsed into `Equal`) is ready to file. 3.8,
generated lowerings per engine, has #271.

### 3.3 Dependencies that are not semantic

#936 orders #905 after #923 (typed `Value`). `WSet K` is `List (Row × K)` and
never looks inside a `Value`; the order is about merge conflicts in
`Incremental.lean`, not meaning. Saying so lets #905 start on the untyped
representation if #923 slips, with EPIC4's rule (step 2 before 1.0, steps 1
and 3 after) unchanged.

### 3.4 `Engine.wf` by `decide` (#931)

`Engine.wf` ("every arm contains the reference's value") is decidable over
finite diff tables, as `ObsRow.wf` is, but not over an arm stated as a
tolerance (`agg .fsum vs v := Near …`). State the arms as `v = reference ∨
deviation vs v` so `wf` is `Or.inl rfl` and the tolerance lives in the
deviation; #931 should say which arms are decided and which are proved.

## 4. Research gaps that stay open

Each of these is new work no source covers, confirmed by the notes and
today's searches. They are the claims `docs/prior-work.md` can make once the
code exists, and each is a paper if written up.

1. Incrementalisation with provenance: ℤ[X]-annotated Z-sets through
   `D ∘ Q ∘ I` with a proof; aggregate provenance with deltas. Status after
   this review: the positive fragment is a corollary (2.1, prototype), the
   aggregate part a one-line extension for rings (2.4). Nothing published.
2. ε-indexed refinement with a triangle rule, mechanised: no proof-assistant
   development exists (2.3). Sverify has it.
3. A verified exactly-once refresh protocol for lakehouse sinks with lost
   acknowledgements and zombie writers: no model, no Jepsen report (2.2).
4. Tie nondeterminism over a K-relation carrier, with `WITH TIES`, ordered
   aggregates, window peers, and contracts as certain answers: Logos (2.5)
   has the list-level outcome semantics and the lifting theorem; the rest
   is new.
5. Incremental window and top-k rules proved against a nondeterministic
   batch semantics: no delta rule published, one Isabelle proof of a
   different algorithm (2.7).
6. Error propagation through a whole relational plan with two norms: no
   source (2.3); NumFuzz is the nearest pattern.
7. Conservation contracts as commuting with a semimodule map: no database
   paper names conservation (`lit-sensitivity.md` B5, confirmed).

## 5. Additions to `docs/prior-work.md`

- Pîrlea, Gladshtein, Kinsbruner, Zhao, Sergey, Veil, CAV 2025.
- Kellison, Hsu, NumFuzz, PLDI 2024, arXiv 2405.04612.
- Jeannerod, Rump, SIMAX 34(2) 2013; Rump, ARITH 2019 (the sum bound).
- Mandarapu, Kunkunuru, arXiv 2609.00381, 2026 (forward bounds as test
  oracles for SQL aggregates).
- Chmielewski, Draghici, Olteanu, Zhang, arXiv 2606.07795, 2026 (IVM over
  semirings, insert-only).
- Chothia, Liagouris, McSherry, Roscoe, PVLDB 9(12) 2016 (lineage on
  differential dataflow).
- Konnov, leanda, 2025 (the cost of porting a TLA+ invariant to Lean).
- Green, TOCS 2011 §4 (the provenance hierarchy; ℕ[X] as the free
  commutative semiring).
- Ke, Li, Li, Logos, arXiv 2608.15709, 2026 (outcome-set semantics of
  ORDER BY and FETCH in Rocq).
- Amarilli, Ba, Deutch, Senellart, TCS 2019, arXiv 1801.06396
  (order-incomplete data; possible and certain answers over orders).
- Green, Tannen, "Models for incomplete and probabilistic information",
  2006; Koch, ICDT 2009 (representation systems, world-set algebra).
- Gheerbrant, Libkin, Sirangelo, TODS 2014 (certain answers of monotone
  queries).
- Lefèvre, IEEE TC 66(12) 2017 (`mpfr_sum`: the correctly rounded sum and
  its special cases); IEEE 1788-2015 §12.12.12.
- Heimes, Traytel, Schneider, Isabelle AFP 2020 (a verified sliding-window
  aggregation).
- Cohen, "Few Rows Tell Them Apart", arXiv 2609.09978, 2026 (small-database
  bounds for query inequivalence).
- Green, ICDT 2009 §7.5 (bag equivalence of unions of conjunctive queries).
- Enzyme, arXiv 2603.27775, 2026 (an industrial IVM that names tie
  nondeterminism as a hazard).

## 6. Text for the issues

### #905

Replace "`Why`" by "`NX`, the free commutative semiring ℕ[X] on source row
ids (Green 2011 §4): `List (List (String × Nat))` up to `Perm` at both
levels". Replace item 3's "re-proved once from `CSemiring.left_distrib`" by
"`cross_add`, `zeval_add` and `delta_correct` are stated for `[Mul K]` and
keep their proofs; `CSemiring` is needed by `consolidate`, `weight` and
`evalK_lift`". Add item 6: "`Rel.delta` over `WSet (ZPoly)` with change
tables annotated `+x`/`−x` gives provenance of deltas; `--lineage --delta`
prints it; the quarantine of a refresh names changed source rows from it."
Add to the optimization: "`evalK` and `Rel.delta` drop `orderBy`; measure
the delta terms of the catalogue's sorted incremental queries." Move
"aggregates over K" from out of scope to a step: "for `[Ring K]` and
integer measures, `lin g z = Σ (g row) • w`; `aggregate_maintained` over
`K`."

### #933

Replace decision 1 by: "Lean-first with Veil (CAV 2025; `#model_check` in
the 2.0 pre-release) on the Veil toolchain; no TLA+ spec. Step 1 is the
Veil model with the four scenario parameters and `#model_check` against
invariants 1 to 5 and the #889 property; step 2 is trace validation by
replaying the chaos suite's events through `next` with `decide`; steps 3
to 5 as written, with the refinement theorem as plain Lean over the Veil
definitions." Note the toolchain pin to check first.

### #929

Step 2 is done (#896). Add the `M₁` relation (`Relation.NearL1`) as step 2b
with its triangle rule. Fix the `x · y` and `x / y` rows (3.1). Replace
Higham's constant in the `SUM` row by `(n − 1)·u·Σ|x|` (Jeannerod, Rump
2013) with the no-underflow hypothesis. Cite NumFuzz for the composition
rule. Add the test that `allows_rows` and `Relation.Near` agree on a
near-tie case.

### #928

Note that step 1 is `Measure.OrderAllowed` and `Measure.allowed_eq`
generalised, and that `evalK` treats `orderBy` as the identity (2.5).
Replace "No paper gives a K-relation account of ORDER BY, LIMIT or windows;
the seam is new" by: "Logos (arXiv 2608.15709, Rocq, 2026) gives ORDER BY
and FETCH an outcome-set semantics with `Lin` as its `Rows ∧ sorted_K` and
the lifting lemma as its Theorem 9; the seam adds the K-relation carrier,
`WITH TIES`, ordered aggregates, window peers, the `Set (KRel ℕ)`
re-injection with its exactness theorem, and contracts on every outcome.
The vocabulary is incomplete information: `OrderAllowed` is a
representation system (Green, Tannen 2006), `Sem` is Koch's pointwise
world-set lifting (ICDT 2009), the re-injection is algebraic completion,
and a contract on every tie order is a certain answer (Amarilli et al.,
TCS 2019, whose po-relations cannot represent tie-sensitive top-k)." Step
5's rule is unclaimed in the literature (2.7); say so in "What done looks
like".

### #913 / #914

State the zero, infinity, NaN and overflow rules of the correctly rounded
sum as `mpfr_sum` states them, decide the all-`−0.0` case against the
`+0.0` seed, define `STDDEV` as `RN(√var_exact)`, and name `AVG`'s second
rounding in `epsilon` (2.6). Cite IEEE 754 §9.4 as leaving `sum`
unspecified and IEEE 1788 §12.12.12 as the standard that requires it
correctly rounded.

### New: Design: plan equivalence, `sv.same` (#893 3.2)

Verdicts `Equal` (proved), `Different(db)` (checked by `Rel.eval`),
`EqualUpTo(k)`, `Unknown`; the pipeline of `lit-equivalence.md` §6 (3VL to
2VL pairs, proved normaliser, Chaudhuri-Vardi isomorphism on the SPJU core,
Cohen-Nutt-Sagiv rule for aggregates, bounded conflict-driven counterexample
search); validation on the Calcite 232/444, CockroachDB 1287 and VeriEQL
sets with the lift fraction reported. `UNION ALL` is in the complete core
(Green 2009 §7.5); Cohen 2026's bounds give `EqualUpTo(k)` its `k` on the
conjunctive fragments (2.7). Milestone M4.

### New: Design: the zone domain for facts (#893 2.5)

`Fact.diff` as a closed difference-bound matrix with a zero column (Dill
1989; Miné 2001): intervals read off the matrix, incremental closure after
each fact, emptiness as a negative cycle, NULL as a per-column flag;
`Fact.holds` stays as the syntactic fallback. Milestone M4.

### #936

Add the two issues above to the table; note the #905 and #933 changes; mark
2.1's ℕ[X] naming under "What not to do" ("do not call ℕ[X] `Why`").
