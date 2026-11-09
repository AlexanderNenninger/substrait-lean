# Prior work and credits

Sverify builds on other people's work: the projects it runs on, the ideas behind its design, and the research it learned from. This page credits them, and places sverify next to related tools. The survey reflects what we found in November 2026; corrections are welcome.

## What sverify builds on

### Platforms and formats

- [Substrait](https://substrait.io), the cross-language specification of relational plans that sverify gives a formal meaning to.
- Lean 4: L. de Moura, S. Ullrich, "The Lean 4 Theorem Prover and Programming Language", CADE-28, 2021. [lean-lang.org](https://lean-lang.org)
- Mathlib: The mathlib Community, "The Lean Mathematical Library", CPP 2020. Sverify's float error bounds (`float-bounds/`) are proved with it. [mathlib4](https://github.com/leanprover-community/mathlib4)
- DuckDB: M. Raasveldt, H. Mühleisen, "DuckDB: an Embeddable Analytical Database", SIGMOD 2019. [duckdb.org](https://duckdb.org)
- sqllogictest, by D. R. Hipp for SQLite, and DuckDB's suite of it, which sverify replays to characterize DuckDB. [sqlite.org/sqllogictest](https://sqlite.org/sqllogictest), [DuckDB's tests](https://github.com/duckdb/duckdb/tree/main/test)
- [SQLGlot](https://github.com/tobymao/sqlglot), which parses the DuckDB SQL that sverify lifts.
- [Ibis](https://ibis-project.org), the dataframe API sverify verifies.
- Apache Arrow and [Arrow Flight](https://arrow.apache.org/docs/format/Flight.html), the data sverify moves between engines. [arrow.apache.org](https://arrow.apache.org)
- Delta Lake: M. Armbrust et al., "Delta Lake: High-Performance ACID Table Storage over Cloud Object Stores", PVLDB 13(12), 2020, and [delta-rs](https://github.com/delta-io/delta-rs).
- [Apache Iceberg](https://iceberg.apache.org) and [pyiceberg](https://github.com/apache/iceberg-python).
- The engines sverify profiles: DuckDB; [Polars](https://pola.rs); Spark SQL (M. Armbrust et al., SIGMOD 2015); and Snowflake.
- Apache DataFusion (A. Lamb et al., SIGMOD 2024), whose Substrait producer wrote the `df_*.json` golden fixtures and whose bugs sverify recorded (`upstream/bugs/DF-*.json`).

### Engine testing

Sverify's replay and its differential oracle follow the idea of checking an engine against a reference, from:

- P. Guagliardo, L. Libkin, "A Formal Semantics of SQL Queries, Its Validation, and Applications", PVLDB 11(1), 2017, which validates a formal semantics against real engines by random testing.
- M. Rigger, Z. Su: "Testing Database Engines via Pivoted Query Synthesis", OSDI 2020; "Detecting Optimization Bugs in Database Engines via Non-Optimizing Reference Engine Construction", ESEC/FSE 2020; "Finding Bugs in Database Systems via Query Partitioning", OOPSLA 2020. [SQLancer](https://github.com/sqlancer/sqlancer)
- S. Zhong, M. Rigger, SQLancer++, ASPLOS 2026. [arXiv 2503.21424](https://arxiv.org/abs/2503.21424)

### SQL semantics and query equivalence

Sverify found no formal semantics of Substrait; the closest work formalizes
SQL or relational algebra, most of it in Coq.

- S. Chu, K. Weitz, A. Cheung, D. Suciu, "HoTTSQL: Proving Query Rewrites with Univalent SQL Semantics", PLDI 2017, and the Cosette prover: queries denoted as K-relations using univalence. [arXiv 1607.04822](https://arxiv.org/abs/1607.04822), [PLDI page](https://pldi17.sigplan.org/event/pldi-2017-papers-hottsql-proving-query-rewrites-with-univalent-sql-semantics), [Cosette](https://github.com/uwdb/Cosette)
- V. Benzaken, É. Contejean, "A Coq Mechanised Formal Semantics for Realistic SQL Queries", CPP 2019 (SQLCert): realistic SQL with nulls, aggregates and correlated subqueries, an extended bag algebra, and proofs of common optimizer rewrites. [HAL 01487062](https://hal.archives-ouvertes.fr/hal-01487062), [HAL 01955433](https://hal.archives-ouvertes.fr/hal-01955433)
- W. Ricciotti, J. Cheney, "A Formalization of SQL with Nulls", JAR 2022: three-valued logic, set and bag operations, lateral joins and nested subqueries. [arXiv 2003.11331](https://arxiv.org/abs/2003.11331), [PMC9637088](https://www.ncbi.nlm.nih.gov/pmc/articles/PMC9637088/)
- J. Auerbach, M. Hirzel, L. Mandel, A. Shinnar, J. Siméon, "Q*cert: A Platform for Implementing and Verifying Query Compilers", SIGMOD 2017: a proved query compiler built around the nested relational algebra (NRA<sup>e</sup>), the closest analogue to a proved IR for queries. [querycert.github.io](https://querycert.github.io)
- Q. Zhou, J. Arulraj, S. Navathe, W. Harris, J. Wu, "SPES: A Symbolic Approach to Proving Query Equivalence Under Bag Semantics". [arXiv 2004.00481](https://arxiv.org/abs/2004.00481)
- H. Ding et al., "Proving Query Equivalence Using Linear Integer Arithmetic" (SQLSolver), SIGMOD 2024. [SQLSolver](https://github.com/SJTU-IPADS/SQLSolver)
- Y. He, P. Zhao, X. Wang, Y. Wang, "VeriEQL: Bounded Equivalence Verification for Complex SQL Queries with Integrity Constraints", OOPSLA 2024. [VeriEQL](https://github.com/michaelmior/VeriEQL)
- S. Wang, S. Pan, A. Cheung, "QED: A Powerful Query Equivalence Decider for SQL", PVLDB 17(11), 2024. [qed-solver](https://github.com/qed-solver)

### In Lean 4

- RelationalAlgebra (Rickerd): relational algebra ≡ first-order logic, built on Mathlib. [Reservoir](https://reservoir.lean-lang.org/@Rickerd1234/RelationalAlgebra)
- provenance (Senellart): semantics for ProvSQL with semiring provenance, a route to K-relation semantics in Lean. [Reservoir](https://reservoir.lean-lang.org/@PierreSenellart/provenance)
- Emergence AI's [Lean SQL equivalence write-up](https://www.emergence.ai/blog/formal-verification-of-sql-queries-in-lean-for-enhanced-accuracy), and the typed-queries chapter of [*Functional Programming in Lean*](https://lean-lang.org/functional_programming_in_lean/Programming-with-Dependent-Types/Worked-Example___-Typed-Queries/).

### Incremental view maintenance and streaming

- M. Budiu, T. Chajed, F. McSherry, L. Ryzhyk, V. Tannen, "DBSP: Automatic Incremental View Maintenance for Rich Query Languages", PVLDB 16(7), 2023, with its [proofs in Lean](https://github.com/tchajed/database-stream-processing-theory). Sverify's delta rules and Z-set view of changes follow it.
- F. McSherry, D. G. Murray, R. Isaacs, M. Isard, "Differential Dataflow", CIDR 2013.
- A. Gupta, I. S. Mumick, V. S. Subrahmanian, "Maintaining Views Incrementally", SIGMOD 1993.
- T. Akidau et al., "The Dataflow Model", PVLDB 8(12), 2015, and "Watermarks in Stream Processing Systems", PVLDB 14(12), 2021, for watermarks and lateness.

### Numerics

- N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002: the standard model of rounding and the summation bounds in `float-bounds/`.
- B. P. Welford, "Note on a Method for Calculating Corrected Sums of Squares and Products", Technometrics 4(3), 1962.
- T. F. Chan, G. H. Golub, R. J. LeVeque, "Algorithms for Computing the Sample Variance: Analysis and Recommendations", The American Statistician 37(3), 1983.
- E. Schubert, M. Gertz, "Numerically Stable Parallel Computation of (Co-)Variance", SSDBM 2018: the co-moment updates and merges the engines use.
- S. Boldo, G. Melquiond, "Flocq: A Unified Library for Proving Floating-Point Algorithms in Coq", ARITH 2011.
- For the planned approximate quantiles: M. Greenwald, S. Khanna, "Space-Efficient Online Computation of Quantile Summaries", SIGMOD 2001; T. Dunning, O. Ertl, "Computing Extremely Accurate Quantiles Using t-Digests", [arXiv 1902.04023](https://arxiv.org/abs/1902.04023).

### Program analysis

- P. Cousot, R. Cousot, "Abstract Interpretation: A Unified Lattice Model for Static Analysis of Programs by Construction or Approximation of Fixpoints", POPL 1977: the range analysis behind contracts.
- E. W. Dijkstra, "Guarded Commands, Nondeterminacy and Formal Derivation of Programs", CACM 18(8), 1975: weakest preconditions, behind the inferred bounds and suggestions.
- C. A. R. Hoare, "An Axiomatic Basis for Computer Programming", CACM 12(10), 1969: pre- and postconditions, behind `requires` and `ensures`.

## Related tools

As far as we found, no other project combines a mechanized semantics of plans with proved contracts, proved translations to engines, incremental maintenance and float bounds, and none formalizes Substrait. Each neighbour covers one part:

| Tool | What it does | Relation to sverify |
|---|---|---|
| [QED](https://github.com/qed-solver), Cosette, SPES, SQLSolver, VeriEQL, Polygon | Decide or refute whether two queries are equivalent | Sverify checks one query against a contract; these tools fit its planned translation validation |
| Logos ([arXiv 2608.15709](https://arxiv.org/abs/2608.15709)) | Proofs of query equivalence in Rocq, with runtime errors and engine scalar semantics | Closest in spirit for semantics that include errors |
| SQLCert, Q*cert | Mechanized SQL semantics, verified query compilers | Verified compilation, without contracts or today's engines |
| Grain-aware transformations (Karayannidis, [arXiv 2601.00995](https://arxiv.org/abs/2601.00995)) | Proves join and aggregation grain in Lean 4 | The nearest "prove the pipeline before data runs" work, for grain |
| [DBSP / Feldera](https://www.feldera.com) | Incremental view maintenance with a proved theory, in its own engine | Sverify proves per-plan deltas, retention and engine SQL |
| Materialize, Differential Dataflow | Incremental views at scale | Not proved |
| Great Expectations, Soda, Deequ | Check rules on data while or after it runs | Sverify proves before data runs and checks only what it can't prove |
| dbt model contracts, Gable | Check schemas and contracts statically | Schema level; sverify reasons about values |
| Ibis, Narwhals, SQLGlot | One API or SQL across engines | Best effort; sverify proves the translation |
| [substrait-validator](https://github.com/substrait-io/substrait-validator) | Checks that a plan is well formed | Sverify gives the plan its meaning |
| SQLancer, SQLancer++ | Find engine bugs with metamorphic oracles | Sverify's oracle compares engines with a proved reference |
| "Bounded, Indeterminate, or a Bug" (Mandarapu, Kunkunuru, [arXiv 2609.00381](https://arxiv.org/abs/2609.00381)) | Tests SUM, AVG and VARIANCE across 8 engines against exact results and condition-number bounds | The closest neighbour to sverify's float bounds, which are machine-checked |
