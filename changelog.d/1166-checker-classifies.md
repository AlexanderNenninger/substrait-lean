### The checker classifies issues and evidence

- `substrait-check --contract` says per issue whether it is assumed and
  checked on the data while the job runs (`"assumed"`: a `SUM` that leaves
  its type, an overflow to `±∞`), and its exit code no longer counts those as
  unproved: a plan whose only issue is an assumed `SUM` overflow exits 0, as
  sverify's report already said
  ([#1088](https://github.com/AlexanderNenninger/substrait-lean/issues/1088)).
- An overflow to `±∞` is reported only under the reference: under another
  profile the request names (`semantics="duckdb"` included, which sverify now
  sends), the engine gives `±∞`.
- The report's `engines` block gives every engine a route may reach a
  verdict, DataFusion included (`"profile": false`), and says per engine why a
  translated run rests on tests (`"tested_because"`) and what evidence it
  carries (`"translated_evidence"`)
  ([#1166](https://github.com/AlexanderNenninger/substrait-lean/issues/1166)).
