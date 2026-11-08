# `--contract` goldens

Each `<name>.json` is a `--contract` request as `sverify.verify` sends it, and
`<name>.expected` is the checker's answer through `--serve` (`tests/run.sh`;
`tests/run.sh --update` re-records). They cover a projection, an integer
division, an unbounded integer `SUM`, a capped double `SUM`, an overflow to
`±∞`, keys over a sort, the Polars and Substrait profiles, and SQL.

They were recorded from `sverify.verify` calls on main at bfe0fa26 (#1088), to
show that splitting `ContractCheck.check` into `parse` and `Request.check`
changes no answer. A change to the report's JSON re-records them.
