# Polars's tests, replayed

The ledgers of `python -m sverify_dev.polars_tests` (#2615): one per module of Polars's
Python unit tests at `py-2.1.0`, and [triage.json](triage.json) for the collects where the
model and sverify's run agree with each other and differ from Polars. The facts README
explains the replay ([../facts/README.md](../facts/README.md#polarss-own-tests)).

The ledgers hold test ids, outcomes and normalized reasons, and no query text or data of
Polars's tests; Polars's licence is [LICENSE-polars](LICENSE-polars) (MIT).
