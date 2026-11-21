### Install lines lead with the engine, and a refused run names its postcondition in words

- The install sections of `python/README.md`, `docs/getting-started.md`, `docs/engines.md` and the `sverify` skill lead with `pip install 'sverify[duckdb]'`, which the first example needs; `pip install sverify` follows as the verify-only install.
- `UnverifiedRunError` and the unverified-refresh warning say `ensures total < 5 is not proved`, as `sverify check` does, with the Python syntax left out.

([#1997](https://github.com/AlexanderNenninger/substrait-lean/issues/1997))
