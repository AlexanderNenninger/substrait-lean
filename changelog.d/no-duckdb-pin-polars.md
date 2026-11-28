CI's `no-duckdb` job pins Polars to 2.1.0, the version in `uv.lock` and the facts, so a new Polars release can't fail it with `EngineVersionError`.
