### sverify-dbt first run

A seed without `column_types` takes its column types from DuckDB's reading of its CSV, so a seed-based starter project is checked instead of refused (#1586). The refusal for a relation without types now reads "ref('x') has no column types: …", and `sverify-dbt suggest` says when it read nothing because every model was refused. A plain `dbt compile` after `dbt run` renders an incremental model's `{{ this }}` branch; sverify-dbt now says so and asks for `dbt compile --full-refresh`.
