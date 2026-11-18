### sverify-dbt first run

A seed without `column_types` is checked once `dbt seed` and `dbt docs generate` have given it types, and is refused with that instruction before (#1586). The refusal for a relation without types now reads "ref('x') has no column types: …", and `sverify-dbt suggest` says when it read nothing because every model was refused. A plain `dbt compile` after `dbt run` renders an incremental model's `{{ this }}` branch; sverify-dbt now says so and asks for `dbt compile --full-refresh`.
