-- A type-2 history from customer updates: each version is valid until the
-- next update (catalogue: dbt-scd2-from-updates).
select
    customer_id,
    city,
    plan,
    updated_at as valid_from,
    lead(updated_at) over (partition by customer_id order by updated_at) as valid_to
from {{ source('app', 'customer_updates') }}
