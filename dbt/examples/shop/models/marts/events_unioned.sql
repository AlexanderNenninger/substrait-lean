-- Two event sources stacked, each row tagged with its source (catalogue:
-- dbt-union-sources).
select user_id, event_ts as ts, event_name as name, cast(null as double) as amount, 'events' as source
from {{ source('app', 'events') }}
union all
select customer_id as user_id, order_ts as ts, 'order' as name, amount, 'orders' as source
from {{ ref('stg_orders') }}
