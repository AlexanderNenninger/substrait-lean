-- The orders that count: cancelled ones are dropped.
select order_id, customer_id, order_ts, status, amount
from {{ source('app', 'orders') }}
where status <> 'cancelled'
