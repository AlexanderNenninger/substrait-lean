-- Each customer's order count per status (catalogue: dbt-pivot-wider).
select
    customer_id,
    count(*) filter (where status = 'placed') as placed,
    count(*) filter (where status = 'shipped') as shipped,
    count(*) filter (where status = 'returned') as returned
from {{ ref('stg_orders') }}
group by customer_id
