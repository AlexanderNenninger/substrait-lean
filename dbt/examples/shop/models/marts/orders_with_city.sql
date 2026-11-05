-- Each order with the customer's city when it was placed (catalogue:
-- dbt-scd2-point-in-time).
select o.order_id, o.order_ts, h.city
from {{ ref('stg_orders') }} as o
left join {{ ref('customer_history') }} as h
    on o.customer_id = h.customer_id
    and h.valid_from <= o.order_ts
    and (h.valid_to is null or o.order_ts < h.valid_to)
