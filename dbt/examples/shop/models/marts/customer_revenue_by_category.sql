-- Each customer's revenue per product category, one column per category
-- (catalogue: dbt-pivot-conditional).
select
    o.customer_id,
    sum(i.qty * i.price) filter (where p.category = 'books') as books,
    sum(i.qty * i.price) filter (where p.category = 'games') as games,
    sum(i.qty * i.price) filter (where p.category = 'garden') as garden
from {{ ref('stg_orders') }} as o
join {{ source('app', 'order_items') }} as i on i.order_id = o.order_id
join {{ source('app', 'products') }} as p on p.product_id = i.product_id
group by o.customer_id
