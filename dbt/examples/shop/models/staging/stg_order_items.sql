-- Order items with a surrogate key (catalogue: dbt-surrogate-key), as
-- dbt_utils.generate_surrogate_key writes it.
select
    {{ dbt_utils.generate_surrogate_key(['order_id', 'product_id']) }} as item_key,
    order_id,
    product_id,
    qty,
    price
from {{ source('app', 'order_items') }}
