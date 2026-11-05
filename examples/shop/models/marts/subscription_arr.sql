-- Annual recurring revenue per subscription.
select customer_id, start_date, end_date, mrr * 12 as arr
from {{ source('app', 'subscriptions') }}
