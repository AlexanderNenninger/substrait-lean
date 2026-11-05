"""Revenue per city and day (tour notebook 3), in Ibis and in SQL.

The left join leaves `city` NULL for an order without a history row, so
`_.city.notnull()` is not proved for `first_try`. `daily_city_revenue`
fills it with "unknown". The SQL model divides by `n_orders`.
"""

import datetime as dt

import ibis
import sverify as sv
from ibis import _

orders = ibis.table(
    {
        "order_id": "!int64",
        "customer_id": "!int64",
        "amount_cents": "!int64",
        "order_ts": "!timestamp",
    },
    name="orders",
)
history = ibis.table(
    {
        "customer_id": "!int64",
        "city": "!string",
        "valid_from": "!timestamp",
        "valid_to": "timestamp",
    },
    name="history",
)


def city_day_revenue(orders, history, unknown_city=None):
    h = history
    joined = orders.left_join(
        h,
        (orders.customer_id == h.customer_id)
        & (h.valid_from <= orders.order_ts)
        & (h.valid_to.isnull() | (orders.order_ts < h.valid_to)),
    )
    city = h.city if unknown_city is None else h.city.fill_null(unknown_city)
    return (
        joined.select(city=city, day=orders.order_ts.truncate("D"), amount_cents=orders.amount_cents)
        .group_by(["city", "day"])
        .aggregate(n_orders=_.count(), revenue_cents=_.amount_cents.sum())
        .mutate(revenue_cents=_.revenue_cents.fill_null(0))
    )


REQUIRES = {
    "orders": [
        sv.unique("order_id"),
        _.amount_cents >= 0,
        _.order_ts >= dt.datetime(2000, 1, 1),
    ]
}
ENSURES = [_.city.notnull(), _.day.notnull(), sv.unique("city", "day"), _.revenue_cents >= 0]

first_try = sv.verify(city_day_revenue(orders, history), requires=REQUIRES, ensures=ENSURES)


@sv.transform(requires=REQUIRES, ensures=ENSURES)
def daily_city_revenue(orders, history):
    return city_day_revenue(orders, history, unknown_city="unknown")


MODEL_SQL = """
select coalesce(h.city, 'unknown') as city,
       date_trunc('day', o.order_ts) as day,
       count(*) as n_orders,
       coalesce(sum(o.amount_cents), 0) as revenue_cents,
       sum(o.amount_cents) / count(o.order_id) as mean_cents
from orders o
left join history h
  on o.customer_id = h.customer_id
 and h.valid_from <= o.order_ts
 and (h.valid_to is null or o.order_ts < h.valid_to)
group by coalesce(h.city, 'unknown'), date_trunc('day', o.order_ts)
"""

sql_report = sv.verify(
    MODEL_SQL,
    tables={"orders": orders, "history": history},
    requires={"orders": ["amount_cents >= 0", sv.unique("order_id")]},
    ensures=["city is not null", "revenue_cents >= 0", sv.unique("city", "day")],
)
