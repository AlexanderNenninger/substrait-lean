### sverify-dbt reads mutually_exclusive_ranges

sverify-dbt reads `dbt_utils.mutually_exclusive_ranges` as `sv.non_overlapping`, on plain columns and with an open end written `coalesce(valid_to, L)` when another test keeps every start before `L`. The shop's point-in-time join `orders_with_city` now proves `unique(order_id)` ([#814](https://github.com/AlexanderNenninger/substrait-lean/issues/814)).
