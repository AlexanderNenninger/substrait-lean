# What sverify proves of the shop project

Every data test and contract constraint of `examples/shop`, and what blocks
the ones `sverify-dbt check` does not prove. Measured on 2026-11-05.

| | First written (`06bab94b`) | With the suggested test (`06bab94b`) | Now (`6c583f0b`) |
|---|---|---|---|
| Proved | 16 of 26 | 17 of 26 | 19 of 26 |
| Provable with work in sverify | | 7 | 5 |
| Not provable | | 2 | 2 |

The 26 are 24 data tests and 2 contract constraints. The first column is
the project as first written, the second adds the one test
`sverify-dbt suggest` proposed (below), and the third is substrait-lean's
`main` after
[#726](https://github.com/AlexanderNenninger/substrait-lean/pull/726) (`md5`
in the SQL lift) and
[#729](https://github.com/AlexanderNenninger/substrait-lean/pull/729) (signs
of double arithmetic), which proved one test each.

## Added from sverify's suggestion

| Test | Why | Proves |
|---|---|---|
| `source('app', 'subscriptions').mrr`: `accepted_range` `max_value: 1000000` | sverify suggested `max_value: 700000000000000000, inclusive: false`, since `mrr * 12` overflows otherwise. A shop would cap a subscription's monthly revenue far lower, and a tighter bound proves the same. | `subscription_arr`: `accepted_range(arr)` |

`sverify-dbt suggest` proposes nothing more: none of the tests left
unproved has a suggestion (`CheckedCondition.suggested` is empty for each).
The project declares no other source test for sverify's sake.

## Not proved

| Model | Test | Blocked by | Class |
|---|---|---|---|
| `stg_orders` | `accepted_values(status)` | String value sets: `status <> 'cancelled'` over the source's four values leaves three, which sverify does not track ([#708]) | provable with work |
| `events_unioned` | `accepted_values(source)` | A string constant in each branch of a `UNION ALL` ([#708]) | provable with work |
| `sales_by_quarter` | `accepted_values(quarter)` | A string constant in each branch of a `UNION ALL` ([#708]) | provable with work |
| `sales_by_quarter` | `unique_combination_of_columns(region, quarter)` | A key through a `UNION ALL` whose branches differ in a constant ([#436], with [#708]) | provable with work |
| `orders_with_city` | `unique(order_id)` | The point-in-time join matches one version only if a customer's `[valid_from, valid_to)` ranges don't overlap. A real project states that with `dbt_utils.mutually_exclusive_ranges` on `customer_history`, and sverify would need that as a precondition and a key rule for range joins (no issue yet, large) | provable with work |
| `stg_order_items` | `unique(item_key)` | Two keys may hash alike: `md5` is not injective, and the model rightly does not assume it | not provable |
| `org_depth` | `unique(emp_id)` | The model is refused (`WITH RECURSIVE`, [#320]). Even read, an employee appears once only if the manager graph has no cycle, which is a property of the data no test here states | not provable |

[#320]: https://github.com/AlexanderNenninger/substrait-lean/issues/320
[#436]: https://github.com/AlexanderNenninger/substrait-lean/issues/436
[#708]: https://github.com/AlexanderNenninger/substrait-lean/issues/708
[#728]: https://github.com/AlexanderNenninger/substrait-lean/pull/728

## By blocker

| Blocker | Tests it would prove |
|---|---|
| [#708] string value sets (with [#436] for the key; [#728] open) | 4 |
| Range-join keys over `mutually_exclusive_ranges` | 1 |

[#702] (domain errors under `semantics="duckdb"`, fixed in #729) blocked
none of these tests: every model's double arithmetic is bounded by its
source tests.

[#702]: https://github.com/AlexanderNenninger/substrait-lean/issues/702

## Proved

| Model | Proved |
|---|---|
| `stg_orders` | `not_null(order_id)`, `unique(order_id)`, `not_null(customer_id)`, `accepted_range(amount)` |
| `customer_history` | `not_null(customer_id)`, `unique_combination_of_columns(customer_id, valid_from)`, `expression_is_true(valid_to > valid_from)` |
| `customer_revenue_by_category` | `accepted_range(books)` (since #729), contract `primary_key(customer_id)` |
| `stg_order_items` | `not_null(item_key)` (since #726) |
| `order_status_counts` | `unique(customer_id)`, `expect_column_values_to_be_between(placed)`, contract `not_null(customer_id)` |
| `orders_with_city` | `not_null(order_id)` |
| `events_unioned` | `not_null(source)`, `accepted_range(amount)` |
| `sales_by_quarter` | `not_null(region)`, `not_null(quarter)` |
| `subscription_arr` | `accepted_range(arr)` (after the suggested test) |
