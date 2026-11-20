# What sverify proves of the shop project

Every data test and contract constraint of `examples/shop`, and what blocks
the ones `sverify-dbt check` does not prove. Measured on 2026-11-05, and the last column on 2026-11-19.

| | First written (`06bab94b`) | With the suggested test (`06bab94b`) | 2026-11-19 (`f931cf1a`) |
|---|---|---|---|
| Proved | 16 of 26 | 17 of 26 | 23 of 26 |
| Provable with work in sverify | | 7 | 1 |
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

Measured on 2026-11-19 (`sverify-dbt check examples/shop`): 21 of the 24 data tests and both contract constraints are proved (23 of 26). String value sets ([#708], closed) now prove every `accepted_values` test.

| Model | Test | Blocked by | Class |
|---|---|---|---|
| `orders_with_city` | `unique(order_id)` | The point-in-time join matches one version only if a customer's `[valid_from, valid_to)` ranges don't overlap. A real project states that with `dbt_utils.mutually_exclusive_ranges` on `customer_history`, and sverify would need that as a precondition and a key rule for range joins (no issue yet, large) | provable with work |
| `stg_order_items` | `unique(item_key)` | Two keys may hash alike: `md5` is not injective, and the model rightly does not assume it | not provable |
| `org_depth` | `unique(emp_id)` | The model is refused (`WITH RECURSIVE`, [#320]). Even read, an employee appears once only if the manager graph has no cycle, which is a property of the data no test here states | not provable |

[#320]: https://github.com/AlexanderNenninger/substrait-lean/issues/320
[#708]: https://github.com/AlexanderNenninger/substrait-lean/issues/708
