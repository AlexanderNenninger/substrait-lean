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
unproved has a suggestion (`Postcondition.suggested` is empty for each).
One more source test is there for sverify's sake: `customer_updates.updated_at`
below `timestamp '9999-12-31'`, the value `customer_history`'s
`mutually_exclusive_ranges` reads an open `valid_to` as. With it every version
starts before the open end, so the test states `sv.non_overlapping` and the
point-in-time join keeps its key ([#814]).

## Not proved

Measured on 2026-11-21 (`sverify-dbt check examples/shop`): 23 of the 26 data tests and both contract constraints are proved (25 of 28). String value sets ([#708], closed) prove every `accepted_values` test, and non-overlapping ranges ([#814]) the point-in-time join's key.

| Model | Test | Blocked by | Class |
|---|---|---|---|
| `customer_history` | `dbt_utils.mutually_exclusive_ranges` | Its open end is written `coalesce(valid_to, L)`, which no condition of the model's own result states, and the ranges come from `lead(updated_at)`, which sverify derives non-overlapping ranges from only with SCD 2 ([#763]). `dbt build` runs the test before `orders_with_city`, which assumes it | provable with work |
| `stg_order_items` | `unique(item_key)` | Two keys may hash alike: `md5` is not injective, and the model rightly does not assume it | not provable |
| `org_depth` | `unique(emp_id)` | The model is refused (`WITH RECURSIVE`, [#320]). Even read, an employee appears once only if the manager graph has no cycle, which is a property of the data no test here states | not provable |

[#320]: https://github.com/AlexanderNenninger/substrait-lean/issues/320
[#708]: https://github.com/AlexanderNenninger/substrait-lean/issues/708
[#763]: https://github.com/AlexanderNenninger/substrait-lean/issues/763
[#814]: https://github.com/AlexanderNenninger/substrait-lean/issues/814
