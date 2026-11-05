-- One row per region and quarter (catalogue: dbt-unpivot-union).
select region, 'q1' as quarter, q1 as sales from {{ source('app', 'sales_wide') }}
union all
select region, 'q2' as quarter, q2 as sales from {{ source('app', 'sales_wide') }}
union all
select region, 'q3' as quarter, q3 as sales from {{ source('app', 'sales_wide') }}
union all
select region, 'q4' as quarter, q4 as sales from {{ source('app', 'sales_wide') }}
