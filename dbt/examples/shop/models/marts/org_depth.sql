-- Each employee's depth below the top of the hierarchy (catalogue:
-- dbt-org-hierarchy).
with recursive chain as (
    select emp_id, 0 as depth from {{ source('app', 'employees') }} where manager_id is null
    union all
    select e.emp_id, c.depth + 1
    from {{ source('app', 'employees') }} as e
    join chain as c on e.manager_id = c.emp_id
    where c.depth < 10
)
select emp_id, depth from chain
