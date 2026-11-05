### A DATE as a TIMESTAMP, and more temporal functions in SQL

The model casts a DATE to a TIMESTAMP, its midnight, and a timestamp to its
microseconds since 1970. So `CAST(d AS TIMESTAMP)`, `date_trunc` of a DATE
column and `DATE ± INTERVAL`, which DuckDB types as TIMESTAMPs, lift and
verify as output columns and in aggregates, and a DATE column compares with
a timestamp ([#807](https://github.com/AlexanderNenninger/substrait-lean/issues/807)).
The SQL lift reads `date_diff` in every unit from microseconds to years,
`epoch`, `extract(epoch …)`, `epoch_us`, `make_date`, `last_day`, `dayname`,
`monthname`, `isodow` and `isoyear`, and the Ibis API's `ibis.date` of
columns verifies
([#809](https://github.com/AlexanderNenninger/substrait-lean/issues/809)).
The new casts and `make_date` of columns run on DuckDB; other engines refuse
them until #271.

Writing a DATE's parts for DuckDB takes `date_part` of the date itself, three
times faster on 5,000,000 dates.
