### Fixed: SQL reports described timestamps and dates as integers

The facts of a SQL transformation described its timestamp and date columns
as "any integer", the model's codes for them. They now read as the same
columns written in Ibis do, "any timestamp" and "a date in [...]" (#452).
