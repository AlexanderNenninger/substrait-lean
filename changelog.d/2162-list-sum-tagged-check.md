### Written list_sum raises sverify's tagged check

`list_sum` past 64 bits now raises sverify's own tagged check ("list_sum out of range") in the written SQL, instead of DuckDB's untagged cast error. The report and the semantics are unchanged (#2162).
