### Written list_sum raises sverify's tagged check

`list_sum` past 64 bits now raises sverify's own tagged check ("CAST to a 64-bit integer out of range") in the written SQL, as every written integer cast does, instead of DuckDB's untagged cast error. The report and the semantics are unchanged (#2162).
