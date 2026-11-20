### ODCS: `missingValues` rules that list values read

`odcs.read` raised `TypeError` on a `missingValues` rule that listed values. It now reads the rule as the column being neither NULL nor one of the values (#1886).
