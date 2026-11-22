### to_substrait casts the narrower input of a set relation

A set relation whose inputs differ in decimal precision (a full outer join of two sums) is written with a cast of the narrower input to the wider precision at the same scale, and reads back (#1904). It was refused for the time between #2106 and this change.
