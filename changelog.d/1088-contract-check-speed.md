### `verify` checks contracts at their earlier speed again

Since the checker's contract check was split into parsing and checking
(#1088), it built every table's knowledge, its schema parse included, again
at each read of each analysis pass, and a contract check took about twice as
long: TPC-DS q27 743 ms where it took 145 ms. It builds that knowledge once per
request again, and gives the same answers.
