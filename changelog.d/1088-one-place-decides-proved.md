### One place decides "proved"

`Report` alone combines a report's fields into "proved"; the CLI's status of a
discovered transform and the Substrait export now call it. The trusted-base
page lists that decision and every read after it, and a test fails where
another module starts deciding for itself
([#1088](https://github.com/AlexanderNenninger/substrait-lean/issues/1088)).
