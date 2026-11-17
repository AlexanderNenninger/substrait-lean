### The SQL writer's refusals say what to do

A plan the SQL writer cannot write now ends with a fix or a way out: a malformed plan says to build it with sverify or fix it, and the other refusals say to rewrite the step or run the plan with another engine. `python -m sverify_dev.exits` counts the refusals that still name nothing, and a test keeps the count from rising ([#1205](https://github.com/AlexanderNenninger/substrait-lean/issues/1205)).
