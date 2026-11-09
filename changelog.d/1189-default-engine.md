### The default engine is the plugin's

- Where no engine is named (`sv.connect()`, `Node.refresh()`, `sverify refresh`),
  plans run on the installed engine whose plugin is the default
  (`ProfilePlugin.default`: DuckDB), or else the first local one. With no engine
  installed, running a plan is an error that names what to install; `verify`
  needs no engine ([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189),
  [#1288](https://github.com/AlexanderNenninger/substrait-lean/issues/1288)).
- An engine whose integer `//` and `%` floor says so in its plugin
  (`ProfilePlugin.floor_division`, Polars's); the Ibis producer and the division
  hints read it, where they named Polars before.
