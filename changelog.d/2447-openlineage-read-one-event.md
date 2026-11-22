### OpenLineage: `read` takes a file holding one event over several lines

`sverify.openlineage.read` reads a JSON file holding one event written over several lines, as `jq .` or Marquez's UI save it. It used to fail with a `JSONDecodeError` ([#2447](https://github.com/AlexanderNenninger/substrait-lean/issues/2447)).
