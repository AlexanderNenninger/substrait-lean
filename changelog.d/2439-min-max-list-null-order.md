### `to_substrait` exports `min` and `max` of values that are not lists

The default `to_substrait()` refused every `min` and `max`, even of an integer column, naming `list_null_order`: where a NULL element sorts inside a list. That option now matters only where a value of the plan may be a list, so `min` and `max` of integers, doubles and strings export, and of lists still depend on it ([#2439](https://github.com/AlexanderNenninger/substrait-lean/issues/2439)).
