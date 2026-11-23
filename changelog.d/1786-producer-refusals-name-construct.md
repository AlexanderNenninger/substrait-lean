### Every refusal of the Ibis producer names its construct

Each refusal of the Ibis frontend sets `UnsupportedError.construct`: `"function <name>"` for a function, otherwise SQL keywords in upper case (`"LAMBDA"`, `"FRAME"`, `"INTERVAL"`, `"JOIN"`). A tool can group refusals by it without reading the message, whose text is unchanged ([#700](https://github.com/AlexanderNenninger/substrait-lean/issues/700), [#1786](https://github.com/AlexanderNenninger/substrait-lean/pull/1786)).
