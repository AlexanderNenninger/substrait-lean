### Every refusal of the SQL lift names its construct and the SQL it refused

Each refusal of the SQL frontend sets `UnsupportedError.construct` (`"function md5"`, or keywords such as `"CORRELATED SUBQUERY"` and `"TRY CAST"`) and `UnsupportedError.sql`, the innermost part of the query being read, cut at 60 characters. With #1786 every refusal of both frontends names its construct ([#700](https://github.com/AlexanderNenninger/substrait-lean/issues/700), [#1788](https://github.com/AlexanderNenninger/substrait-lean/pull/1788)).
