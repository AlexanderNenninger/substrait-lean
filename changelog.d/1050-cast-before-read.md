### The unsigned and zoned-timestamp refusals say where the cast goes

- "unsigned integers (uint32) are not supported yet (#350)" and the
  timestamp refusals now say to cast the column before sverify reads the
  table: an Ibis cast after the read does not help, since the read itself
  carries the type
  ([#1050](https://github.com/AlexanderNenninger/substrait-lean/issues/1050)).
