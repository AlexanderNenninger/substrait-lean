### The checker's slow cases

- The checker's abstract evaluation no longer evaluates a projection's or an
  aggregate's input once per expression, which grew exponentially with the
  plan's depth: TPC-DS q36 took 56 s per proof and takes 0.8 s, and the
  catalogue's 55 contracts 110 s and 5 s
  ([#825](https://github.com/AlexanderNenninger/substrait-lean/issues/825)).
  A decimal cast's bounds, each table's description and a plan with
  `VALUES` cost less too.
