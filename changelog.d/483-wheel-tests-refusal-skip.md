### The installed wheel's tests skip the refusal-message scan

`test_refusal_messages.py` reads the repository's sources, which the Wheels
workflow's copy of the tests against the installed wheel doesn't have. It now
skips there, as `test_scripts.py` does, so the wheel builds pass again
([#483](https://github.com/AlexanderNenninger/substrait-lean/pull/483)).
