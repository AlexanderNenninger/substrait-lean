### Text files are read and written as UTF-8 on every platform

sverify names `encoding="utf-8"` wherever it reads or writes a text file: the
SQL files of `sverify check`, ODCS contracts, OpenLineage files, sink records,
secrets files and the proof cache. On Windows, Python's default is the
locale's code page (cp1252), so non-ASCII text in those files failed or was
misread there
([#183](https://github.com/AlexanderNenninger/substrait-lean/issues/183)).
