### `substrait-check --help`

The Lean checker prints a usage page for `--help` and `-h`: its flags grouped
(checking a plan, diagnostics, serving, tables and coverage), one line each,
with an example and the exit codes. An unknown flag, a flag used without its
file and a file it can't read are usage errors with one line on stderr and
exit 2, where they ended in an uncaught exception before
([#2239](https://github.com/AlexanderNenninger/substrait-lean/issues/2239)).
The flags keep their names.
