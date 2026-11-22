### The CLI's time budget stops cleanly where there is no SIGALRM

On Windows, `sverify check --timeout` (and `SVERIFY_TIMEOUT`) now raises the
budget's error in the main thread when time runs out, so the command prints
what it proved before stopping, as on Linux and macOS. Before, only the
watchdog stopped it, ending the process without the partial report
([#183](https://github.com/AlexanderNenninger/substrait-lean/issues/183)).
