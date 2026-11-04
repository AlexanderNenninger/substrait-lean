"""The process's DuckDB database (`sverify._duckdb`): a resident's weakref
finalizer queues it to be dropped (`forget`), and the garbage collector may
run it while this thread holds the module's lock, inside `cursor` or
`collect`. That deadlocked the process (tests hung in `cursor`)."""

import threading

from sverify import _duckdb


def run(fn) -> bool:
    """Whether `fn` returns within ten seconds."""
    t = threading.Thread(target=fn, daemon=True)
    t.start()
    t.join(10)
    return not t.is_alive()


def test_forget_while_the_lock_is_held():
    def finalizer_inside_cursor():
        with _duckdb._LOCK:  # as in `cursor`, when the collector runs
            _duckdb.forget("sverify_gone", "TABLE")

    assert run(finalizer_inside_cursor)
    assert ("sverify_gone", "TABLE") in _duckdb._GONE
    _duckdb.collect(_duckdb.cursor())
    assert ("sverify_gone", "TABLE") not in _duckdb._GONE
