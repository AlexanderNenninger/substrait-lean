"""A TCP proxy that can go down: the local stand-in for a MinIO restart.

    python _proxy.py <listen port> <target port> <down flag file>

While the flag file exists, the proxy closes every connection, new and
open, as a store that went away does; once it is removed, it forwards
again. It runs as its own process: delta-rs blocks the interpreter that
calls it (`upstream/LEDGER.md` DL-1), so a proxy thread in the test's
process would stall with it.
"""

import contextlib
import os
import socket
import sys
import threading

LISTEN, TARGET, FLAG = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
open_conns: set[socket.socket] = set()
lock = threading.Lock()


def down() -> bool:
    return os.path.exists(FLAG)


def pipe(src: socket.socket, dst: socket.socket) -> None:
    try:
        while not down():
            src.settimeout(0.2)
            try:
                data = src.recv(65536)
            except TimeoutError:
                continue
            if not data:
                break
            dst.sendall(data)
    except OSError:
        pass
    finally:
        for s in (src, dst):
            with lock:
                open_conns.discard(s)
            with contextlib.suppress(OSError):
                s.shutdown(socket.SHUT_RDWR)
            s.close()


def main() -> None:
    server = socket.create_server(("127.0.0.1", LISTEN))
    while True:
        client, _ = server.accept()
        if down():
            client.close()
            continue
        try:
            upstream = socket.create_connection(("127.0.0.1", TARGET))
        except OSError:
            client.close()
            continue
        with lock:
            open_conns.update((client, upstream))
        threading.Thread(target=pipe, args=(client, upstream), daemon=True).start()
        threading.Thread(target=pipe, args=(upstream, client), daemon=True).start()


if __name__ == "__main__":
    main()
