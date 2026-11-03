### No more Intel macOS wheels

Wheels exist for Linux (x86_64, aarch64) and macOS on Apple silicon (arm64).
On an Intel Mac, pip and uv build `sverify` from the sdist, which needs
[elan](https://github.com/leanprover/elan).
