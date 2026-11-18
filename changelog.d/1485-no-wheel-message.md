### A clear message where no wheel exists

PyPI carries wheels for Linux (x86_64, aarch64) and macOS on Apple silicon. On Windows and Intel macOS, `pip install sverify` used to fall back to the sdist, which needs elan and a full `lake build`. The sdist's build now stops at once and names the platforms with a wheel, WSL2 or a container as the way out, and `SVERIFY_BUILD_FROM_SOURCE=1` for building from source (#1485).
