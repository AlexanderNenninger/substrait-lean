### Nightly wheels

Each night, when `main` has changed, the Wheels workflow builds and tests the
wheels for every platform and publishes them as the rolling
[`nightly` pre-release](https://github.com/AlexanderNenninger/substrait-lean/releases/tag/nightly),
versioned `<next minor>.dev<commits>+g<sha>`. Install them with
`uv add "sverify>=0.4.0.dev0" --find-links https://github.com/AlexanderNenninger/substrait-lean/releases/expanded_assets/nightly`
or `pip install --pre sverify --find-links …`; `python/README.md` has the
details. Each build's wheels stay on the release for 30 days, so a pinned wheel
URL works that long. They never go to PyPI.
