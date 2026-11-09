"""The test suite's hooks and fixtures are a plugin of their own
(`tests/_suite.py`), which the engine packages' tests load too."""

pytest_plugins = ["_suite"]
