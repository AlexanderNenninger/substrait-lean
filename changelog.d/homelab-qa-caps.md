### `homelab_qa.sh` takes its worker count, niceness and directory prefix from the environment

`PYTEST_XDIST_AUTO_NUM_WORKERS`, `HOMELAB_QA_NICE`, `HOMELAB_QA_PREFIX` and `HOMELAB_QA_CHECK_GENERATED` override the defaults (6, 10, `substrait-lean`, true). The Lean build and the tests run in separate memory scopes, the build's capped by `HOMELAB_QA_BUILD_MEMORY_MAX`, so the background chaos run can build at 8 GB and test at 2 GB beside one QA run.
