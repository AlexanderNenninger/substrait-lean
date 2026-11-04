### `homelab_qa.sh` takes its worker count, niceness and directory prefix from the environment

`PYTEST_XDIST_AUTO_NUM_WORKERS`, `HOMELAB_QA_NICE` and `HOMELAB_QA_PREFIX` override the defaults (6, 10, `substrait-lean`), so the background chaos run can go capped beside one QA run.
