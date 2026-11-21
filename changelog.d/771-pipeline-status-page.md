### A status page per pipeline in the pipeline template

The pipeline template's catalog now has a phone-friendly status page for each pipeline, `status-<file>.html`. It shows the last refresh (with a link to its run), the rows each node wrote and stores, the contract the check proved, and the next scheduled refresh, read from `refresh.yml`'s schedule. The existing `pages` workflow publishes it with the catalog ([#771](https://github.com/AlexanderNenninger/substrait-lean/issues/771)).
