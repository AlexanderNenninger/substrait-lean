### SQLGlot from 30.8, beside SQLMesh

`sverify` requires `sqlglot>=30.8.0,<30.18` in place of `~=30.17.0`. The lift's tests pass on every release from 30.8, the one SQLMesh 0.235 and later pin, so `pip install sverify sqlmesh` resolves to a current SQLMesh in place of falling back to 0.4.1 (#1485).
