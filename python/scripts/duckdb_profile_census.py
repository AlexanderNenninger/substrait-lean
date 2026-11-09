"""Each catalogue query verified under semantics="duckdb": proved or not,
and the options the checker's transfer names (#1189 R1b). One JSON line each."""
import json, sys, warnings
warnings.simplefilter("ignore")
sys.path.insert(0, "tools")
from sverify_dev import catalogue as c
import sverify as sv
from sverify import contracts

#: `plan`: each postcondition list gains `sv.equivalent(floats="plan")`.
PLAN = sys.argv[1:] == ["plan"]

answers: list[dict] = []
real = contracts.run_checker
def spy(args, text):
    code, out, err = real(args, text)
    if args == ("--contract",) and out.strip():
        answers.append(json.loads(out))
    return code, out, err
contracts.run_checker = spy

s = c.load_schemas()
for q in c.load_queries():
    if q.requires is None or q.not_expressible:
        continue
    answers.clear()
    row = {"id": q.id}
    try:
        e = c.build(q, s, "native"); req, ens = c.contract(q, s, "native")
        if PLAN:
            ens = [*ens, sv.equivalent(floats="plan")]
        kw = {"tables": c.tables(s, q.dataset, "native")} if isinstance(e, str) else {}
        r = sv.verify(e, requires=req, ensures=ens, semantics="duckdb", **kw)
        row["proved"] = r.proved
        t = (answers[-1].get("transfer") or {}) if answers else {}
        row["transfer_ok"] = t.get("ok")
        row["failures"] = sorted({f["option"] for f in t.get("failures", [])})
    except Exception as ex:  # noqa: BLE001
        row["error"] = f"{type(ex).__name__}: {str(ex)[:120]}"
    print(json.dumps(row), flush=True)
