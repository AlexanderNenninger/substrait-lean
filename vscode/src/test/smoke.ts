// A smoke test without VS Code: the checker process on the demo files, and
// the live contract check. `npm test` (SVERIFY_PYTHON picks the interpreter).

import * as assert from "assert";
import * as path from "path";
import { Checker } from "../checker";
import { liveColumnProblems } from "../contracts";

async function main(): Promise<void> {
  const root = path.resolve(__dirname, "../..");
  const python = process.env.SVERIFY_PYTHON ?? path.resolve(root, "../python/.venv/bin/python");
  const checker = new Checker(python, root, path.join(root, "demo"), () => {});
  const ready = await checker.start();
  console.log(`checker ready: sverify ${ready.sverify}, imports ${ready.import_seconds} s`);
  try {
    const t0 = Date.now();
    const orders = await checker.check(path.join(root, "demo/orders.py"), 0);
    console.log(`orders.py: ${Date.now() - t0} ms`);
    const byName = Object.fromEntries(orders.subjects.map((s) => [s.name, s]));
    assert.strictEqual(byName.doubled.proved, true);
    assert.strictEqual(byName.plus_one.proved, false);
    const needs = orders.diagnostics.filter((d) => d.code === "needs" && d.message.includes("qty != 0"));
    assert.strictEqual(needs.length, 1, "unit_price needs qty != 0");
    assert.ok(needs[0].fixes.some((f) => f.title.startsWith("Guard the division")));
    assert.ok(orders.diagnostics.some((d) => d.code === "unknown-column" && d.message.includes("amout")));
    assert.ok(orders.hovers.length > 0 && orders.lenses.length >= 5);

    for (const f of ["payments.py", "sensors.py", "mart.py"]) {
      const t = Date.now();
      const r = await checker.check(path.join(root, "demo", f), 0);
      console.log(`${f}: ${Date.now() - t} ms, ${r.subjects.map((s) => `${s.name} ${s.proved ? "proved" : "not proved"}`).join(", ")}`);
    }

    const site = orders.sites.find((s) => s.role === "requires" && s.table === "orders")!;
    const text = 'x = {"orders": [_.amonut >= 0, sv.unique("idd")]}';
    const problems = liveColumnProblems(text, [{ ...site, range: [0, 4, 0, text.length] }]);
    assert.deepStrictEqual(
      problems.map((p) => [p.replacement, text.slice(p.range[1], p.range[3])]),
      [["amount", "amonut"], ["id", "idd"]],
    );
    console.log("ok");
  } finally {
    checker.stop();
  }
}

main().catch((e) => {
  console.error(e);
  process.exit(1);
});
