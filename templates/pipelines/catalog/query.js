// The query box of a table's page: DuckDB-WASM in the browser, over the
// table's Parquet files (the site's own snapshot, or the data branch's files).
import * as duckdb from "https://cdn.jsdelivr.net/npm/@duckdb/duckdb-wasm@1.29.0/+esm";

let ready = null;

async function connect(name, files) {
  const bundle = await duckdb.selectBundle(duckdb.getJsDelivrBundles());
  const workerUrl = URL.createObjectURL(
    new Blob([`importScripts("${bundle.mainWorker}");`], { type: "text/javascript" }),
  );
  const db = new duckdb.AsyncDuckDB(new duckdb.VoidLogger(), new Worker(workerUrl));
  await db.instantiate(bundle.mainModule, bundle.pthreadWorker);
  URL.revokeObjectURL(workerUrl);
  const names = [];
  for (const [i, f] of files.entries()) {
    const url = new URL(f, location.href).href;
    const local = `${name}_${i}.parquet`;
    await db.registerFileURL(local, url, duckdb.DuckDBDataProtocol.HTTP, false);
    names.push(`'${local}'`);
  }
  const conn = await db.connect();
  await conn.query(`CREATE VIEW "${name}" AS SELECT * FROM read_parquet([${names.join(", ")}])`);
  return conn;
}

function render(table) {
  const cols = table.schema.fields.map((f) => f.name);
  const head = cols.map((c) => `<th>${escape(c)}</th>`).join("");
  const rows = table.toArray().map((r) => {
    const row = r.toJSON();
    return "<tr>" + cols.map((c) => `<td>${escape(row[c] ?? "")}</td>`).join("") + "</tr>";
  });
  return `<table><thead><tr>${head}</tr></thead><tbody>${rows.join("")}</tbody></table>`;
}

function escape(v) {
  return String(v).replace(/[&<>"]/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" })[c]);
}

export function attach(name, files) {
  const button = document.getElementById("run");
  const out = document.getElementById("result");
  button.addEventListener("click", async () => {
    out.textContent = "Running…";
    try {
      ready ??= connect(name, files);
      const conn = await ready;
      out.innerHTML = render(await conn.query(document.getElementById("sql").value));
    } catch (e) {
      out.textContent = String(e.message ?? e);
    }
  });
}
