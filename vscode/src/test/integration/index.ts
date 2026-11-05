// In the extension host: open demo/orders.py and read what the extension
// provides through VS Code's own commands.

import * as assert from "assert";
import * as path from "path";
import * as vscode from "vscode";

async function waitFor<T>(what: string, get: () => T | undefined, ms = 60000): Promise<T> {
  const end = Date.now() + ms;
  for (;;) {
    const v = get();
    if (v !== undefined) {
      return v;
    }
    if (Date.now() > end) {
      throw new Error(`timed out waiting for ${what}`);
    }
    await new Promise((r) => setTimeout(r, 200));
  }
}

function find(doc: vscode.TextDocument, text: string, from = 0): vscode.Position {
  const i = doc.getText().indexOf(text, doc.offsetAt(new vscode.Position(from, 0)));
  assert.ok(i >= 0, `${text} in ${doc.fileName}`);
  return doc.positionAt(i);
}

export async function run(): Promise<void> {
  const folder = vscode.workspace.workspaceFolders![0].uri.fsPath;
  const uri = vscode.Uri.file(path.join(folder, "orders.py"));
  const doc = await vscode.workspace.openTextDocument(uri);
  const editor = await vscode.window.showTextDocument(doc);
  const t0 = Date.now();
  const diags = await waitFor("diagnostics", () => {
    const d = vscode.languages.getDiagnostics(uri).filter((x) => x.source === "sverify");
    return d.length ? d : undefined;
  });
  const out: string[] = [`diagnostics after ${Date.now() - t0} ms (first check, cold):`];
  for (const d of diags) {
    out.push(`  ${d.range.start.line + 1}:${d.range.start.character + 1} [${d.code}] ${d.message.split("\n")[0]}`);
  }

  // Quick fixes on the division of unit_price.
  const div = find(doc, "orders.amount // orders.qty");
  const actions = (await vscode.commands.executeCommand<vscode.CodeAction[]>(
    "vscode.executeCodeActionProvider",
    uri,
    new vscode.Range(div, div.translate(0, 5)),
  ))!.filter((a) => a.kind?.value === "quickfix");
  out.push("quick fixes at `orders.amount // orders.qty`:", ...actions.map((a) => `  ${a.isPreferred ? "*" : " "} ${a.title}`));
  assert.ok(actions.some((a) => a.title === "Add _.qty != 0 to requires of orders"));
  assert.ok(actions.some((a) => a.title.startsWith("Guard the division")));

  // Hovers: the transform, and an output column.
  const name = find(doc, "doubled(orders)");
  const hovers = (await vscode.commands.executeCommand<vscode.Hover[]>("vscode.executeHoverProvider", uri, name.translate(0, 2)))!;
  const md = hovers.flatMap((h) => h.contents.map((c) => (c as vscode.MarkdownString).value ?? String(c))).join("\n");
  out.push("hover on `def doubled`:", ...md.split("\n").map((l) => `  | ${l}`));
  assert.ok(md.includes("sverify: doubled — proved"), md);
  assert.ok(md.includes("| duckdb |"), md);

  // Code lenses.
  const lenses = (await vscode.commands.executeCommand<vscode.CodeLens[]>("vscode.executeCodeLensProvider", uri))!;
  const titles = lenses.map((l) => l.command?.title ?? "").filter((t) => t.startsWith("sverify"));
  out.push("code lenses:", ...titles.map((t) => `  ${t}`));
  assert.ok(titles.length >= 5);

  // Completion inside a contract: columns after `_.`, helpers after `sv.`.
  const req = find(doc, "_.amount >= 0, _.amount < 1_000_000_000");
  await editor.edit((e) => e.insert(req, "_.am"));
  const cols = (await vscode.commands.executeCommand<vscode.CompletionList>(
    "vscode.executeCompletionItemProvider",
    uri,
    req.translate(0, 4),
  ))!.items.filter((i) => typeof i.detail === "string" && i.detail.includes("(input orders)"));
  out.push("completion after `_.` in requires:", ...cols.map((i) => `  ${i.label} ${i.detail}`));
  assert.ok(cols.some((i) => i.label === "amount"));
  // The typed `_.am_.amount` is no column: the live check flags it.
  const live = await waitFor("live diagnostic", () =>
    vscode.languages.getDiagnostics(uri).find((d) => d.code === "unknown-column" && d.range.start.line === req.line && d.message.includes("am_")) ?? undefined,
  ).catch(() => undefined);
  out.push(`live check of the typed column: ${live ? live.message : "(none)"}`);
  await editor.edit((e) => e.delete(new vscode.Range(req, req.translate(0, 4))));

  const ens = find(doc, "ensures=[_.total > 5]");
  const at = ens.translate(0, "ensures=[".length);
  await editor.edit((e) => e.insert(at, "sv."));
  const helpers = (await vscode.commands.executeCommand<vscode.CompletionList>(
    "vscode.executeCompletionItemProvider",
    uri,
    at.translate(0, 3),
  ))!.items.filter((i) => typeof i.detail === "string" && i.detail.startsWith("sv."));
  out.push("completion after `sv.` in ensures:", ...helpers.map((i) => `  ${i.label}: ${i.detail}`));
  assert.ok(helpers.some((i) => i.label === "equivalent"));
  assert.ok(!helpers.some((i) => i.label === "references"));
  await editor.edit((e) => e.delete(new vscode.Range(at, at.translate(0, 3))));
  assert.ok(!doc.getText().includes("_.am_") && !doc.getText().includes("sv._"), "the edits are gone");

  // A second check, warm: save the file.
  const t1 = Date.now();
  await doc.save();
  await new Promise((r) => setTimeout(r, 300));
  out.push(`saved; status bar shows the check (warm) after ~${Date.now() - t1} ms`);
  console.log(out.join("\n"));
}
