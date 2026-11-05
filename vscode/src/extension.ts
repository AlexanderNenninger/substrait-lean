// sverify in the editor: on save, the Python checker runs the file's
// `@sv.transform`s and `sv.verify` calls; their reports become diagnostics,
// quick fixes, hovers, code lenses and contract completion.

import * as fs from "fs";
import * as path from "path";
import * as vscode from "vscode";
import { CheckResult, Checker, Fix, Range, Site } from "./checker";
import { helpersFor, liveColumnProblems, shiftRange } from "./contracts";

const SEVERITY = [
  vscode.DiagnosticSeverity.Error,
  vscode.DiagnosticSeverity.Warning,
  vscode.DiagnosticSeverity.Information,
  vscode.DiagnosticSeverity.Hint,
];

function toRange(r: Range): vscode.Range {
  return new vscode.Range(r[0], r[1], r[2], r[3]);
}

class State {
  readonly results = new Map<string, CheckResult>();
  readonly fixes = new WeakMap<vscode.Diagnostic, Fix[]>();
  readonly checkers = new Map<string, Checker>();
  readonly diagnostics = vscode.languages.createDiagnosticCollection("sverify");
  readonly live = vscode.languages.createDiagnosticCollection("sverify-live");
  readonly output = vscode.window.createOutputChannel("sverify");
  readonly status = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 50);
  readonly lensesChanged = new vscode.EventEmitter<void>();
  private running = new Map<string, Promise<void>>();
  private again = new Set<string>();

  constructor(readonly context: vscode.ExtensionContext) {
    this.status.command = "sverify.showReport";
  }

  log(line: string): void {
    this.output.appendLine(line);
  }

  pythonFor(folder: string): string {
    const cfg = vscode.workspace.getConfiguration("sverify");
    const set = cfg.get<string>("pythonPath", "").replace("${workspaceFolder}", folder);
    if (set) {
      return set;
    }
    for (const c of [".venv/bin/python", "python/.venv/bin/python", ".venv/Scripts/python.exe"]) {
      const p = path.join(folder, c);
      if (fs.existsSync(p)) {
        return p;
      }
    }
    return "python3";
  }

  checker(doc: vscode.TextDocument): Checker {
    const folder = vscode.workspace.getWorkspaceFolder(doc.uri)?.uri.fsPath ?? path.dirname(doc.uri.fsPath);
    let c = this.checkers.get(folder);
    if (!c) {
      c = new Checker(this.pythonFor(folder), this.context.extensionPath, folder, (l) => this.log(l));
      this.checkers.set(folder, c);
      c.start().then(
        (r) => this.log(`checker ready: sverify ${r.sverify}, imports took ${r.import_seconds} s`),
        (e) => {
          this.log(`checker failed to start: ${e}`);
          vscode.window.showErrorMessage(
            `sverify: the checker did not start (${e.message}). Set sverify.pythonPath to a Python with sverify installed.`,
          );
        },
      );
    }
    return c;
  }

  restart(): void {
    for (const c of this.checkers.values()) {
      c.stop();
    }
    this.checkers.clear();
  }

  /** Check `doc`; a save during a check queues one more. */
  check(doc: vscode.TextDocument): Promise<void> {
    const key = doc.uri.toString();
    if (this.running.has(key)) {
      this.again.add(key);
      return this.running.get(key)!;
    }
    const run = this.run(doc).finally(() => {
      this.running.delete(key);
      if (this.again.delete(key)) {
        void this.check(doc);
      }
    });
    this.running.set(key, run);
    return run;
  }

  private async run(doc: vscode.TextDocument): Promise<void> {
    const name = path.basename(doc.uri.fsPath);
    this.status.text = `$(sync~spin) sverify: checking ${name}`;
    this.status.tooltip = undefined;
    this.status.show();
    const t0 = Date.now();
    const counterexamples = vscode.workspace.getConfiguration("sverify").get<number | null>("counterexamples", null);
    let result: CheckResult;
    try {
      result = await this.checker(doc).check(doc.uri.fsPath, counterexamples);
    } catch (e: any) {
      this.status.text = `$(error) sverify: ${e.message ?? e}`;
      this.log(String(e?.stack ?? e));
      return;
    }
    const ms = Date.now() - t0;
    this.results.set(doc.uri.toString(), result);
    this.publish(doc.uri, result);
    this.live.delete(doc.uri);
    this.lensesChanged.fire();
    const checked = result.subjects.filter((s) => s.checked);
    const proved = checked.filter((s) => s.proved).length;
    const icon = proved === checked.length ? "$(pass)" : "$(error)";
    this.status.text = checked.length
      ? `${icon} sverify: ${proved}/${checked.length} proved (${(ms / 1000).toFixed(1)} s)`
      : `sverify: nothing to check in ${name}`;
    this.status.tooltip = result.subjects.map((s) => s.summary ?? `${s.name}: not checked`).join("\n");
    this.log(`checked ${name} in ${ms} ms (checker ${result.seconds} s)`);
  }

  publish(uri: vscode.Uri, result: CheckResult, hideCodes: Set<string> = new Set()): void {
    const out: vscode.Diagnostic[] = [];
    for (const d of result.diagnostics) {
      if (hideCodes.has(d.code)) {
        continue;
      }
      const diag = new vscode.Diagnostic(toRange(d.range), d.message, SEVERITY[d.severity]);
      diag.source = "sverify";
      diag.code = d.code;
      this.fixes.set(diag, d.fixes);
      out.push(diag);
    }
    this.diagnostics.set(uri, out);
  }
}

function usesSverify(doc: vscode.TextDocument): boolean {
  return doc.languageId === "python" && doc.uri.scheme === "file" && doc.getText().includes("sverify");
}

export function activate(context: vscode.ExtensionContext): void {
  const state = new State(context);
  const selector: vscode.DocumentSelector = { language: "python", scheme: "file" };
  const onSave = () => vscode.workspace.getConfiguration("sverify").get<boolean>("checkOnSave", true);

  context.subscriptions.push(
    state.diagnostics,
    state.live,
    state.output,
    state.status,
    vscode.workspace.onDidSaveTextDocument((doc) => {
      if (onSave() && usesSverify(doc)) {
        void state.check(doc);
      }
    }),
    vscode.workspace.onDidOpenTextDocument((doc) => {
      if (onSave() && usesSverify(doc) && !state.results.has(doc.uri.toString())) {
        void state.check(doc);
      }
    }),
    vscode.workspace.onDidChangeTextDocument((e) => onChange(state, e)),
    vscode.workspace.onDidCloseTextDocument((doc) => {
      state.diagnostics.delete(doc.uri);
      state.live.delete(doc.uri);
      state.results.delete(doc.uri.toString());
    }),
    vscode.workspace.onDidChangeConfiguration((e) => {
      if (e.affectsConfiguration("sverify.pythonPath")) {
        state.restart();
      }
    }),
    vscode.commands.registerCommand("sverify.check", () => {
      const doc = vscode.window.activeTextEditor?.document;
      if (doc) {
        void state.check(doc);
      }
    }),
    vscode.commands.registerCommand("sverify.restart", () => state.restart()),
    vscode.commands.registerCommand("sverify.showReport", (uri?: vscode.Uri, subject?: number) => showReport(state, uri, subject)),
    vscode.languages.registerCodeActionsProvider(selector, new FixProvider(state), {
      providedCodeActionKinds: [vscode.CodeActionKind.QuickFix],
    }),
    vscode.languages.registerHoverProvider(selector, new HoverProvider(state)),
    vscode.languages.registerCodeLensProvider(selector, new LensProvider(state)),
    vscode.languages.registerCompletionItemProvider(selector, new ContractCompletion(state), ".", '"', "'"),
    { dispose: () => state.restart() },
  );
  for (const doc of vscode.workspace.textDocuments) {
    if (onSave() && usesSverify(doc)) {
      void state.check(doc);
    }
  }
}

export function deactivate(): void {}

/** Keep the contract sites in place while the file is edited, and check
 * the columns a contract names as it is typed. */
function onChange(state: State, e: vscode.TextDocumentChangeEvent): void {
  const result = state.results.get(e.document.uri.toString());
  if (!result || e.contentChanges.length === 0) {
    return;
  }
  for (const change of e.contentChanges) {
    const added = change.text.split("\n").length - 1;
    const removed = change.range.end.line - change.range.start.line;
    const delta = added - removed;
    const at = [change.range.start.line, change.range.end.line] as const;
    for (const s of result.sites) {
      s.range = shiftRange(s.range, at, delta);
    }
    for (const h of result.hovers) {
      h.range = shiftRange(h.range, at, delta);
    }
    for (const l of result.lenses) {
      l.range = shiftRange(l.range, at, delta);
    }
  }
  const problems = liveColumnProblems(e.document.getText(), result.sites);
  state.live.set(
    e.document.uri,
    problems.map((p) => {
      const d = new vscode.Diagnostic(toRange(p.range), p.message, vscode.DiagnosticSeverity.Error);
      d.source = "sverify";
      d.code = "unknown-column";
      if (p.replacement) {
        state.fixes.set(d, [
          { title: `Change to \`${p.replacement}\``, edits: [{ range: p.range, newText: p.replacement }], preferred: true, preview: false },
        ]);
      }
      return d;
    }),
  );
  // The checker's own column findings are stale now; the live ones replace them.
  state.publish(e.document.uri, result, new Set(["unknown-column"]));
}

class FixProvider implements vscode.CodeActionProvider {
  constructor(private readonly state: State) {}

  provideCodeActions(doc: vscode.TextDocument, _range: vscode.Range, ctx: vscode.CodeActionContext): vscode.CodeAction[] {
    const preview = vscode.workspace.getConfiguration("sverify").get<boolean>("previewFixes", true);
    const out: vscode.CodeAction[] = [];
    const seen = new Set<string>();
    for (const diag of ctx.diagnostics) {
      for (const fix of this.state.fixes.get(diag) ?? []) {
        if (seen.has(fix.title)) {
          continue;
        }
        seen.add(fix.title);
        const action = new vscode.CodeAction(fix.title, vscode.CodeActionKind.QuickFix);
        const edit = new vscode.WorkspaceEdit();
        for (const e of fix.edits) {
          const meta = preview && fix.preview ? { needsConfirmation: true, label: fix.title } : undefined;
          edit.replace(doc.uri, toRange(e.range), e.newText, meta);
        }
        action.edit = edit;
        action.diagnostics = [diag];
        action.isPreferred = fix.preferred;
        out.push(action);
      }
    }
    return out;
  }
}

class HoverProvider implements vscode.HoverProvider {
  constructor(private readonly state: State) {}

  provideHover(doc: vscode.TextDocument, pos: vscode.Position): vscode.Hover | undefined {
    const result = this.state.results.get(doc.uri.toString());
    if (!result) {
      return undefined;
    }
    let best: { range: vscode.Range; markdown: string } | undefined;
    for (const h of result.hovers) {
      const r = toRange(h.range);
      if (r.contains(pos) && (!best || best.range.contains(r))) {
        best = { range: r, markdown: h.markdown };
      }
    }
    if (!best) {
      return undefined;
    }
    const md = new vscode.MarkdownString(best.markdown);
    md.supportHtml = false;
    return new vscode.Hover(md, best.range);
  }
}

class LensProvider implements vscode.CodeLensProvider {
  readonly onDidChangeCodeLenses: vscode.Event<void>;

  constructor(private readonly state: State) {
    this.onDidChangeCodeLenses = state.lensesChanged.event;
  }

  provideCodeLenses(doc: vscode.TextDocument): vscode.CodeLens[] {
    const result = this.state.results.get(doc.uri.toString());
    return (result?.lenses ?? []).map(
      (l) =>
        new vscode.CodeLens(toRange(l.range), {
          title: l.title,
          command: "sverify.showReport",
          arguments: [doc.uri, l.subject],
        }),
    );
  }
}

class ContractCompletion implements vscode.CompletionItemProvider {
  constructor(private readonly state: State) {}

  provideCompletionItems(doc: vscode.TextDocument, pos: vscode.Position): vscode.CompletionItem[] | undefined {
    const result = this.state.results.get(doc.uri.toString());
    const before = doc.lineAt(pos.line).text.slice(0, pos.character);
    const site = result?.sites.find((s) => toRange(s.range).contains(pos));
    const helper = /\b(sv|sverify)\.(\w*)$/.exec(before);
    if (helper) {
      return helpersFor(site?.role).map((h) => {
        const item = new vscode.CompletionItem(h.name, vscode.CompletionItemKind.Function);
        item.insertText = new vscode.SnippetString(h.snippet);
        item.detail = h.detail;
        item.documentation = new vscode.MarkdownString(h.doc);
        item.sortText = `0${h.name}`;
        return item;
      });
    }
    if (!site) {
      return undefined;
    }
    if (/(?<![\w.])_\.\w*$/.test(before) || /\b(unique|rows_per)\(\[?(["'][^"']*["'],\s*)*["']\w*$/.test(before)) {
      return columns(site);
    }
    return undefined;
  }
}

function columns(site: Site): vscode.CompletionItem[] {
  const where = site.role === "ensures" ? "output" : `input ${site.table ?? ""}`;
  return Object.entries(site.columns).map(([name, type]) => {
    const item = new vscode.CompletionItem(name, vscode.CompletionItemKind.Field);
    item.detail = `${type} (${where})`;
    item.sortText = `0${name}`;
    return item;
  });
}

async function showReport(state: State, uri?: vscode.Uri, subject?: number): Promise<void> {
  const doc = uri ? undefined : vscode.window.activeTextEditor?.document;
  const key = (uri ?? doc?.uri)?.toString();
  const result = key ? state.results.get(key) : undefined;
  if (!result) {
    vscode.window.showInformationMessage("sverify: no report for this file yet; save it to check it.");
    return;
  }
  const subjects = subject === undefined ? result.subjects : [result.subjects[subject]];
  const parts = subjects.map((s) => {
    const routes = Object.entries(s.routes ?? {})
      .map(([e, r]) => `| ${e} | ${r.kind ?? "refused"} | ${r.cls ?? "?"} | ${(r.observation ?? r.reason ?? "").replace(/\|/g, "/")} |`)
      .join("\n");
    return [
      `## ${s.name} (${s.kind})`,
      "",
      s.checked ? "```text\n" + (s.report ?? "") + "\n```" : "not checked",
      "",
      routes ? "| engine | route | class | |\n|---|---|---|---|\n" + routes : "",
    ].join("\n");
  });
  const md = await vscode.workspace.openTextDocument({ language: "markdown", content: parts.join("\n\n") });
  await vscode.window.showTextDocument(md, { viewColumn: vscode.ViewColumn.Beside, preview: true });
}
