// The Python checker process (`python -m sverify_vscode serve`): one per
// workspace folder, answering JSON-lines requests on stdin and stdout.

import { ChildProcess, spawn } from "child_process";
import * as path from "path";
import * as readline from "readline";

/** A range as the checker sends it: start line, start character, end line, end character. */
export type Range = [number, number, number, number];

export interface Edit {
  range: Range;
  newText: string;
}

export interface Fix {
  title: string;
  edits: Edit[];
  preferred: boolean;
  preview: boolean;
}

export interface Diagnostic {
  range: Range;
  severity: number; // 0 error, 1 warning, 2 information, 3 hint
  message: string;
  code: string;
  subject: number;
  fixes: Fix[];
}

export interface RouteInfo {
  kind: string | null;
  cls: string | null;
  evidence?: string | null;
  observation?: string | null;
  shims?: string[];
  reason: string;
  suggested?: Record<string, string[]>;
}

export interface Subject {
  kind: "transform" | "verify";
  name: string;
  range: Range;
  checked: boolean;
  proved?: boolean;
  seconds?: number;
  summary?: string;
  routes?: Record<string, RouteInfo>;
  report?: string;
}

export interface Site {
  range: Range;
  role: "requires" | "ensures";
  table: string | null;
  columns: Record<string, string>;
  subject: number;
}

export interface CheckResult {
  file: string;
  seconds: number;
  subjects: Subject[];
  diagnostics: Diagnostic[];
  hovers: { range: Range; markdown: string }[];
  lenses: { range: Range; title: string; subject: number }[];
  sites: Site[];
}

interface Pending {
  resolve: (v: any) => void;
  reject: (e: Error) => void;
}

export class Checker {
  private proc: ChildProcess | undefined;
  private pending = new Map<number, Pending>();
  private next = 1;
  private ready: Promise<{ sverify: string | null; import_seconds: number }> | undefined;

  constructor(
    private readonly python: string,
    private readonly extensionPath: string,
    private readonly cwd: string,
    private readonly log: (line: string) => void,
  ) {}

  start(): Promise<{ sverify: string | null; import_seconds: number }> {
    if (this.ready) {
      return this.ready;
    }
    const env = { ...process.env, PYTHONPATH: path.join(this.extensionPath, "python"), PYTHONUNBUFFERED: "1" };
    this.log(`starting ${this.python} -m sverify_vscode serve in ${this.cwd}`);
    const proc = spawn(this.python, ["-m", "sverify_vscode", "serve"], { cwd: this.cwd, env });
    this.proc = proc;
    proc.stderr?.on("data", (d: Buffer) => this.log(d.toString().trimEnd()));
    this.ready = new Promise((resolve, reject) => {
      let first = true;
      const lines = readline.createInterface({ input: proc.stdout! });
      lines.on("line", (line) => {
        let msg: any;
        try {
          msg = JSON.parse(line);
        } catch {
          this.log(`(not JSON) ${line}`);
          return;
        }
        if (first) {
          first = false;
          resolve(msg);
          return;
        }
        const p = this.pending.get(msg.id);
        if (!p) {
          return;
        }
        this.pending.delete(msg.id);
        if (msg.error) {
          if (msg.trace) {
            this.log(msg.trace);
          }
          p.reject(new Error(msg.error));
        } else {
          p.resolve(msg.result);
        }
      });
      proc.on("error", (e) => reject(e));
      proc.on("exit", (code) => {
        this.log(`checker exited (${code})`);
        const err = new Error(`the sverify checker exited (${code}); see the sverify output`);
        if (first) {
          reject(err);
        }
        for (const p of this.pending.values()) {
          p.reject(err);
        }
        this.pending.clear();
        this.proc = undefined;
        this.ready = undefined;
      });
    });
    return this.ready;
  }

  async check(file: string, counterexamples: number | null): Promise<CheckResult> {
    await this.start();
    const id = this.next++;
    return new Promise((resolve, reject) => {
      this.pending.set(id, { resolve, reject });
      this.proc!.stdin!.write(JSON.stringify({ id, method: "check", path: file, counterexamples }) + "\n");
    });
  }

  stop(): void {
    this.proc?.kill();
    this.proc = undefined;
    this.ready = undefined;
  }
}
