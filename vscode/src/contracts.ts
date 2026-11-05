// Contract authoring without the checker: the helpers `requires` and
// `ensures` take, and the columns a contract names, checked as it is typed
// against the schemas of the last check. No vscode import, so the smoke
// test runs it under plain Node.

import type { Range, Site } from "./checker";

export interface Helper {
  name: string;
  snippet: string;
  detail: string;
  doc: string;
  roles: ("requires" | "ensures")[];
}

export const HELPERS: Helper[] = [
  {
    name: "unique",
    snippet: 'unique("${1:column}")',
    detail: "sv.unique(*cols): a key",
    doc: "The columns identify a row. In `requires`, checked on the data (or proved from table metadata); in `ensures`, proved.",
    roles: ["requires", "ensures"],
  },
  {
    name: "max_rows",
    snippet: "max_rows(${1:1_000_000})",
    detail: "sv.max_rows(n): a row cap",
    doc: "At most `n` rows. Lean carries the cap through the plan, which proves that a `SUM` fits its type and bounds the `ε` of a double aggregate.",
    roles: ["requires", "ensures"],
  },
  {
    name: "rows_per",
    snippet: 'rows_per(["${1:column}"], at_most=${2:1})',
    detail: "sv.rows_per(cols, at_most): rows per key",
    doc: "At most `at_most` rows agree on `cols`. A group of an aggregate by `cols` then has at most that many rows. `unique(*cols)` is `rows_per(cols, at_most=1)`.",
    roles: ["requires", "ensures"],
  },
  {
    name: "references",
    snippet: 'references("${1:column}", to=("${2:table}", "${3:column}"))',
    detail: "sv.references(col, to=(table, col)): a foreign key",
    doc: "Every non-NULL value of `col` occurs in the referenced column. Only in `requires`.",
    roles: ["requires"],
  },
  {
    name: "arrives_within",
    snippet: 'arrives_within("${1:ts}", hours=${2:1})',
    detail: "sv.arrives_within(col, days=, hours=, …): lateness",
    doc: "Every row a batch inserts or deletes has `col` at most this far behind the watermark. Only in `requires` on a source.",
    roles: ["requires"],
  },
  {
    name: "approx",
    snippet: "approx(${1:_.column <= 100})",
    detail: "sv.approx(cond, rel=1e-6): allow for rounding",
    doc: "Relaxes each comparison with a number by `rel · max(1, |k|)`, for a condition on a double that rounding may break by the last bits.",
    roles: ["ensures"],
  },
  {
    name: "equivalent",
    snippet: 'equivalent(rows="${1|multiset,sequence|}", floats=${2|"exact","plan",sv.within(rel=1e-9)|})',
    detail: "sv.equivalent(rows=, floats=, …): what the consumer observes",
    doc: 'Names what the result\'s consumer observes. An engine\'s result is correct when it equals, up to this, a result the reference allows. Without it, rows are a multiset and every value is exact. `floats="plan"` accepts the checker\'s ε per double column.',
    roles: ["ensures"],
  },
  {
    name: "within",
    snippet: "within(${1|abs,rel,ulps|}=${2:1e-9})",
    detail: "sv.within(abs=, rel=, ulps=): a tolerance on doubles",
    doc: "A tolerance for `sv.equivalent(floats=...)`: two doubles are equal when they are within any one of the bounds.",
    roles: ["ensures"],
  },
];

/** The helpers that belong in a contract of `role` (all outside a contract). */
export function helpersFor(role: "requires" | "ensures" | undefined): Helper[] {
  return role ? HELPERS.filter((h) => h.roles.includes(role)) : HELPERS;
}

/** Move a range for an edit of lines `at` that adds `delta` lines. */
export function shiftRange(r: Range, at: readonly [number, number], delta: number): Range {
  if (delta === 0) {
    return r;
  }
  if (at[1] < r[0]) {
    return [r[0] + delta, r[1], r[2] + delta, r[3]];
  }
  if (at[0] <= r[2]) {
    return [r[0], r[1], Math.max(r[0], r[2] + delta), r[3]];
  }
  return r;
}

export interface Problem {
  range: Range;
  message: string;
  replacement?: string;
}

/** The end of the bracketed list or dict that opens at `start`. */
function closing(text: string, start: number): number {
  let depth = 0;
  let quote: string | null = null;
  for (let i = start; i < text.length; i++) {
    const ch = text[i];
    if (quote) {
      if (ch === "\\") {
        i++;
      } else if (ch === quote) {
        quote = null;
      }
      continue;
    }
    if (ch === '"' || ch === "'") {
      quote = ch;
    } else if ("([{".includes(ch)) {
      depth++;
    } else if (")]}".includes(ch)) {
      depth--;
      if (depth === 0) {
        return i + 1;
      }
    }
  }
  return text.length;
}

function offsetAt(lines: string[], line: number, ch: number): number {
  let o = 0;
  for (let i = 0; i < line && i < lines.length; i++) {
    o += lines[i].length + 1;
  }
  return o + ch;
}

function positionAt(text: string, offset: number): [number, number] {
  const before = text.slice(0, offset);
  const line = before.split("\n").length - 1;
  return [line, offset - (before.lastIndexOf("\n") + 1)];
}

/** Edit distance, for "did you mean". */
function distance(a: string, b: string): number {
  const d = Array.from({ length: a.length + 1 }, (_, i) => [i, ...Array(b.length).fill(0)]);
  for (let j = 1; j <= b.length; j++) {
    d[0][j] = j;
  }
  for (let i = 1; i <= a.length; i++) {
    for (let j = 1; j <= b.length; j++) {
      d[i][j] = Math.min(d[i - 1][j] + 1, d[i][j - 1] + 1, d[i - 1][j - 1] + (a[i - 1] === b[j - 1] ? 0 : 1));
    }
  }
  return d[a.length][b.length];
}

/** Columns that `_.x`, `_["x"]` and `sv.unique("x")` name in each contract
 * site, and that its table does not have. */
export function liveColumnProblems(text: string, sites: Site[]): Problem[] {
  const lines = text.split("\n");
  const out: Problem[] = [];
  for (const site of sites) {
    const names = Object.keys(site.columns);
    if (names.length === 0) {
      continue;
    }
    const start = offsetAt(lines, site.range[0], site.range[1]);
    const opener = text.slice(start).search(/[[{(]/);
    if (opener < 0) {
      continue;
    }
    const end = closing(text, start + opener);
    const body = text.slice(start, end);
    const rx = /(?<![\w.])_\.([A-Za-z_]\w*)|(?<![\w.])_\[["'](\w+)["']\]|\b(?:unique|rows_per)\(\[?((?:\s*["']\w+["']\s*,?)+)/g;
    for (let m = rx.exec(body); m; m = rx.exec(body)) {
      const found: [string, number][] = [];
      if (m[1]) {
        found.push([m[1], m.index + 2]);
      } else if (m[2]) {
        found.push([m[2], m.index + 3]);
      } else if (m[3]) {
        const base = m.index + m[0].length - m[3].length;
        for (const c of m[3].matchAll(/["'](\w+)["']/g)) {
          found.push([c[1], base + (c.index ?? 0) + 1]);
        }
      }
      for (const [name, at] of found) {
        if (names.includes(name) || isMethod(name)) {
          continue;
        }
        const [l0, c0] = positionAt(text, start + at);
        const near = names.map((n) => [n, distance(n, name)] as const).sort((a, b) => a[1] - b[1])[0];
        const where = site.role === "ensures" ? "the output" : site.table ?? "the input";
        const replacement = near && near[1] <= Math.max(2, name.length / 3) ? near[0] : undefined;
        out.push({
          range: [l0, c0, l0, c0 + name.length],
          message:
            `${where} has no column \`${name}\`` +
            (replacement ? `; did you mean \`${replacement}\`?` : "") +
            ` (columns: ${names.join(", ")})`,
          replacement,
        });
      }
    }
  }
  return out;
}

/** Attributes of Ibis's deferred `_` that are no column. */
function isMethod(name: string): boolean {
  return ["pipe", "op", "schema", "columns"].includes(name);
}
