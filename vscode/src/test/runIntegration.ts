// Runs `integration/index.ts` in a VS Code extension host on the demo
// workspace: `npm run test:vscode` (VSCODE_PATH picks the VS Code binary;
// by default the installed one on macOS, else a download).

import * as fs from "fs";
import * as os from "os";
import * as path from "path";
import { runTests } from "@vscode/test-electron";

async function main(): Promise<void> {
  const root = path.resolve(__dirname, "../..");
  const mac = "/Applications/Visual Studio Code.app/Contents/MacOS/Code";
  const vscodeExecutablePath = process.env.VSCODE_PATH ?? (fs.existsSync(mac) ? mac : undefined);
  // The test types into the files and saves them: it works on a copy.
  const demo = fs.mkdtempSync(path.join(os.tmpdir(), "sverify-demo-"));
  fs.cpSync(path.join(root, "demo"), demo, { recursive: true });
  const settings = path.join(demo, ".vscode", "settings.json");
  const python = process.env.SVERIFY_PYTHON ?? path.resolve(root, "../python/.venv/bin/python");
  fs.writeFileSync(settings, JSON.stringify({ "sverify.pythonPath": python, "sverify.counterexamples": 0 }, null, 2));
  await runTests({
    vscodeExecutablePath,
    extensionDevelopmentPath: root,
    extensionTestsPath: path.join(__dirname, "integration/index"),
    launchArgs: [demo, "--disable-extensions", "--skip-welcome", "--skip-release-notes"],
  }).finally(() => fs.rmSync(demo, { recursive: true, force: true }));
}

main().catch((e) => {
  console.error(e);
  process.exit(1);
});
