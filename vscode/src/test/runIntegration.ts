// Runs `integration/index.ts` in a VS Code extension host on the demo
// workspace: `npm run test:vscode` (VSCODE_PATH picks the VS Code binary;
// by default the installed one on macOS, else a download).

import * as fs from "fs";
import * as path from "path";
import { runTests } from "@vscode/test-electron";

async function main(): Promise<void> {
  const root = path.resolve(__dirname, "../..");
  const mac = "/Applications/Visual Studio Code.app/Contents/MacOS/Code";
  const vscodeExecutablePath = process.env.VSCODE_PATH ?? (fs.existsSync(mac) ? mac : undefined);
  await runTests({
    vscodeExecutablePath,
    extensionDevelopmentPath: root,
    extensionTestsPath: path.join(__dirname, "integration/index"),
    launchArgs: [path.join(root, "demo"), "--disable-extensions", "--skip-welcome", "--skip-release-notes"],
  });
}

main().catch((e) => {
  console.error(e);
  process.exit(1);
});
