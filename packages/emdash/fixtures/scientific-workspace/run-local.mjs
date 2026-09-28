import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawn } from 'node:child_process';

const root = path.dirname(fileURLToPath(import.meta.url));
const manifest = JSON.parse(await fs.readFile(path.join(root, 'workspace.program.json'), 'utf8'));
if (process.version !== manifest.runtime.node) throw new Error(`This project pins Node ${manifest.runtime.node}; current Node is ${process.version}.`);
const task = process.argv[2] ?? 'compute';
if (!Object.hasOwn(manifest.tasks, task)) throw new Error('Choose a task declared in workspace.program.json.');
const output = path.resolve(process.argv[3] ?? path.join(root, 'results'));
await fs.mkdir(output, { recursive: true });
if ((await fs.readdir(output)).length) throw new Error('Choose an empty output directory to retain a distinct run.');
const parameters = process.argv[4] ?? '{}';
JSON.parse(parameters);
const child = spawn(process.execPath, ['--experimental-strip-types', '--no-warnings', manifest.tasks[task].entrypoint], {
  cwd: root, env: { ...process.env, WORKSPACE_EXECUTION_OUTPUT_DIR: output }, stdio: ['pipe', 'inherit', 'inherit'],
});
child.stdin.on('error', () => {}); child.stdin.end(parameters);
child.once('error', error => { console.error(error.message); process.exitCode = 1; });
child.once('close', code => { process.exitCode = code ?? 1; });
