import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { createHash } from 'node:crypto';
import { spawn } from 'node:child_process';
const root = path.dirname(fileURLToPath(import.meta.url));
const request = JSON.parse(await fs.readFile(path.join(root, 'request.json'), 'utf8'));
if (request.nodeVersion !== process.version) throw new Error(`Use the captured Node runtime ${request.nodeVersion}.`);
const source = path.join(root, 'source');
for (const file of request.files) {
  if (!file.path.split('/').every(part => /^[A-Za-z0-9_][A-Za-z0-9_.-]*$/.test(part))) throw new Error('Invalid captured path.');
  const bytes = await fs.readFile(path.join(source, file.path));
  if (createHash('sha256').update(bytes).digest('hex') !== file.sha256) throw new Error('Captured source changed: ' + file.path);
}
const manifest = JSON.parse(await fs.readFile(path.join(source, request.input.manifestPath), 'utf8'));
const task = manifest.tasks[request.input.task]; if (!task) throw new Error('Captured task is missing.');
const output = path.join(root, 'replayed-artifacts'); await fs.mkdir(output, { recursive: false });
const child = spawn(process.execPath, ['--experimental-strip-types', '--no-warnings', '--max-old-space-size=256', task.entrypoint], {
  cwd: source, env: { ...process.env, WORKSPACE_EXECUTION_OUTPUT_DIR: output }, stdio: ['pipe', 'inherit', 'inherit'],
});
const timeout = setTimeout(() => child.kill('SIGKILL'), 30_000);
child.stdin.on('error', () => {}); child.stdin.end(JSON.stringify(request.input.parameters));
child.once('error', error => { clearTimeout(timeout); console.error(error.message); process.exitCode = 1; });
child.once('close', code => { clearTimeout(timeout); process.exitCode = code ?? 1; });
