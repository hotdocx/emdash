import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import { existsSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { test } from 'node:test';

const reporter = fileURLToPath(new URL('./test-progress.mjs', import.meta.url));

async function fixture(t, body, observe = () => {}) {
  const directory = mkdtempSync(join(tmpdir(), 'emdash-progress-'));
  t.after(() => rmSync(directory, { recursive: true, force: true }));
  const file = join(directory, 'fixture.mjs');
  writeFileSync(file, `import { test } from 'node:test';\n${body(directory)}`);
  const env = { ...process.env, EMDASH_TEST_PROGRESS_INTERVAL_MS: '50' };
  // This is a new runner, not a recursively imported test worker.
  delete env.NODE_TEST_CONTEXT;
  const child = spawn(process.execPath, ['--test', '--test-reporter=spec',
    '--test-reporter-destination=stdout', `--test-reporter=${reporter}`,
    '--test-reporter-destination=stderr', file], {
    env,
  });
  const deadline = setTimeout(() => child.kill('SIGKILL'), 12_000);
  let stdout = '';
  let stderr = '';
  child.stdout.on('data', (chunk) => { stdout += chunk; });
  child.stderr.on('data', (chunk) => {
    stderr += chunk;
    observe(String(chunk), directory);
  });
  try {
    const result = await new Promise((resolve, reject) => {
      child.once('error', reject);
      child.once('close', (code, signal) => resolve({ code, signal }));
    });
    return { ...result, stdout, stderr };
  } finally {
    clearTimeout(deadline);
    if (child.exitCode === null && child.signalCode === null) child.kill('SIGKILL');
  }
}

test('progress preserves successful, skipped and todo results without logging every fast test', async (t) => {
  const result = await fixture(t, () => `
    test('fast pass', () => {});
    test('skip', { skip: true }, () => { throw Error('must not run'); });
    test('todo', { todo: true }, () => { throw Error('expected todo'); });
  `);
  assert.equal(result.code, 0, result.stdout + result.stderr);
  assert.equal(result.signal, null);
  assert.match(result.stdout, /fast pass/);
  assert.match(result.stdout, /skipped 1/);
  assert.match(result.stdout, /todo 1/);
  // Heartbeats may name the last fast event; only standalone completion lines
  // would violate the reporter's policy of omitting routine fast successes.
  assert.doesNotMatch(result.stderr, /^\[progress\] completed passed "fast pass"/m);
  assert.doesNotMatch(result.stderr, /^\[progress\] completed not-passed "todo"/m);
});

test('progress reports an early failure before its earlier-declared sibling finishes', async (t) => {
  let earlyFailure = false;
  const result = await fixture(t, (directory) => `
    import { writeFileSync } from 'node:fs';
    import { setTimeout } from 'node:timers/promises';
    test('parent', { concurrency: true }, async (t) => {
      await Promise.all([
        t.test('first declaration', async () => {
          await setTimeout(600);
          writeFileSync(${JSON.stringify(join(directory, 'first-done'))}, 'done');
        }),
        t.test('early failure', async () => {
          await setTimeout(40);
          throw Error('controlled failure');
        }),
      ]);
    });
  `, (chunk, directory) => {
    if (chunk.includes('completed not-passed "early failure"') &&
        !existsSync(join(directory, 'first-done'))) earlyFailure = true;
  });
  assert.equal(result.code, 1, result.stdout + result.stderr);
  assert.equal(earlyFailure, true, result.stderr);
  assert.match(result.stderr, /early failure.*duration=\d+\.\dms/);
  assert.match(result.stdout, /controlled failure/);
});

test('parent heartbeat stays responsive during synchronous worker computation and records slow duration', async (t) => {
  let liveDuringComputation = false;
  const result = await fixture(t, (directory) => `
    import { writeFileSync } from 'node:fs';
    test('cpu-bound fixture', () => {
      writeFileSync(${JSON.stringify(join(directory, 'started'))}, 'started');
      const end = performance.now() + 5_100;
      while (performance.now() < end) { /* controlled CPU-bound work */ }
      writeFileSync(${JSON.stringify(join(directory, 'done'))}, 'done');
    });
  `, (chunk, directory) => {
    if (chunk.includes('[progress] parent alive') &&
        existsSync(join(directory, 'started')) && !existsSync(join(directory, 'done'))) {
      liveDuringComputation = true;
    }
  });
  assert.equal(result.code, 0, result.stdout + result.stderr);
  assert.equal(liveDuringComputation, true, result.stderr);
  const duration = result.stderr.match(/completed passed "cpu-bound fixture".*duration=([\d.]+)ms/);
  assert.ok(duration && Number(duration[1]) >= 5_000, result.stderr);
});
