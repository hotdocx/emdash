import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { cp, mkdtemp, mkdir, readFile, rm } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { Client } from '@modelcontextprotocol/sdk/client/index.js';
import { StdioClientTransport } from '@modelcontextprotocol/sdk/client/stdio.js';

const repositoryRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../../..');
const args = process.argv.slice(2);
if (args.length && (args.length !== 2 || args[0] !== '--plugin')) throw new Error('Usage: verify-goal-mcp.mjs [--plugin DIRECTORY]');
const sourcePlugin = args.length ? path.resolve(args[1]) : path.join(repositoryRoot, 'plugins/emdash');
const root = await mkdtemp(path.join(os.tmpdir(), 'emdash-plugin-copy-'));
const plugin = path.join(root, 'plugin'), workspace = path.join(root, 'mathematics');
let client;
try {
  await cp(sourcePlugin, plugin, { recursive: true });
  await mkdir(workspace);
  const executable = path.join(plugin, 'dist/emdash-agent.cjs');
  const cli = (command, input) => JSON.parse(execFileSync(process.execPath, [executable, command,
    ...(command === 'request' ? [] : ['--root', workspace])], {
    cwd: root, encoding: 'utf8', timeout: 30_000, input,
  }));
  async function connect() {
    const next = new Client({ name: 'emdash-copied-plugin-acceptance', version: '1.0.0' });
    const transport = new StdioClientTransport({
      command: process.execPath, args: [path.join(plugin, 'scripts/start-mcp.mjs')],
      cwd: plugin, stderr: 'pipe',
    });
    transport.stderr?.on('data', () => undefined);
    await next.connect(transport);
    return next;
  }
  const call = async (name, arguments_) => {
    const response = await client.callTool({ name, arguments: { root: workspace, ...arguments_ } });
    assert.equal(response.isError, false, JSON.stringify(response));
    assert.equal(response.structuredContent.ok, true);
    assert.deepEqual(JSON.parse(response.content[0].text), response.structuredContent);
    return response.structuredContent.result;
  };
  client = await connect();
  const tools = await client.listTools();
  const capabilities = JSON.parse(execFileSync(process.execPath, [executable, 'capabilities'], { cwd: root, encoding: 'utf8' })).result;
  assert.deepEqual(tools.tools.map(t => t.name), capabilities.commands.map(c => c.tool));
  const initial = await call('emdash_initialize', {});
  const computed = await call('emdash_compute', {});
  assert.equal(computed.member, true);
  assert.deepEqual(computed, cli('compute').result);
  const view = await call('emdash_render', {});
  assert.match(await readFile(view.htmlPath, 'utf8'), /<svg/u);
  const snapshot = await call('emdash_inspect', {});
  assert.deepEqual(snapshot, cli('inspect').result);
  await client.close(); client = await connect();
  const resumed = await call('emdash_inspect', {});
  assert.equal(resumed.sourceRevision, initial.sourceRevision);
  assert.equal(resumed.artifacts.computation.status, 'current');
  const nextSource = { ...resumed.source, title: 'Continue after restarting the tool server' };
  const updated = await call('emdash_update', { expectedRevision: resumed.sourceRevision, source: nextSource });
  assert.equal(updated.artifacts.computation.status, 'stale');
  const stale = await client.callTool({ name: 'emdash_update', arguments: {
    root: workspace, expectedRevision: initial.sourceRevision, source: nextSource,
  } });
  assert.equal(stale.isError, true);
  assert.equal(stale.structuredContent.error.code, 'STALE_SOURCE');
  const wrong = await client.callTool({ name: 'emdash_initialize', arguments: { root: plugin } });
  assert.equal(wrong.isError, true);
  assert.equal(wrong.structuredContent.error.code, 'PLUGIN_DIRECTORY');
  console.log('Copied plugin STDIO: real SDK discovery/calls, CLI parity, compute/view, restart, update and stale/root controls passed.');
} finally {
  await client?.close();
  await rm(root, { recursive: true, force: true });
}
