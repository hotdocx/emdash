import assert from 'node:assert/strict';
import { existsSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { describe, it } from 'node:test';
import { Client } from '@modelcontextprotocol/sdk/client/index.js';
import { InMemoryTransport } from '@modelcontextprotocol/sdk/inMemory.js';
import { ALGEBRA_GOAL_COMMANDS } from '../src/v3_2/algebra_goal_commands';
import {
    ALGEBRA_GOAL_MCP_PROFILE, algebraGoalMcpTools, createAlgebraGoalMcpServer,
    executeAlgebraGoalWorker
} from '../src/v3_2/algebra_goal_mcp';

const temporary = async (run: (root: string) => Promise<void>) => {
    const root = mkdtempSync(path.join(tmpdir(), 'emdash-mcp-test-'));
    try { await run(root); } finally { rmSync(root, { recursive: true, force: true }); }
};

describe('algebra goal MCP projection and worker bounds', () => {
    it('derives names, schemas and write annotations from the same command catalog', () => {
        const tools = algebraGoalMcpTools();
        assert.deepEqual(tools.map(t => t.name), ALGEBRA_GOAL_COMMANDS.map(c => c.tool));
        tools.forEach((tool, index) => {
            const command = ALGEBRA_GOAL_COMMANDS[index];
            assert.equal(tool.annotations?.readOnlyHint, !command.writes);
            assert.deepEqual(tool.inputSchema.required, ['root', ...command.required]);
            for (const name of Object.keys(command.properties)) {
                assert.deepEqual(tool.inputSchema.properties?.[name], command.properties[name]);
            }
        });
    });

    it('negotiates real SDK discovery and rejects unknown, relative and runtime-directory requests', async () => temporary(async root => {
        const executable = path.join(root, 'worker.cjs');
        writeFileSync(executable, 'throw new Error("This worker must not execute");');
        const server = createAlgebraGoalMcpServer(executable);
        const client = new Client({ name: 'emdash-test', version: '1.0.0' });
        const [clientTransport, serverTransport] = InMemoryTransport.createLinkedPair();
        await server.connect(serverTransport); await client.connect(clientTransport);
        try {
            const listed = await client.listTools();
            assert.deepEqual(listed.tools, algebraGoalMcpTools());
            for (const request of [
                { name: 'not_an_emdash_tool', arguments: { root } },
                { name: 'emdash_inspect', arguments: { root: 'relative' } },
                { name: 'emdash_initialize', arguments: { root } },
                { name: 'emdash_compute', arguments: { root, module: './unknown.js' } }
            ]) {
                const result = await client.callTool(request);
                assert.equal(result.isError, true);
                assert.equal((result.structuredContent as { ok?: boolean } | undefined)?.ok, false);
            }
        } finally { await client.close(); await server.close(); }
    }));

    it('honors pre-execution cancellation and bounded input without spawning a worker', async () => {
        const controller = new AbortController(); controller.abort();
        const cancelled = await executeAlgebraGoalWorker('/missing/worker.cjs', {}, controller.signal);
        assert.equal(cancelled.ok, false);
        if (!cancelled.ok) assert.equal(cancelled.error.code, 'CANCELLED');
        const oversized = await executeAlgebraGoalWorker('/missing/worker.cjs',
            { source: 'x'.repeat(ALGEBRA_GOAL_MCP_PROFILE.maximumRequestBytes + 1) });
        assert.equal(oversized.ok, false);
        if (!oversized.ok) assert.equal(oversized.error.code, 'INPUT_LIMIT');
    });

    it('bounds worker time and output and rejects non-protocol results', async () => temporary(async root => {
        const executable = path.join(root, 'worker.cjs');
        writeFileSync(executable, 'process.stdin.resume(); setInterval(() => {}, 1000);');
        const timeout = await executeAlgebraGoalWorker(executable, {}, undefined, { timeoutMs: 50 });
        assert.equal(timeout.ok, false);
        if (!timeout.ok) assert.equal(timeout.error.code, 'TIMEOUT');
        writeFileSync(executable, 'process.stdout.write("x".repeat(100000)); setInterval(() => {}, 1000);');
        const output = await executeAlgebraGoalWorker(executable, {}, undefined, { maximumOutputBytes: 1024 });
        assert.equal(output.ok, false);
        if (!output.ok) assert.equal(output.error.code, 'OUTPUT_LIMIT');
        writeFileSync(executable, 'console.log("{}");');
        const invalid = await executeAlgebraGoalWorker(executable, {});
        assert.equal(invalid.ok, false);
        if (!invalid.ok) assert.equal(invalid.error.code, 'WORKER_FAILED');
    }));

    it('cancels and reaps a running worker', async () => temporary(async root => {
        const executable = path.join(root, 'worker.cjs'), pidPath = path.join(root, 'pid');
        writeFileSync(executable, `require('node:fs').writeFileSync(${JSON.stringify(pidPath)}, String(process.pid)); process.stdin.resume(); setInterval(() => {}, 1000);`);
        const controller = new AbortController();
        const pending = executeAlgebraGoalWorker(executable, {}, controller.signal);
        try {
            const deadline = Date.now() + 5000;
            while (!existsSync(pidPath) && Date.now() < deadline) await new Promise(resolve => setTimeout(resolve, 10));
            assert.ok(existsSync(pidPath));
            const pid = Number(readFileSync(pidPath, 'utf8'));
            controller.abort();
            const response = await pending;
            assert.equal(response.ok, false);
            if (!response.ok) assert.equal(response.error.code, 'CANCELLED');
            assert.throws(() => process.kill(pid, 0), { code: 'ESRCH' });
        } finally { controller.abort(); await pending; }
    }));
});
