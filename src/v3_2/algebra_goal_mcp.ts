/** STDIO projection of the shared goal commands; no second mathematical implementation. */
import { spawn } from 'node:child_process';
import { existsSync, realpathSync } from 'node:fs';
import path from 'node:path';
import { Server } from '@modelcontextprotocol/sdk/server/index.js';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import { CallToolRequestSchema, ListToolsRequestSchema, type Tool } from '@modelcontextprotocol/sdk/types.js';
import {
    ALGEBRA_GOAL_COMMANDS, algebraGoalFailure, type AlgebraGoalCommandResponse
} from './algebra_goal_commands';
import { AlgebraGoalError, algebraGoalRecord } from './algebra_goal_source';

export const ALGEBRA_GOAL_MCP_PROFILE = Object.freeze({
    revision: 'emdash-algebra-goal-mcp-v1', serverName: 'emdash-algebra', version: '0.1.0',
    transport: 'stdio', maximumRequestBytes: 1024 * 1024,
    maximumOutputBytes: 4 * 1024 * 1024, operationTimeoutMs: 30_000,
    workerHeapMiB: 512, maximumConcurrentOperations: 2,
    executesUserModules: false, invokesNetwork: false
} as const);

export function algebraGoalMcpTools(): Tool[] {
    return ALGEBRA_GOAL_COMMANDS.map(command => ({
        name: command.tool, description: command.description,
        inputSchema: {
            type: 'object', additionalProperties: false,
            properties: {
                root: { type: 'string', minLength: 1, maxLength: 4096,
                    description: 'Absolute directory of the user-selected mathematics workspace; never the installed plugin directory.' },
                ...command.properties
            },
            required: ['root', ...command.required]
        },
        outputSchema: { type: 'object', required: ['ok'], properties: {
            ok: { type: 'boolean' }, command: { type: 'string' },
            result: { type: 'object' }, error: { type: 'object' }
        }, additionalProperties: false },
        annotations: { readOnlyHint: !command.writes, destructiveHint: false,
            idempotentHint: !command.writes, openWorldHint: false }
    }));
}

/** A fixed bundled worker keeps CPU work cancellable without evaluating supplied code. */
export async function executeAlgebraGoalWorker(
    executable: string, request: unknown, signal?: AbortSignal,
    options: { timeoutMs?: number; maximumOutputBytes?: number } = {}
): Promise<AlgebraGoalCommandResponse> {
    const input = JSON.stringify(request);
    if (Buffer.byteLength(input) > ALGEBRA_GOAL_MCP_PROFILE.maximumRequestBytes) {
        return algebraGoalFailure(new AlgebraGoalError('INPUT_LIMIT', 'Tool input exceeds one MiB'));
    }
    if (signal?.aborted) return algebraGoalFailure(new AlgebraGoalError('CANCELLED', 'Operation cancelled before execution'));
    return new Promise(resolve => {
        const child = spawn(process.execPath,
            [`--max-old-space-size=${ALGEBRA_GOAL_MCP_PROFILE.workerHeapMiB}`, executable, 'request'],
            { stdio: ['pipe', 'pipe', 'pipe'], shell: false, windowsHide: true });
        const output: Buffer[] = [];
        let outputSize = 0;
        let stopped: AlgebraGoalError | undefined;
        let settled = false;
        const stop = (code: string, message: string) => {
            if (!stopped) stopped = new AlgebraGoalError(code, message);
            child.kill('SIGKILL');
        };
        const cancel = () => stop('CANCELLED', 'Operation cancelled; inspect the workspace before retrying a write');
        const timer = setTimeout(() => stop('TIMEOUT', 'Operation exceeded its deadline; inspect the workspace before retrying'),
            options.timeoutMs ?? ALGEBRA_GOAL_MCP_PROFILE.operationTimeoutMs);
        const finish = (response: AlgebraGoalCommandResponse) => {
            if (settled) return;
            settled = true; clearTimeout(timer); signal?.removeEventListener('abort', cancel); resolve(response);
        };
        signal?.addEventListener('abort', cancel, { once: true });
        if (signal?.aborted) cancel();
        child.stdout.on('data', (chunk: Buffer) => {
            outputSize += chunk.byteLength;
            if (outputSize > (options.maximumOutputBytes ?? ALGEBRA_GOAL_MCP_PROFILE.maximumOutputBytes)) {
                stop('OUTPUT_LIMIT', 'Operation output exceeded its byte limit');
            } else output.push(chunk);
        });
        // Drain diagnostics without returning environment/loader details as mathematical output.
        child.stderr.resume();
        child.stdin.on('error', () => undefined); // A cancelled or exited child may close stdin early.
        child.on('error', error => finish(algebraGoalFailure(error)));
        child.on('close', code => {
            if (stopped) { finish(algebraGoalFailure(stopped)); return; }
            try {
                const response = JSON.parse(new TextDecoder('utf-8', { fatal: true }).decode(Buffer.concat(output)));
                if (!response || typeof response !== 'object' || typeof response.ok !== 'boolean' ||
                    (response.ok ? code !== 0 || !response.result : code === 0 || !response.error)) {
                    throw new Error('Invalid command envelope');
                }
                finish(response as AlgebraGoalCommandResponse);
            } catch {
                finish(algebraGoalFailure(new AlgebraGoalError('WORKER_FAILED',
                    'The mathematical worker did not return a valid command result')));
            }
        });
        child.stdin.end(input);
    });
}

function canonicalProspectivePath(value: string): string {
    const missing: string[] = [];
    let existing = path.resolve(value);
    while (!existsSync(existing)) {
        const parent = path.dirname(existing);
        if (parent === existing) throw new AlgebraGoalError('INVALID_ROOT', 'The workspace has no accessible filesystem root');
        missing.unshift(path.basename(existing)); existing = parent;
    }
    return path.join(realpathSync(existing), ...missing);
}

export function createAlgebraGoalMcpServer(executableInput: string) {
    const executable = realpathSync(executableInput);
    const runtimeDirectory = path.dirname(executable);
    const candidatePluginRoot = path.dirname(runtimeDirectory);
    const protectedRoot = existsSync(path.join(candidatePluginRoot, '.codex-plugin/plugin.json'))
        ? candidatePluginRoot : runtimeDirectory;
    const running = new Set<AbortController>();
    // The lower-level SDK API projects our existing JSON schemas without a parallel Zod catalog.
    const server = new Server({ name: ALGEBRA_GOAL_MCP_PROFILE.serverName, version: ALGEBRA_GOAL_MCP_PROFILE.version }, {
        capabilities: { tools: {} },
        instructions: 'Emdash assists mathematical goals through ordinary workspace files. Use an explicit absolute root for the user-selected workspace, never the installed plugin directory. Inspect existing source before updates. Compute and render need no proof goal. Tools return structured results and retained artifacts. Do not treat exact arithmetic, approximations or computed-equation assumptions as checked proofs.'
    });
    server.setRequestHandler(ListToolsRequestSchema, async () => ({ tools: algebraGoalMcpTools() }));
    server.setRequestHandler(CallToolRequestSchema, async (request, extra) => {
        let response: AlgebraGoalCommandResponse;
        let cancellation: AbortController | undefined;
        const cancel = () => cancellation?.abort();
        try {
            const command = ALGEBRA_GOAL_COMMANDS.find(c => c.tool === request.params.name);
            if (!command) throw new AlgebraGoalError('UNKNOWN_TOOL', 'Unknown Emdash tool');
            const args = algebraGoalRecord(request.params.arguments ?? {}, ['root', ...Object.keys(command.properties)], 'arguments');
            if (typeof args.root !== 'string' || args.root.length > 4096 || !path.isAbsolute(args.root)) {
                throw new AlgebraGoalError('INVALID_ROOT', 'Choose an absolute mathematics workspace directory');
            }
            const relative = path.relative(protectedRoot, canonicalProspectivePath(args.root));
            if (relative === '' || (!relative.startsWith(`..${path.sep}`) && relative !== '..' && !path.isAbsolute(relative))) {
                throw new AlgebraGoalError('PLUGIN_DIRECTORY', 'Choose a workspace outside the installed plugin runtime');
            }
            if (running.size >= ALGEBRA_GOAL_MCP_PROFILE.maximumConcurrentOperations) {
                throw new AlgebraGoalError('RUNTIME_BUSY', 'Two operations are already running; wait for one to finish');
            }
            cancellation = new AbortController(); running.add(cancellation);
            extra.signal.addEventListener('abort', cancel, { once: true });
            if (extra.signal.aborted) cancellation.abort();
            response = await executeAlgebraGoalWorker(executable, { command: command.command, ...args }, cancellation.signal);
        } catch (error) { response = algebraGoalFailure(error); }
        finally {
            extra.signal.removeEventListener('abort', cancel);
            if (cancellation) running.delete(cancellation);
        }
        return { isError: !response.ok, structuredContent: response,
            content: [{ type: 'text' as const, text: JSON.stringify(response) }] };
    });
    server.onclose = () => { for (const request of running) request.abort(); };
    return server;
}

export async function startAlgebraGoalMcp(executable: string): Promise<void> {
    const server = createAlgebraGoalMcpServer(executable);
    await server.connect(new StdioServerTransport());
    const close = () => { void server.close(); };
    process.once('SIGTERM', close); process.once('SIGINT', close);
}
