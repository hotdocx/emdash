/** Focused AI-PROOF-2 tests for the Node-owned local command seam. */

import assert from 'node:assert';
import { describe, it } from 'node:test';
import {
    runCoreAiProofCli
} from '../src/v3_2/ai_proof_cli';

interface CliResult {
    readonly exitCode: number;
    readonly stdout: string;
    readonly stderr: string;
}

const run = (argv: readonly string[]): CliResult => {
    let stdout = '';
    let stderr = '';
    const exitCode = runCoreAiProofCli(argv, {
        readText: () => 'stable AI proof demo source\n',
        stdout: text => { stdout += text; },
        stderr: text => { stderr += text; }
    });
    return { exitCode, stdout, stderr };
};

describe('TypeScript v3.2 AI-PROOF-2 local CLI', () => {
    it('checks the complete declaration with one JSONL proof record', () => {
        const result = run(['check']);
        assert.equal(result.exitCode, 0);
        assert.equal(result.stderr, '');
        const lines = result.stdout.trimEnd().split('\n');
        assert.equal(lines.length, 1);
        const record = JSON.parse(lines[0]) as {
            kind: string;
            status: string;
            declarationId: string;
            checkedCore?: string;
        };
        assert.equal(record.kind, 'proof');
        assert.equal(record.status, 'complete');
        assert.equal(record.declarationId, 'complete_identity');
        assert.match(record.checkedCore ?? '', /^\(lambda/u);
    });

    it('reports the default incomplete declaration as proof plus goal', () => {
        const result = run(['goals']);
        assert.equal(result.exitCode, 0);
        assert.equal(result.stderr, '');
        const records = result.stdout.trimEnd().split('\n').map(
            line => JSON.parse(line) as {
                kind: string;
                status?: string;
                goal?: { id: string };
            }
        );
        assert.deepEqual(
            records.map(record => record.kind),
            ['proof', 'goal']
        );
        assert.equal(records[0].status, 'incomplete');
        assert.equal(records[1].goal?.id, 'body');
        assert.doesNotMatch(result.stdout, /\?m\d|session|Symbol/u);
    });

    it('makes incomplete check distinct from successful goal inspection', () => {
        const result = run(['check', 'open_identity']);
        assert.equal(result.exitCode, 1);
        assert.match(result.stdout, /"status":"incomplete"/u);
        assert.match(result.stderr, /proof is incomplete/u);
    });

    it('offers a compact human rendering of the same artifact', () => {
        const complete = run(['check', '--format', 'text']);
        assert.equal(complete.exitCode, 0);
        assert.match(complete.stdout, /complete_identity: complete/u);
        assert.match(complete.stdout, /checked Core/u);

        const open = run(['goals', '--format=text']);
        assert.equal(open.exitCode, 0);
        assert.match(open.stdout, /open_identity: incomplete/u);
        assert.match(open.stdout, /Goal body/u);
        assert.match(open.stdout, /\|- AIProofA/u);
    });

    it('fails closed on unknown commands, declarations, and formats', () => {
        for (const argv of [
            [] as string[],
            ['serve'],
            ['check', 'unknown'],
            ['goals', '--format', 'xml']
        ]) {
            const result = run(argv);
            assert.equal(result.exitCode, 2);
            assert.equal(result.stdout, '');
            assert.match(result.stderr, /^emdash:/u);
        }
    });
});
