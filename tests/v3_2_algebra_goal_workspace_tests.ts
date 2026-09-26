import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, symlinkSync, writeFileSync, existsSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { describe, it } from 'node:test';
import {
    ALGEBRA_GOAL_SOURCE_PROFILE, algebraGoalInput, checkAlgebraGoalRelation,
    computeAlgebraGoal, createAlgebraGoalExampleSource, createAlgebraGoalSource,
    normalizeAlgebraGoalSource, serializeAlgebraGoalSource
} from '../src/v3_2/algebra_goal_source';
import {
    ALGEBRA_GOAL_WORKSPACE_PROFILE, algebraGoalSha256, computeAlgebraGoalWorkspace,
    initializeAlgebraGoalWorkspace, inspectAlgebraGoalWorkspace, readAlgebraGoalWorkspace,
    renderAlgebraGoalWorkspace, updateAlgebraGoalWorkspace, withAlgebraGoalConstruction
} from '../src/v3_2/algebra_goal_workspace';
import { executeAlgebraGoalCommand } from '../src/v3_2/algebra_goal_commands';
import { readAlgebraGoalStdin } from '../src/v3_2/algebra_goal_cli';

const fixture = async (run: (root: string) => Promise<void>) => {
    const root = mkdtempSync(path.join(tmpdir(), 'emdash-goal-test-'));
    try { await run(root); } finally { rmSync(root, { recursive: true, force: true }); }
};
const changed = () => ({ ...createAlgebraGoalExampleSource(), title: 'Continue the same calculation with a revised goal' });

describe('algebra goal source and ordinary workspace', () => {
    it('preserves UTF-8 across input chunks and rejects malformed or oversized command bytes', async () => {
        const bytes = Buffer.from('A goal about α and β');
        async function* chunks() { for (const byte of bytes) yield Uint8Array.of(byte); }
        assert.equal(await readAlgebraGoalStdin(chunks()), bytes.toString());
        async function* invalid() { yield Uint8Array.of(0xc3); }
        await assert.rejects(readAlgebraGoalStdin(invalid()));
        async function* oversized() { yield Buffer.alloc(1024 * 1024 + 1); }
        await assert.rejects(readAlgebraGoalStdin(oversized()), /one MiB/u);
    });

    it('round-trips TypeScript-built inputs and retains an independently checked positive relation', () => {
        const original = createAlgebraGoalExampleSource();
        const source = createAlgebraGoalSource(algebraGoalInput(original), { title: original.title });
        assert.deepEqual(source, original);
        assert.deepEqual(normalizeAlgebraGoalSource(JSON.parse(serializeAlgebraGoalSource(source))), source);
        const computed = computeAlgebraGoal(source);
        assert.equal(computed.member, true);
        assert.equal(computed.engine, ALGEBRA_GOAL_SOURCE_PROFILE.engine);
        assert.equal(checkAlgebraGoalRelation(source, computed).authority, 'exact-polynomial-arithmetic');
        const altered = { ...computed, coefficients: computed.coefficients.map((coefficient, index) =>
            index === 0 ? [{ coefficient: '7', exponents: ['0', '0'] }] : coefficient) };
        assert.throws(() => checkAlgebraGoalRelation(source, altered));
    });

    it('reports nonmembership without inventing a usable relation', () => {
        const source = normalizeAlgebraGoalSource({ ...createAlgebraGoalExampleSource(),
            query: { name: 'g', terms: [{ coefficient: '1', exponents: ['0', '0'] }] } });
        const result = computeAlgebraGoal(source);
        assert.equal(result.member, false);
        assert.ok(result.remainder.length);
        assert.throws(() => checkAlgebraGoalRelation(source, result), /positive/u);
    });

    it('rejects malformed domains, dimensions, approximate numbers, unknown fields and input limits', () => {
        const source = createAlgebraGoalExampleSource();
        for (const bad of [
            { ...source, ring: { ...source.ring, field: 'R' } },
            { ...source, ring: { ...source.ring, variables: ['x', 'x'] } },
            { ...source, module: './execute-me.ts' },
            { ...source, query: { name: 'g', terms: [{ coefficient: 0.5, exponents: ['0', '0'] }] } },
            { ...source, query: { name: 'g', terms: [{ coefficient: '1/0', exponents: ['0', '0'] }] } },
            { ...source, query: { name: 'g', terms: [{ coefficient: '1', exponents: ['0'] }] } },
            { ...source, query: { name: 'g', terms: [{ coefficient: '1', exponents: ['4097', '0'] }] } },
            { ...source, generators: Array(9).fill(source.generators[0]) }
        ]) assert.throws(() => normalizeAlgebraGoalSource(bad));
    });

    it('rejects normalized source expansion before creating an unreadable workspace', async () => fixture(async root => {
        const source = { ...createAlgebraGoalExampleSource(), generators: Array.from({ length: 8 }, (_, i) => ({
            name: `f${i + 1}`, terms: Array.from({ length: 256 }, (_, degree) => ({
                coefficient: '1'.repeat(400), exponents: [String(degree), '0']
            }))
        })) };
        assert.ok(Buffer.byteLength(JSON.stringify(source)) < ALGEBRA_GOAL_WORKSPACE_PROFILE.maximumSourceBytes);
        assert.ok(Buffer.byteLength(serializeAlgebraGoalSource(source)) > ALGEBRA_GOAL_WORKSPACE_PROFILE.maximumSourceBytes);
        await assert.rejects(initializeAlgebraGoalWorkspace(root, source), { code: 'FILE_LIMIT' });
        assert.equal(existsSync(path.join(root, ALGEBRA_GOAL_WORKSPACE_PROFILE.sourceFile)), false);
    }));

    it('initializes without overwriting user files and resumes with source-bound results and views', async () => fixture(async root => {
        writeFileSync(path.join(root, 'notes.md'), 'User notes');
        const initialized = await initializeAlgebraGoalWorkspace(root);
        await assert.rejects(initializeAlgebraGoalWorkspace(root), { code: 'EEXIST' });
        const computed = await computeAlgebraGoalWorkspace(root);
        const rendered = await renderAlgebraGoalWorkspace(root);
        assert.equal(computed.sourceRevision, initialized.sourceRevision);
        assert.equal(rendered.sourceRevision, initialized.sourceRevision);
        assert.deepEqual(computed.coefficients.map(c => c.coefficient), ['-1*x', '1']);
        assert.match(readFileSync(rendered.svgPath, 'utf8'), /<svg/u);
        const resumed = inspectAlgebraGoalWorkspace(root);
        assert.equal(resumed.artifacts.computation.status, 'current');
        assert.equal(resumed.artifacts.view.status, 'current');
        assert.equal(readFileSync(path.join(root, 'notes.md'), 'utf8'), 'User notes');
    }));

    it('compares revisions, retains preceding source bytes, and marks derived artifacts stale', async () => fixture(async root => {
        const initial = await initializeAlgebraGoalWorkspace(root);
        await computeAlgebraGoalWorkspace(root);
        const previous = readAlgebraGoalWorkspace(root).sourceText;
        const updated = await updateAlgebraGoalWorkspace(root, initial.sourceRevision, changed());
        assert.notEqual(updated.sourceRevision, initial.sourceRevision);
        assert.equal(updated.artifacts.computation.status, 'stale');
        assert.equal(readFileSync(path.join(root, '.emdash/history', initial.sourceRevision.slice(7) + '.json'), 'utf8'), previous);
        await assert.rejects(updateAlgebraGoalWorkspace(root, initial.sourceRevision, initial.source), /changed/u);
        assert.equal(readAlgebraGoalWorkspace(root).source.title, changed().title);
    }));

    it('rejects symlinked source and generated paths without modifying the targets', async () => fixture(async base => {
        const root = path.join(base, 'workspace'), external = path.join(base, 'outside');
        mkdirSync(root); mkdirSync(external);
        const target = path.join(external, 'source.json');
        writeFileSync(target, serializeAlgebraGoalSource(createAlgebraGoalExampleSource()));
        symlinkSync(target, path.join(root, ALGEBRA_GOAL_WORKSPACE_PROFILE.sourceFile));
        assert.throws(() => readAlgebraGoalWorkspace(root), /ordinary file/u);
        rmSync(path.join(root, ALGEBRA_GOAL_WORKSPACE_PROFILE.sourceFile));
        writeFileSync(path.join(root, ALGEBRA_GOAL_WORKSPACE_PROFILE.sourceFile), readFileSync(target));
        symlinkSync(external, path.join(root, '.emdash'));
        await assert.rejects(computeAlgebraGoalWorkspace(root), /ordinary directory/u);
        assert.equal(existsSync(path.join(external, 'computation.json')), false);
        assert.equal(readFileSync(target, 'utf8'), serializeAlgebraGoalSource(createAlgebraGoalExampleSource()));
    }));

    it('honors an active mutation lock and recovers only an identified dead-process lock', async () => fixture(async root => {
        await initializeAlgebraGoalWorkspace(root);
        const lock = path.join(root, '.emdash/operation.lock');
        const active = JSON.stringify({ revision: ALGEBRA_GOAL_WORKSPACE_PROFILE.revision, pid: process.pid, nonce: 'other-operation' });
        writeFileSync(lock, active);
        await assert.rejects(computeAlgebraGoalWorkspace(root), /Another operation/u);
        assert.equal(readFileSync(lock, 'utf8'), active);
        writeFileSync(lock, JSON.stringify({ revision: ALGEBRA_GOAL_WORKSPACE_PROFILE.revision, pid: 2147483647, nonce: 'dead-operation' }));
        assert.equal((await computeAlgebraGoalWorkspace(root)).member, true);
        assert.equal(existsSync(lock), false);
    }));

    it('rejects a source edit during asynchronous construction and tracks computation dependencies', async () => fixture(async root => {
        await initializeAlgebraGoalWorkspace(root); await computeAlgebraGoalWorkspace(root);
        await assert.rejects(withAlgebraGoalConstruction(root, async () => {
            writeFileSync(path.join(root, ALGEBRA_GOAL_WORKSPACE_PROFILE.sourceFile), serializeAlgebraGoalSource(changed()));
            return { artifact: {}, summary: {} };
        }), /source changed/u);
        assert.equal(existsSync(path.join(root, '.emdash/construction.json')), false);
        await computeAlgebraGoalWorkspace(root);
        await withAlgebraGoalConstruction(root, async () => ({ artifact: { fixture: true }, summary: {} }));
        assert.equal(inspectAlgebraGoalWorkspace(root).artifacts.construction.status, 'current');
        const file = path.join(root, '.emdash/computation.json');
        writeFileSync(file, readFileSync(file, 'utf8') + '\n');
        assert.equal(inspectAlgebraGoalWorkspace(root).artifacts.construction.status, 'stale');
        rmSync(file);
        assert.equal(inspectAlgebraGoalWorkspace(root).artifacts.construction.status, 'stale');
    }));

    it('keeps exact computation available when numeric rendering fails and escapes view titles', async () => fixture(async root => {
        let source = createAlgebraGoalExampleSource();
        const huge = '1' + '0'.repeat(400);
        source = normalizeAlgebraGoalSource({ ...source, title: '<script>not code</script>',
            generators: [source.generators[0], { ...source.generators[1],
                terms: [{ coefficient: '1', exponents: ['1', '1'] }, { coefficient: '-' + huge, exponents: ['0', '0'] }] }],
            query: { ...source.query, terms: [{ coefficient: '1', exponents: ['3', '0'] }, { coefficient: '-' + huge, exponents: ['0', '0'] }] }
        });
        const initial = await initializeAlgebraGoalWorkspace(root, source);
        assert.equal((await computeAlgebraGoalWorkspace(root)).member, true);
        await assert.rejects(renderAlgebraGoalWorkspace(root), /numerical interpretation/u);
        assert.equal(inspectAlgebraGoalWorkspace(root).artifacts.computation.status, 'current');
        await updateAlgebraGoalWorkspace(root, initial.sourceRevision, { ...createAlgebraGoalExampleSource(), title: source.title });
        const view = await renderAlgebraGoalWorkspace(root);
        const html = readFileSync(view.htmlPath, 'utf8');
        assert.doesNotMatch(html, /<script>/u);
        assert.match(html, /&lt;script&gt;/u);
    }));

    it('returns shared structured diagnostics and never executes an adjacent source module', async () => fixture(async root => {
        const marker = path.join(root, 'unexpected');
        writeFileSync(path.join(root, 'unsafe.ts'), `require('node:fs').writeFileSync(${JSON.stringify(marker)}, 'bad')`);
        const response = await executeAlgebraGoalCommand({ command: 'init', root,
            source: { ...createAlgebraGoalExampleSource(), module: './unsafe.ts' } });
        assert.equal(response.ok, false);
        assert.equal(existsSync(marker), false);
        assert.equal((await executeAlgebraGoalCommand({ command: 'unknown', root })).ok, false);
        assert.equal((await executeAlgebraGoalCommand({ command: 'init', root })).ok, true);
        const current = readAlgebraGoalWorkspace(root);
        assert.equal(current.sourceRevision, algebraGoalSha256(current.sourceText));
        writeFileSync(path.join(root, ALGEBRA_GOAL_WORKSPACE_PROFILE.sourceFile), ' '.repeat(1024 * 1024 + 1));
        const oversized = await executeAlgebraGoalCommand({ command: 'inspect', root });
        assert.equal(oversized.ok, false);
        if (!oversized.ok) assert.equal(oversized.error.code, 'FILE_LIMIT');
    }));
});
