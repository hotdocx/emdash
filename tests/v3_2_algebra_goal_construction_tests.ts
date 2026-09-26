import assert from 'node:assert/strict';
import { existsSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { describe, it } from 'node:test';
import {
    algebraGoalInput, algebraGoalPolynomialTerms, checkAlgebraGoalRelation,
    createAlgebraGoalExampleSource, normalizeAlgebraGoalSource, serializeAlgebraGoalSource
} from '../src/v3_2/algebra_goal_source';
import {
    algebraGoalSha256, computeAlgebraGoalWorkspace, initializeAlgebraGoalWorkspace,
    inspectAlgebraGoalWorkspace, readAlgebraGoalWorkspace
} from '../src/v3_2/algebra_goal_workspace';
import { constructAlgebraGoalWorkspace } from '../src/v3_2/algebra_goal_construction';
import { algebraPolynomialAdd, algebraPolynomialSubtract, algebraPolynomialText } from '../src/v3_2/algebra_polynomial';

const fixture = async (run: (root: string) => Promise<void>, source = createAlgebraGoalExampleSource()) => {
    const root = mkdtempSync(path.join(tmpdir(), 'emdash-goal-construction-'));
    try {
        await initializeAlgebraGoalWorkspace(root, source);
        await computeAlgebraGoalWorkspace(root);
        await run(root);
    } finally { rmSync(root, { recursive: true, force: true }); }
};
const artifact = (root: string) => JSON.parse(readFileSync(path.join(root, '.emdash/construction.json'), 'utf8'));
const adoption = { mode: 'internal', adoptionReason: 'Explicit test use of the exact computed zero-composition equation' };

describe('goal workspace native and internal constructions', () => {
    it('builds a native whole complex and applies its upper map without adopting a law', async () => fixture(async root => {
        const result = await constructAlgebraGoalWorkspace(root, {});
        assert.deepEqual(result.ranks, [1, 3, 1]);
        assert.deepEqual(result.nativeUpperColumn, ['-1*x', '1', '-1']);
        assert.deepEqual(result.nativeImageOfOne, result.nativeUpperColumn);
        assert.equal(result.compositeIsZero, true);
        assert.equal(result.adoptedEquationCount, 0);
        assert.equal(artifact(root).result.internal, undefined);
        assert.equal(artifact(root).result.native.differentials.length, 2);
        assert.equal(inspectAlgebraGoalWorkspace(root).artifacts.construction.status, 'current');
    }));

    it('constructs and uses a transparent Core complex with exactly one explicit computed equation', async () => fixture(async root => {
        await assert.rejects(constructAlgebraGoalWorkspace(root, { mode: 'internal' }), /explicit reason/u);
        assert.equal(existsSync(path.join(root, '.emdash/construction.json')), false);
        const result = await constructAlgebraGoalWorkspace(root, adoption);
        assert.equal(result.resultStatus, 'typed-internal-reuse-with-explicit-computed-equation');
        assert.equal(result.adoptedEquationCount, 1);
        const internal = artifact(root).result.internal;
        assert.equal(internal.assumptions.length, 1);
        assert.equal(internal.assumptions[0].classification, 'computed-equation');
        assert.equal(internal.assumptions[0].hasProofBody, false);
        assert.equal(internal.assumptions[0].authority, 'checked-relative-to-explicit-assumption');
        assert.ok(internal.definitions.every((d: { transparency: string; body: string }) => d.transparency === 'transparent' && d.body));
        assert.match(internal.upperDifferential, /goal_reuse_complex/u);
        assert.match(internal.image, /goal_reuse_complex/u);
        assert.match(internal.image, /bridge_comm_ring_matrix_apply/u);
        for (const material of internal.fingerprintMaterials) {
            assert.equal(algebraGoalSha256(material.source), material.sourceSha256);
            assert.equal(algebraGoalSha256(material.profile), material.profileSha256);
        }
        assert.match(artifact(root).result.sourceData, /retained-native-computation/u);
        assert.doesNotMatch(artifact(root).result.sourceData, /singular-lift/u);
    }));

    it('retains a different valid coefficient vector instead of recomputing the native answer', async () => fixture(async root => {
        await constructAlgebraGoalWorkspace(root, adoption);
        const first = artifact(root);
        const source = readAlgebraGoalWorkspace(root).source;
        const input = algebraGoalInput(source);
        const filename = path.join(root, '.emdash/computation.json');
        const retained = JSON.parse(readFileSync(filename, 'utf8'));
        const checked = checkAlgebraGoalRelation(source, retained.computation);
        const alternative = [
            algebraPolynomialAdd(checked.coefficients[0], input.ideal.generators[1]),
            algebraPolynomialSubtract(checked.coefficients[1], input.ideal.generators[0])
        ];
        retained.computation.coefficients = alternative.map(algebraGoalPolynomialTerms);
        writeFileSync(filename, JSON.stringify(retained));
        assert.equal(inspectAlgebraGoalWorkspace(root).artifacts.construction.status, 'stale');
        const result = await constructAlgebraGoalWorkspace(root, adoption);
        assert.deepEqual(result.nativeUpperColumn.slice(0, 2), alternative.map(algebraPolynomialText));
        const next = artifact(root);
        assert.notEqual(next.computationRevision, first.computationRevision);
        assert.notEqual(next.result.internal.definitions[0].body, first.result.internal.definitions[0].body);
    }));

    it('keeps rational native construction useful when the formal interpretation is unsupported', async () => {
        const initial = createAlgebraGoalExampleSource();
        const source = normalizeAlgebraGoalSource({ ...initial,
            generators: [initial.generators[0], { ...initial.generators[1], terms: [
                { coefficient: '1', exponents: ['1', '1'] }, { coefficient: '-1/2', exponents: ['0', '0'] }
            ] }], query: { name: 'g', terms: [
                { coefficient: '1', exponents: ['3', '0'] }, { coefficient: '-1/2', exponents: ['0', '0'] }
            ] }
        });
        await fixture(async root => {
            assert.equal((await constructAlgebraGoalWorkspace(root, {})).compositeIsZero, true);
            const nativeBytes = readFileSync(path.join(root, '.emdash/construction.json'), 'utf8');
            await assert.rejects(constructAlgebraGoalWorkspace(root, adoption));
            assert.equal(readFileSync(path.join(root, '.emdash/construction.json'), 'utf8'), nativeBytes);
            assert.deepEqual(readAlgebraGoalWorkspace(root).source, source);
        }, source);
    });

    it('rejects stale, altered or nonpositive retained results without a construction artifact', async () => fixture(async root => {
        const filename = path.join(root, '.emdash/computation.json');
        const original = readFileSync(filename, 'utf8');
        const edited = JSON.parse(original);
        edited.computation.coefficients[0] = [{ coefficient: '7', exponents: ['0', '0'] }];
        writeFileSync(filename, JSON.stringify(edited));
        await assert.rejects(constructAlgebraGoalWorkspace(root, {}), /does not equal/u);
        edited.computation.member = false;
        writeFileSync(filename, JSON.stringify(edited));
        await assert.rejects(constructAlgebraGoalWorkspace(root, {}), /positive native relation/u);
        writeFileSync(filename, original);
        writeFileSync(path.join(root, 'emdash.goal.json'), serializeAlgebraGoalSource({ ...createAlgebraGoalExampleSource(), title: 'Changed source' }));
        await assert.rejects(constructAlgebraGoalWorkspace(root, {}), /current relation/u);
        assert.equal(existsSync(path.join(root, '.emdash/construction.json')), false);
    }));
});
