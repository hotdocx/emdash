import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    adoptAlgebraExternalModuleComplex, assertAlgebraExternalModuleReuseCurrent,
    prepareAlgebraExternalModuleData
} from '../src/v3_2/algebra_external_module_reuse';
import {
    algebraPolynomialWorkspaceInput, createAlgebraPolynomialWorkbenchExample
} from '../src/v3_2/algebra_polynomial_workbench';
import { computeSingularIdealWitness } from '../src/v3_2/algebra_ideal_singular';
import { createAlgebraOracleNodeTransport } from '../src/v3_2/algebra_oracle_node';
import { algebraPolynomialOne, algebraPolynomialRing, serializeAlgebraPolynomial } from '../src/v3_2/algebra_polynomial';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import { createCoreProofArtifactFingerprint } from '../src/v3_2/proof_document';
import { serializeCoreExpression } from '../src/v3_2/core_serialization';
import { createCoreProofChecker } from '../src/v3_2/proof_checker';
import {
    FORMAL_BOUNDED_COMPLEX_ASSEMBLY_BINDINGS, FORMAL_BOUNDED_COMPLEX_ASSEMBLY_PROFILE,
    assembleFormalTwoStepComplex, formalComplexCall, formalComplexNat
} from '../src/v3_2/algebra_formal_bounded_complex_assembly';
import { AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_zariski_signatures';
import { AFFINE_FORMAL_FINITE_MODULE_BINDINGS } from '../src/v3_2/algebra_formal_finite_module';
import { AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS } from '../src/v3_2/algebra_formal_presentation_morphism';
import { serializeKernelExpression } from '../src/v3_2/lambdapi';
import { checkLambdapiProbe } from '../src/v3_2/probe';

const fingerprint = (source: string, profile: string) => {
    const sha = (text: string) => 'sha256:' + createHash('sha256').update(text).digest('hex');
    return createCoreProofArtifactFingerprint({
        source: { id: 'tests/external-module-source.json', sha256: sha(source) }, profileSha256: sha(profile)
    });
};
const decision = Object.freeze({ kind: 'trust-exact-algebra-computation' as const,
    evidence: 'Explicit test adoption of the computed composite of external-derived matrices' });
const workspace = () => createAlgebraPolynomialWorkbenchExample();
const external = async (variant: boolean | 'rational' = false) => computeSingularIdealWitness(
    algebraPolynomialWorkspaceInput(workspace()), {
        async execute() {
            const coefficients = variant === 'rational'
                ? [['TERM:1/2:1,1', 'TERM:-1:1,0', 'TERM:-1/2:0,0'],
                    ['TERM:1/2:2,0', 'TERM:-1/2:0,1', 'TERM:1:0,0']]
                : variant
                ? [['TERM:1:1,1', 'TERM:-1:1,0', 'TERM:-1:0,0'],
                    ['TERM:1:2,0', 'TERM:-1:0,1', 'TERM:1:0,0']]
                : [['TERM:-1:1,0'], ['TERM:1:0,0']];
            return { exitCode: 0, stderr: '', stdout: [
                'EMDASH_WITNESS_V1', 'VERSION:4330', 'MEMBER:1',
                ...coefficients.flatMap((terms, index) =>
                    [`COEFFICIENT:${index}`, ...terms, 'END_COEFFICIENT']), 'END_WITNESS'
            ].join('\n') };
        }
    });

describe('external coefficients in whole internal module constructions', () => {
    it('retains the actual external coefficient choice in typed module data', async () => {
        const a = await external(), b = await external(true);
        const first = prepareAlgebraExternalModuleData(workspace(), a);
        const second = prepareAlgebraExternalModuleData(workspace(), b);
        assert.ok(first.complex.isComplex && second.complex.isComplex);
        assert.equal(second.column.components.length, 3);
        if (b.kind !== 'witness') throw new Error('Expected positive fixture');
        assert.deepEqual(second.column.components.slice(0, 2).map(serializeAlgebraPolynomial),
            b.witness.coefficients.map(serializeAlgebraPolynomial));
        assert.notEqual(serializeCoreExpression(first.realization.formalDifferentials[1]),
            serializeCoreExpression(second.realization.formalDifferentials[1]));
        assert.notEqual(first.sourceData, second.sourceData);
        assert.equal(second.environment.lookup('external_reuse_complex'), undefined);
    });

    it('constructs a transparent whole complex and consumes its projected differential', async () => {
        const result = await adoptAlgebraExternalModuleComplex({
            workspace: workspace(), external: await external(true), decision, fingerprint
        });
        assert.equal(result.adopted.source.entries.length, 1);
        const law = result.adopted.source.entries[0];
        assert.equal(law.classification, 'computed-equation');
        assert.equal(law.declaration.body, undefined);
        assert.equal(law.adoptionArtifact.authority, 'checked-relative-to-explicit-assumption');
        const complex = result.environment.lookup('external_reuse_complex')!;
        assert.equal(complex.transparency, 'transparent');
        assert.equal(serializeCoreExpression(complex.body!), serializeCoreExpression(result.assembled.term));
        assert.ok(result.environment.lookup('external_reuse_image')!.body);
        assert.match(serializeCoreExpression(result.image), /external_reuse_complex/u);
        assert.match(serializeCoreExpression(result.image), /bridge_comm_ring_matrix_apply/u);
        const checker = createCoreProofChecker(result.environment);
        const wrong = assembleFormalTwoStepComplex({
            formalRing: result.data.formalRing, ranks: [1, 4, 1],
            lower: result.data.realization.formalDifferentials[0],
            upper: result.data.realization.formalDifferentials[1], law: law.reference
        });
        assert.throws(() => checker.check(checker.rootContext, wrong.term, wrong.type));
    });

    it('requires an explicit decision and invalidates both changed inputs and changed valid results', async () => {
        const a = await external(), b = await external(true);
        await assert.rejects(adoptAlgebraExternalModuleComplex({
            workspace: workspace(), external: a, decision: undefined as never, fingerprint
        }), /explicit adoption/u);
        const result = await adoptAlgebraExternalModuleComplex({ workspace: workspace(), external: a, decision, fingerprint });
        assertAlgebraExternalModuleReuseCurrent(workspace(), a, result);
        assert.throws(() => assertAlgebraExternalModuleReuseCurrent(workspace(), b, result), /Stale/u);
        const w = workspace();
        assert.throws(() => prepareAlgebraExternalModuleData({ ...w, left: w.right }, a), /Stale/u);
        if (a.kind !== 'witness') throw new Error('Expected positive fixture');
        assert.throws(() => prepareAlgebraExternalModuleData(w, {
            ...a, witness: { ...a.witness, coefficients: [w.right, w.right] }
        }), /does not equal/u);
    });

    it('pins the assembly interface to its reviewed active owner', () => {
        const owner = resolve(__dirname, '..', 'emdash2', FORMAL_BOUNDED_COMPLEX_ASSEMBLY_PROFILE.owner);
        const hash = createHash('sha256').update(readFileSync(owner)).digest('hex');
        assert.equal(hash, FORMAL_BOUNDED_COMPLEX_ASSEMBLY_PROFILE.sourceSha256);
    });

    it('rejects a foreign parent and an unsupported valid rational witness without native substitution', async () => {
        const chosen = await external();
        if (chosen.kind !== 'witness') throw new Error('Expected positive fixture');
        const foreign = algebraPolynomialOne(algebraPolynomialRing(RATIONAL_DOMAIN, ['z']));
        assert.throws(() => prepareAlgebraExternalModuleData(workspace(), {
            ...chosen, witness: { ...chosen.witness, coefficients: [foreign, foreign] }
        }), /ring|parent/iu);
        const rational = await external('rational');
        assert.equal(rational.kind, 'witness');
        assert.throws(() => prepareAlgebraExternalModuleData(workspace(), rational),
            /rational-field interpretation is not supplied/u);
        assert.throws(() => prepareAlgebraExternalModuleData(workspace(), {
            ...chosen, kind: 'nonmembership-observation', authority: 'external-observation'
        }), /positive external witness/u);
    });

    it('uses real Singular data and checks whole construction, projection and action in Lambdapi', {
        skip: process.env.EMDASH_RUN_EXTERNAL_MODULE_REUSE !== '1'
    }, async () => {
        const w = workspace();
        const chosen = await computeSingularIdealWitness(algebraPolynomialWorkspaceInput(w), createAlgebraOracleNodeTransport());
        const result = await adoptAlgebraExternalModuleComplex({ workspace: w, external: chosen, decision, fingerprint });
        const declarationNames = [result.data.formalRing.name,
            ...result.data.formalVariables.map(term => term.name),
            ...result.adopted.source.entries.map(entry => entry.declaration.name),
            'external_reuse_complex', 'external_reuse_argument', 'external_reuse_image'];
        const declarations = declarationNames.map(name => {
            const declaration = result.environment.lookup(name);
            assert.ok(declaration, `Missing consumer declaration ${name}`);
            return declaration;
        });
        const bindings = { ...AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS,
            ...AFFINE_FORMAL_FINITE_MODULE_BINDINGS, ...AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS,
            ...FORMAL_BOUNDED_COMPLEX_ASSEMBLY_BINDINGS,
            ...Object.fromEntries(declarations.map(d => [d.name, d.name])) };
        const serialize = (term: Parameters<typeof serializeKernelExpression>[0]) =>
            serializeKernelExpression(term, { externalFreeReferences: bindings });
        const prefix = ['require open emdash.emdash3_2_commutative_algebra_bounded_free_complexes;',
            ...declarations.map(d => `symbol ${d.name} : ${serialize(d.type)}` +
                (d.body ? ` ≔ ${serialize(d.body)}` : '') + ';')];
        const directImage = formalComplexCall('bridge_comm_ring_matrix_apply',
            [result.data.formalRing, formalComplexNat(result.data.column.parent.rank), formalComplexNat(1),
                result.data.realization.formalDifferentials[1], result.argument]);
        const source = [...prefix,
            `assert ⊢ ${serialize(result.image)} : ${serialize(result.imageType)};`,
            `assert ⊢ ${serialize(result.projected.term)} ≡ ${serialize(result.data.realization.formalDifferentials[1])};`,
            `assert ⊢ ${serialize(result.image)} ≡ ${serialize(directImage)};`
        ].join('\n') + '\n';
        const packageRoot = resolve(__dirname, '..', 'emdash2');
        const positive = checkLambdapiProbe({ source, sourceMap: [] }, { packageRoot, timeoutMs: 60_000 });
        assert.equal(positive.accepted, true, positive.diagnostics);
        let other = prepareAlgebraExternalModuleData(w, await external());
        if (serialize(other.realization.formalDifferentials[1]) === serialize(result.data.realization.formalDifferentials[1])) {
            other = prepareAlgebraExternalModuleData(w, await external(true));
        }
        const negative = checkLambdapiProbe({ source: [...prefix,
            `assert ⊢ ${serialize(result.projected.term)} ≡ ${serialize(other.realization.formalDifferentials[1])};`
        ].join('\n') + '\n', sourceMap: [] }, { packageRoot, timeoutMs: 60_000 });
        assert.equal(negative.timedOut, false, negative.diagnostics);
        assert.equal(negative.accepted, false);
        assert.match(negative.diagnostics, /Assertion failed/iu);
        assert.doesNotMatch(negative.diagnostics, /Syntax error|Unknown symbol|Unknown identifier/iu);
    });
});
