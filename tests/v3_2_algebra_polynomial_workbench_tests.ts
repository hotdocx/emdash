import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    algebraPolynomialWorkspaceInput, algebraPolynomialWorkspaceSource,
    assertAlgebraPolynomialWorkbenchCurrent, computeAlgebraPolynomialWorkbench,
    createAlgebraPolynomialWorkbenchExample, prepareAlgebraPolynomialWorkbenchGoal
} from '../src/v3_2/algebra_polynomial_workbench';
import { renderAlgebraPolynomialWorkbenchHtml } from '../src/v3_2/algebra_polynomial_workbench_view';
import {
    ALGEBRA_CURVE_VIEWPORT, renderAlgebraPolynomialCurveSvg, sampleAlgebraPolynomialCurves
} from '../src/v3_2/algebra_polynomial_plot';
import {
    algebraPolynomial, algebraPolynomialAdd, algebraPolynomialOne,
    algebraPolynomialPower, algebraPolynomialZero
} from '../src/v3_2/algebra_polynomial';
import { algebraPolynomialIdeal } from '../src/v3_2/algebra_ideal';
import { AlgebraOracleTransport } from '../src/v3_2/algebra_oracle';
import { createCoreProofArtifactFingerprint } from '../src/v3_2/proof_document';
import { coreProofPlanExact } from '../src/v3_2/proof_plan';
import { kernelFree, provenance } from '../src/v3_2/kernel';
import { adoptAlgebraFormalCheckedPlan } from '../src/v3_2/algebra_formal_adoption';
import { checkLambdapiProbe } from '../src/v3_2/probe';
import { serializeKernelExpression } from '../src/v3_2/lambdapi';
import { AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_zariski_signatures';

const fingerprint = (source: string, profile: string) => {
    const sha256 = (value: string) => 'sha256:' + createHash('sha256').update(value).digest('hex');
    return createCoreProofArtifactFingerprint({
        source: { id: 'tests/polynomial-workbench.json', sha256: sha256(source) },
        profileSha256: sha256(profile)
    });
};
const transport: AlgebraOracleTransport = {
    async execute() {
        return { exitCode: 0, stderr: '', stdout: [
            'EMDASH_WITNESS_V1', 'VERSION:4330', 'MEMBER:1',
            'COEFFICIENT:0', 'TERM:-1:1,0', 'END_COEFFICIENT',
            'COEFFICIENT:1', 'TERM:1:0,0', 'END_COEFFICIENT', 'END_WITNESS'
        ].join('\n') };
    }
};

describe('shared polynomial workbench', () => {
    it('shares exact source between two computations, a view and a freshly checked open goal', async () => {
        const workspace = createAlgebraPolynomialWorkbenchExample();
        const result = await computeAlgebraPolynomialWorkbench(workspace, transport);
        const formal = await prepareAlgebraPolynomialWorkbenchGoal(workspace, fingerprint);
        assert.equal(result.agrees, true);
        assert.equal(result.external.kind, 'witness');
        assert.equal(formal.source, result.source);
        assert.equal(formal.goal.sourceArtifact.state.status, 'incomplete');
        assert.equal(formal.goal.sourceArtifact.state.goals.length, 1);
        assert.equal(formal.hypotheses.length, 2);
        assert.equal(formal.document.plan.tag, 'hole');
        assert.equal(formal.delegated.interpretation.kind, 'claim');
        assert.equal(formal.status, 'open');
        assert.match(formal.reason, /no proof-plan reconstruction/u);
        assert.throws(() => adoptAlgebraFormalCheckedPlan({
            result: formal.delegated,
            replacement: coreProofPlanExact(kernelFree('workbench_hypothesis_0',
                provenance('surface', 'deliberately wrong proof')))
        }));
        const html = renderAlgebraPolynomialWorkbenchHtml(workspace, result, formal);
        assert.match(html, /Formal goal.*Open/u);
        assert.match(html, /No computation assumption has been adopted/u);
        assert.match(html, /Singular witness checked/u);
        assert.doesNotMatch(html, /<script/iu);
    });

    it('invalidates changed targets even when their membership difference stays the same', async () => {
        const workspace = createAlgebraPolynomialWorkbenchExample();
        const result = await computeAlgebraPolynomialWorkbench(workspace, transport);
        const formal = await prepareAlgebraPolynomialWorkbenchGoal(workspace, fingerprint);
        const one = algebraPolynomialOne(workspace.ideal.ring);
        const changed = { ...workspace,
            left: algebraPolynomialAdd(workspace.left, one),
            right: algebraPolynomialAdd(workspace.right, one) };
        assert.notEqual(algebraPolynomialWorkspaceSource(changed), result.source);
        assert.throws(() => assertAlgebraPolynomialWorkbenchCurrent(changed, result), /Stale/u);
        const fresh = await computeAlgebraPolynomialWorkbench(changed, transport);
        assert.equal(fresh.agrees, true);
        assert.throws(() => renderAlgebraPolynomialWorkbenchHtml(changed, fresh, formal), /stale/u);
        const freshFormal = await prepareAlgebraPolynomialWorkbenchGoal(changed, fingerprint);
        assert.notEqual(freshFormal.document.fingerprint.source.sha256, formal.document.fingerprint.source.sha256);
        assert.notEqual(freshFormal.goal.targetCore, formal.goal.targetCore);
        assert.equal(freshFormal.status, 'open');
    });

    it('rejects source mutation while the external request is running', async () => {
        const workspace = { ...createAlgebraPolynomialWorkbenchExample() };
        await assert.rejects(computeAlgebraPolynomialWorkbench(workspace, {
            async execute(request) {
                workspace.left = workspace.right;
                return transport.execute(request);
            }
        }), /changed while/u);
    });

    it('derives approximate contour points from the source coefficients', () => {
        const workspace = createAlgebraPolynomialWorkbenchExample();
        const view = sampleAlgebraPolynomialCurves(algebraPolynomialWorkspaceInput(workspace));
        assert.equal(view.curves.length, 2);
        assert.ok(view.curves.every(curve => curve.segments.length > 100));
        for (const [x, y] of view.curves[0].segments.flat()) assert.ok(Math.abs(y - x * x) < 0.002);
        for (const [x, y] of view.curves[1].segments.flat()) assert.ok(Math.abs(x * y - 1) < 0.002);
        assert.match(renderAlgebraPolynomialCurveSvg(view), /Approximate real loci/u);
        assert.throws(() => sampleAlgebraPolynomialCurves(algebraPolynomialWorkspaceInput(workspace), {
            ...ALGEBRA_CURVE_VIEWPORT, cells: 10000
        }), /cell count/u);
        assert.throws(() => sampleAlgebraPolynomialCurves(algebraPolynomialWorkspaceInput(workspace), {
            ...ALGEBRA_CURVE_VIEWPORT, xMax: Infinity
        }), /finite viewport/u);
    });

    it('records sampling limitations for repeated factors and zero polynomials', () => {
        const workspace = createAlgebraPolynomialWorkbenchExample();
        const ring = workspace.ideal.ring;
        const input = { ideal: algebraPolynomialIdeal(ring, [
            algebraPolynomialPower(workspace.ideal.generators[0], 2n), algebraPolynomialZero(ring)
        ]), polynomial: algebraPolynomialZero(ring) };
        const view = sampleAlgebraPolynomialCurves(input);
        assert.equal(view.curves[0].segments.length, 0);
        assert.equal(view.curves[1].zeroPolynomial, true);
        assert.match(view.limitation, /miss components, tangencies/u);
    });

    it('keeps unsupported rational interpretation out of the formal goal', async () => {
        const workspace = createAlgebraPolynomialWorkbenchExample();
        const changed = { ...workspace, right: algebraPolynomial(workspace.ideal.ring, [
            { coefficient: '1/2', exponents: [0n, 0n] }
        ]) };
        await assert.rejects(prepareAlgebraPolynomialWorkbenchGoal(changed, fingerprint),
            /rational-field interpretation is not supplied/u);
    });

    it('checks the exact goal/data in Lambdapi and rejects an unrelated premise as its proof', {
        skip: process.env.EMDASH_RUN_WORKBENCH_CONFORMANCE !== '1'
    }, async () => {
        const formal = await prepareAlgebraPolynomialWorkbenchGoal(
            createAlgebraPolynomialWorkbenchExample(), fingerprint);
        const declarations = formal.document.environment.declarations
            .filter(declaration => declaration.name.startsWith('workbench_'));
        const serialize = (term: Parameters<typeof serializeKernelExpression>[0]) =>
            serializeKernelExpression(term, { externalFreeReferences: {
                ...AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS,
                ...Object.fromEntries(declarations.map(d => [d.name, d.name]))
            } });
        const prefix = [
            'require open emdash.emdash3_2_commutative_algebra;',
            ...declarations.map(d => `symbol ${d.name} : ${serialize(d.type)};`)
        ];
        const source = [...prefix,
            `assert ⊢ ${serialize(formal.goal.target)} : TYPE;`,
            ...formal.delegated.interpretation.data.map(d =>
                `assert ⊢ ${serialize(d.term)} : ${serialize(d.type)};`)
        ].join('\n') + '\n';
        const packageRoot = resolve(__dirname, '..', 'emdash2');
        const positive = checkLambdapiProbe({ source, sourceMap: [] }, { packageRoot, timeoutMs: 60_000 });
        assert.equal(positive.accepted, true, positive.diagnostics);
        const negative = checkLambdapiProbe({
            source: [...prefix, `assert ⊢ workbench_hypothesis_0 : ${serialize(formal.goal.target)};`].join('\n') + '\n',
            sourceMap: []
        }, { packageRoot, timeoutMs: 60_000 });
        assert.equal(negative.timedOut, false, negative.diagnostics);
        assert.equal(negative.accepted, false);
        assert.match(negative.diagnostics, /type|typ|assert/iu);
    });
});
