/**
 * Focused ELAB-1C partial internal-Hom tests for the active v3.2 target.
 */

import assert from 'node:assert';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_OWNER_SCHEMAS,
    KernelApplication,
    KernelProbe,
    LAMBDAPI_V32_MODULE,
    LAMBDAPI_V32_OWNER_BINDINGS,
    SurfaceContext,
    V32ElaborationError,
    categoryType,
    checkLambdapiProbe,
    compileSurfaceProbe,
    coreTypeToKernelType,
    declarationsFromSurfaceContext,
    elaborateSurfaceTerm,
    functorType,
    kernelApplication,
    objectType,
    provenance,
    serializeKernelExpression,
    serializeKernelProbe,
    sourceSpan,
    surfaceBinding,
    surfaceFapp0,
    surfaceHomConInt,
    surfaceHomInt,
    surfaceReference
} from '../src/v3_2';

const fixture = 'tests/fixtures/elab1c.surface.ts';
const at = (line: number, startColumn = 1, endColumn = startColumn + 1) =>
    sourceSpan(fixture, line, startColumn, line, endColumn);

function buildContext(): SurfaceContext {
    return new SurfaceContext([
        surfaceBinding('elab1c_A', categoryType(), at(1)),
        surfaceBinding('elab1c_B', categoryType(), at(2)),
        surfaceBinding('elab1c_C', categoryType(), at(3)),
        surfaceBinding('elab1c_W', objectType('elab1c_A'), at(4)),
        surfaceBinding('elab1c_b', objectType('elab1c_B'), at(5)),
        surfaceBinding('elab1c_z', objectType('elab1c_C'), at(6)),
        surfaceBinding(
            'elab1c_F',
            functorType('elab1c_B', 'elab1c_A'),
            at(7)
        )
    ]);
}

const ref = (name: string, line: number) =>
    surfaceReference(name, at(line));

const sourceInternalCase = (line = 20) => surfaceHomInt(
    ref('elab1c_F', line),
    at(line, 1, 20)
);

const sourcePartialCase = (line = 21) => surfaceFapp0(
    sourceInternalCase(line),
    ref('elab1c_W', line),
    at(line, 1, 33)
);

const sourceFinalCase = (line = 22) => surfaceFapp0(
    sourcePartialCase(line),
    ref('elab1c_b', line),
    at(line, 1, 46)
);

const targetInternalCase = (line = 23) => surfaceHomConInt(
    ref('elab1c_F', line),
    at(line, 1, 24)
);

const targetPartialCase = (line = 24) => surfaceFapp0(
    targetInternalCase(line),
    ref('elab1c_W', line),
    at(line, 1, 37)
);

const targetFinalCase = (line = 25) => surfaceFapp0(
    targetPartialCase(line),
    ref('elab1c_b', line),
    at(line, 1, 50)
);

function lookupReference(context: SurfaceContext, name: string) {
    const binding = context.lookup(name);
    assert.ok(binding, `Missing ELAB-1C test binding ${name}`);
    return binding.reference;
}

function exactNormalForms(context: SurfaceContext, line: number) {
    const span = at(line, 1, 60);
    const nodeProvenance = provenance(
        'derived',
        'ELAB-1C expected internal-Hom normal form',
        span
    );
    const A = lookupReference(context, 'elab1c_A');
    const B = lookupReference(context, 'elab1c_B');
    const F = lookupReference(context, 'elab1c_F');
    const W = lookupReference(context, 'elab1c_W');
    const b = lookupReference(context, 'elab1c_b');
    const Fb = kernelApplication('functor-object', [
        { value: B },
        { value: A },
        { value: F },
        { value: b }
    ], nodeProvenance);

    return {
        source: kernelApplication('hom-category', [
            { value: A },
            { value: W },
            { value: Fb }
        ], nodeProvenance),
        target: kernelApplication('hom-category', [
            { value: A },
            { value: Fb },
            { value: W }
        ], nodeProvenance)
    };
}

function compileInternalHomProbe(context: SurfaceContext) {
    const compiled = compileSurfaceProbe(context, [
        {
            label: 'ELAB-1C source internal-Hom functor',
            term: sourceInternalCase()
        },
        {
            label: 'ELAB-1C retained source internal-Hom family',
            term: sourcePartialCase()
        },
        {
            label: 'ELAB-1C projected source internal-Hom category',
            term: sourceFinalCase()
        },
        {
            label: 'ELAB-1C target internal-Hom functor',
            term: targetInternalCase()
        },
        {
            label: 'ELAB-1C retained target internal-Hom family',
            term: targetPartialCase()
        },
        {
            label: 'ELAB-1C projected target internal-Hom category',
            term: targetFinalCase()
        }
    ]);
    const normalForms = exactNormalForms(context, 40);
    const probe: KernelProbe = {
        ...compiled.probe,
        conversions: [
            {
                label: 'ELAB-1C source internal-Hom variance',
                left: compiled.cases[2].elaborated.term,
                right: normalForms.source,
                span: at(40, 1, 60)
            },
            {
                label: 'ELAB-1C target internal-Hom variance',
                left: compiled.cases[5].elaborated.term,
                right: normalForms.target,
                span: at(41, 1, 60)
            }
        ]
    };

    return {
        ...compiled,
        probe,
        serialized: serializeKernelProbe(probe)
    };
}

function assertTwoStageProjection(
    term: ReturnType<typeof elaborateSurfaceTerm>['term'],
    constructor: 'internal-hom-source' | 'internal-hom-target'
): void {
    assert.equal(term.tag, 'application');
    const finalProjection = term as KernelApplication;
    assert.equal(finalProjection.owner, 'functor-object');

    const retainedFamily = finalProjection.arguments[2].value;
    assert.equal(retainedFamily.tag, 'application');
    assert.equal(
        (retainedFamily as KernelApplication).owner,
        'functor-object'
    );

    const internalHom =
        (retainedFamily as KernelApplication).arguments[2].value;
    assert.equal(internalHom.tag, 'application');
    assert.equal((internalHom as KernelApplication).owner, constructor);
}

describe('TypeScript v3.2 ELAB-1C partial internal Hom', () => {
    it('records semantic internal-Hom owners separately from the backend', () => {
        assert.deepEqual(
            CORE_OWNER_SCHEMAS['internal-hom-source'].slots.map(
                slot => [slot.name, slot.plicity, slot.role]
            ),
            [
                ['A', 'implicit', 'target-category'],
                ['B', 'implicit', 'source-category'],
                ['F', 'explicit', 'functor']
            ]
        );
        assert.deepEqual(
            CORE_OWNER_SCHEMAS['internal-hom-target'].slots.map(
                slot => [slot.name, slot.plicity, slot.role]
            ),
            [
                ['A', 'implicit', 'target-category'],
                ['B', 'implicit', 'source-category'],
                ['F', 'explicit', 'functor']
            ]
        );
        assert.equal(
            LAMBDAPI_V32_OWNER_BINDINGS['internal-hom-source']
                .serializedName,
            'hom_int'
        );
        assert.equal(
            LAMBDAPI_V32_OWNER_BINDINGS['internal-hom-target']
                .serializedName,
            'hom_con_int'
        );
    });

    it('retains and later projects the source-varying internal Hom', () => {
        const context = buildContext();
        const internal = elaborateSurfaceTerm(context, sourceInternalCase());
        const retained = elaborateSurfaceTerm(context, sourcePartialCase());
        const projected = elaborateSurfaceTerm(context, sourceFinalCase());

        assert.equal(
            serializeKernelExpression(internal.term),
            '@hom_int elab1c_A elab1c_B elab1c_F'
        );
        assert.equal(
            serializeKernelExpression(coreTypeToKernelType(
                internal.type,
                internal.sourceSpan,
                'ELAB-1C source internal-Hom type'
            )),
            'τ (Functor (Op_cat elab1c_A) (Catd_cat elab1c_B))'
        );
        assert.equal(
            serializeKernelExpression(coreTypeToKernelType(
                retained.type,
                retained.sourceSpan,
                'ELAB-1C retained source family type'
            )),
            'τ (Functor elab1c_B (Cat_cat))'
        );
        assert.equal(projected.type.tag, 'category');
        assert.equal(
            serializeKernelExpression(projected.term),
            '@fapp0 elab1c_B (Cat_cat) ' +
            '(@fapp0 (Op_cat elab1c_A) (Catd_cat elab1c_B) ' +
            '(@hom_int elab1c_A elab1c_B elab1c_F) elab1c_W) ' +
            'elab1c_b'
        );
        assertTwoStageProjection(projected.term, 'internal-hom-source');
    });

    it('retains and later projects the target-varying internal Hom', () => {
        const context = buildContext();
        const internal = elaborateSurfaceTerm(context, targetInternalCase());
        const retained = elaborateSurfaceTerm(context, targetPartialCase());
        const projected = elaborateSurfaceTerm(context, targetFinalCase());

        assert.equal(
            serializeKernelExpression(internal.term),
            '@hom_con_int elab1c_A elab1c_B elab1c_F'
        );
        assert.equal(
            serializeKernelExpression(coreTypeToKernelType(
                internal.type,
                internal.sourceSpan,
                'ELAB-1C target internal-Hom type'
            )),
            'τ (Functor elab1c_A (Catd_cat (Op_cat elab1c_B)))'
        );
        assert.equal(
            serializeKernelExpression(coreTypeToKernelType(
                retained.type,
                retained.sourceSpan,
                'ELAB-1C retained target family type'
            )),
            'τ (Functor (Op_cat elab1c_B) (Cat_cat))'
        );
        assert.equal(projected.type.tag, 'category');
        assert.equal(
            serializeKernelExpression(projected.term),
            '@fapp0 (Op_cat elab1c_B) (Cat_cat) ' +
            '(@fapp0 elab1c_A (Catd_cat (Op_cat elab1c_B)) ' +
            '(@hom_con_int elab1c_A elab1c_B elab1c_F) elab1c_W) ' +
            'elab1c_b'
        );
        assertTwoStageProjection(projected.term, 'internal-hom-target');
    });

    it('rejects a later object from the wrong internalized base', () => {
        const bad = surfaceFapp0(
            sourcePartialCase(31),
            ref('elab1c_z', 32),
            at(31, 1, 48)
        );

        assert.throws(
            () => elaborateSurfaceTerm(buildContext(), bad),
            (error: unknown) => {
                assert.ok(error instanceof V32ElaborationError);
                assert.equal(error.code, 'CATEGORY_MISMATCH');
                assert.equal(error.span.start.line, 32);
                assert.match(error.message, /functor object action/);
                assert.match(error.message, /elab1c_B/);
                assert.match(error.message, /elab1c_C/);
                return true;
            }
        );
    });

    it('serializes both exact variance conversions without collapsing them', () => {
        const context = buildContext();
        const compiled = compileInternalHomProbe(context);
        const source = compiled.serialized.source;
        const normalForms = exactNormalForms(context, 42);
        const sourceNormal = serializeKernelExpression(normalForms.source);
        const targetNormal = serializeKernelExpression(normalForms.target);

        assert.equal(
            sourceNormal,
            'Hom_cat elab1c_A elab1c_W ' +
            '(@fapp0 elab1c_B elab1c_A elab1c_F elab1c_b)'
        );
        assert.equal(
            targetNormal,
            'Hom_cat elab1c_A ' +
            '(@fapp0 elab1c_B elab1c_A elab1c_F elab1c_b) elab1c_W'
        );
        assert.notEqual(sourceNormal, targetNormal);
        assert.ok(source.includes(
            '≡ Hom_cat elab1c_A elab1c_W ' +
            '(@fapp0 elab1c_B elab1c_A elab1c_F elab1c_b);'
        ));
        assert.ok(source.includes(
            '≡ Hom_cat elab1c_A ' +
            '(@fapp0 elab1c_B elab1c_A elab1c_F elab1c_b) elab1c_W;'
        ));

        const conversionEntries = compiled.serialized.sourceMap.filter(
            entry => entry.kind === 'conversion'
        );
        assert.deepEqual(
            conversionEntries.map(entry => entry.sourceSpan.start.line),
            [40, 41]
        );
    });

    it(
        'has both retained internal-Hom routes accepted by Lambdapi',
        { skip: process.env.EMDASH_RUN_LAMBDAPI_PROBES !== '1' },
        () => {
            const compiled = compileInternalHomProbe(buildContext());
            const result = checkLambdapiProbe(compiled.serialized, {
                packageRoot: resolve(__dirname, '../emdash2'),
                timeoutMs: 30_000
            });

            assert.equal(
                result.accepted,
                true,
                `Expected ELAB-1C probe acceptance:\n` +
                `${result.diagnostics}\n${compiled.serialized.source}`
            );
            assert.equal(result.timedOut, false);
        }
    );

    it(
        'has a source/target-reversed target route rejected by Lambdapi',
        { skip: process.env.EMDASH_RUN_LAMBDAPI_PROBES !== '1' },
        () => {
            const context = buildContext();
            const compiled = compileSurfaceProbe(context, [{
                label: 'ELAB-1C target route before deliberate reversal',
                term: targetFinalCase(45)
            }]);
            const reversed = exactNormalForms(context, 46).source;
            const badProbe: KernelProbe = {
                requiredModule: LAMBDAPI_V32_MODULE,
                declarations: declarationsFromSurfaceContext(context),
                assertions: compiled.probe.assertions,
                conversions: [{
                    label: 'ELAB-1C negative reversed target variance',
                    left: compiled.cases[0].elaborated.term,
                    right: reversed,
                    span: at(46, 1, 60)
                }]
            };
            const result = checkLambdapiProbe(
                serializeKernelProbe(badProbe),
                {
                    packageRoot: resolve(__dirname, '../emdash2'),
                    timeoutMs: 30_000
                }
            );

            assert.equal(
                result.accepted,
                false,
                'Expected Lambdapi to reject reversed target-Hom variance'
            );
            assert.equal(result.timedOut, false);
            assert.notEqual(result.status, 0);
        }
    );
});
