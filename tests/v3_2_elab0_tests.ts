/**
 * Focused ELAB-0 through ELAB-1B tests for the active v3.2 target boundary.
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
    PROJECTION_PAIR_SCHEMAS,
    SURFACE_OPERATION_SCHEMAS,
    SurfaceContext,
    V32ElaborationError,
    binderMode,
    categoryType,
    checkLambdapiProbe,
    compileSurfaceProbe,
    coreTypeToKernelType,
    declarationsFromSurfaceContext,
    elaborateSurfaceTerm,
    functorType,
    homCategory,
    homType,
    kernelApplication,
    objectType,
    provenance,
    serializeKernelExpression,
    serializeKernelProbe,
    sourceSpan,
    surfaceBinding,
    surfaceFapp0,
    surfaceFapp1,
    surfaceFapp1Func,
    surfaceOperation,
    surfaceReference,
    surfaceTapp0,
    surfaceTapp0Func,
    surfaceTapp1,
    surfaceTapp1Func,
    transforType
} from '../src/v3_2';

const fixture = 'tests/fixtures/elab0.surface.ts';
const at = (line: number, startColumn = 1, endColumn = startColumn + 1) =>
    sourceSpan(fixture, line, startColumn, line, endColumn);

function buildContext(): SurfaceContext {
    return new SurfaceContext([
        surfaceBinding('elab0_A', categoryType(), at(1)),
        surfaceBinding('elab0_B', categoryType(), at(2)),
        surfaceBinding('elab0_C', categoryType(), at(3)),
        surfaceBinding('elab0_x', objectType('elab0_A'), at(4)),
        surfaceBinding('elab0_y', objectType('elab0_A'), at(5)),
        surfaceBinding('elab0_u', objectType('elab0_C'), at(6)),
        surfaceBinding('elab0_v', objectType('elab0_C'), at(7)),
        surfaceBinding(
            'elab0_F',
            functorType('elab0_A', 'elab0_B'),
            at(8)
        ),
        surfaceBinding(
            'elab0_G',
            functorType('elab0_A', 'elab0_B'),
            at(9)
        ),
        surfaceBinding(
            'elab0_f',
            homType('elab0_A', 'elab0_x', 'elab0_y'),
            at(10)
        ),
        surfaceBinding(
            'elab0_h',
            homType('elab0_C', 'elab0_u', 'elab0_v'),
            at(11)
        ),
        surfaceBinding(
            'elab0_eta',
            transforType(
                'elab0_A',
                'elab0_B',
                'elab0_F',
                'elab0_G'
            ),
            at(12),
            binderMode('implicit', 'natural')
        ),
        surfaceBinding(
            'elab0_g',
            homType('elab0_A', 'elab0_x', 'elab0_y'),
            at(13)
        ),
        surfaceBinding(
            'elab0_alpha',
            homType(
                homCategory('elab0_A', 'elab0_x', 'elab0_y'),
                'elab0_f',
                'elab0_g'
            ),
            at(14)
        )
    ]);
}

const ref = (name: string, line: number) =>
    surfaceReference(name, at(line));

const fapp0Case = () => surfaceFapp0(
    ref('elab0_F', 20),
    ref('elab0_x', 20),
    at(20, 1, 19)
);

const fapp1Case = () => surfaceFapp1(
    ref('elab0_F', 21),
    ref('elab0_f', 21),
    at(21, 1, 25)
);

const tapp0Case = () => surfaceTapp0(
    ref('elab0_eta', 22),
    ref('elab0_x', 22),
    at(22, 1, 27)
);

const tapp1Case = () => surfaceTapp1(
    ref('elab0_eta', 23),
    ref('elab0_f', 23),
    at(23, 1, 30)
);

const fapp1FuncCase = () => surfaceFapp1Func(
    ref('elab0_F', 24),
    ref('elab0_x', 24),
    ref('elab0_y', 24),
    at(24, 1, 32)
);

const tapp0FuncCase = () => surfaceTapp0Func(
    ref('elab0_F', 25),
    ref('elab0_G', 25),
    ref('elab0_x', 25),
    at(25, 1, 34)
);

const tapp1FuncCase = () => surfaceTapp1Func(
    ref('elab0_eta', 26),
    ref('elab0_x', 26),
    ref('elab0_y', 26),
    at(26, 1, 38)
);

const recursiveFapp1Case = () => surfaceFapp0(
    surfaceFapp1Func(
        fapp1FuncCase(),
        ref('elab0_f', 27),
        ref('elab0_g', 27),
        at(27, 1, 49)
    ),
    ref('elab0_alpha', 27),
    at(27, 1, 65)
);

function compilePositiveProbe(context: SurfaceContext) {
    return compileSurfaceProbe(context, [
        { label: 'ELAB-0 object application', term: fapp0Case() },
        { label: 'ELAB-0 arrow application', term: fapp1Case() },
        { label: 'ELAB-1A transfor component', term: tapp0Case() },
        { label: 'ELAB-0 transfor application', term: tapp1Case() }
    ]);
}

function compileFullProjectionProbe(context: SurfaceContext) {
    const fullFapp1 = fapp1FuncCase();
    const fullTapp0 = tapp0FuncCase();
    const fullTapp1 = tapp1FuncCase();
    const compiled = compileSurfaceProbe(context, [
        { label: 'ELAB-1B full functor hom action', term: fullFapp1 },
        { label: 'ELAB-1B full transfor component', term: fullTapp0 },
        { label: 'ELAB-1B full transfor hom action', term: fullTapp1 },
        { label: 'ELAB-1B recursive 2-cell action', term: recursiveFapp1Case() }
    ]);
    const conversion = (
        label: string,
        left: ReturnType<typeof surfaceFapp0>,
        right: ReturnType<typeof surfaceFapp0>,
        line: number
    ) => ({
        label,
        left: elaborateSurfaceTerm(context, left).term,
        right: elaborateSurfaceTerm(context, right).term,
        span: at(line, 1, 60)
    });
    const probe: KernelProbe = {
        ...compiled.probe,
        conversions: [
            conversion(
                'ELAB-1B fapp1 full/capped evaluator',
                surfaceFapp0(
                    fullFapp1,
                    ref('elab0_f', 28),
                    at(28, 1, 45)
                ),
                fapp1Case(),
                28
            ),
            conversion(
                'ELAB-1B tapp0 full/capped evaluator',
                surfaceFapp0(
                    fullTapp0,
                    ref('elab0_eta', 29),
                    at(29, 1, 48)
                ),
                tapp0Case(),
                29
            ),
            conversion(
                'ELAB-1B tapp1 full/capped evaluator',
                surfaceFapp0(
                    fullTapp1,
                    ref('elab0_f', 30),
                    at(30, 1, 50)
                ),
                tapp1Case(),
                30
            )
        ]
    };
    return {
        ...compiled,
        probe,
        serialized: serializeKernelProbe(probe)
    };
}

describe('TypeScript v3.2 ELAB-0 compatibility through ELAB-1B', () => {
    it('models plicity independently from binder variation', () => {
        const explicitObjectOnly = binderMode('explicit', 'object-only');
        const implicitNatural = binderMode('implicit', 'natural');

        assert.deepEqual(explicitObjectOnly, {
            plicity: 'explicit',
            variation: 'object-only'
        });
        assert.deepEqual(implicitNatural, {
            plicity: 'implicit',
            variation: 'natural'
        });

        const eta = buildContext().lookup('elab0_eta');
        assert.ok(eta);
        assert.deepEqual(eta.mode, implicitNatural);
    });

    it('keeps semantic owner schemas separate from Lambdapi bindings', () => {
        assert.equal(
            SURFACE_OPERATION_SCHEMAS['transfor.component.capped'].owner,
            'transfor-component-capped'
        );
        assert.deepEqual(
            CORE_OWNER_SCHEMAS['transfor-component-capped'].slots.map(
                slot => [slot.name, slot.plicity]
            ),
            [
                ['A', 'implicit'],
                ['B', 'implicit'],
                ['F', 'implicit'],
                ['G', 'implicit'],
                ['Y', 'explicit'],
                ['eta', 'explicit']
            ]
        );
        const backend =
            LAMBDAPI_V32_OWNER_BINDINGS['transfor-component-capped'];
        assert.equal(backend.serializedName, 'tapp0_fapp0');
        assert.equal(
            backend.provenance.authorityPath,
            'emdash2/emdash3_2.lp'
        );
        assert.match(backend.provenance.declaration, /symbol tapp0_fapp0/);

        const operations = [
            fapp0Case(),
            fapp1Case(),
            tapp0Case(),
            tapp1Case()
        ];
        assert.ok(operations.every(term => term.tag === 'operation'));
    });

    it('records all three full/capped evaluator pairs explicitly', () => {
        assert.deepEqual(PROJECTION_PAIR_SCHEMAS, {
            'functor-hom': {
                family: 'functor-action',
                dimension: 'hom',
                variance: 'diagonal',
                full: 'functor-hom-full',
                capped: 'functor-hom-capped',
                evaluator: 'functor-object'
            },
            'transfor-component': {
                family: 'transfor-action',
                dimension: 'object',
                variance: 'diagonal',
                full: 'transfor-component-full',
                capped: 'transfor-component-capped',
                evaluator: 'functor-object'
            },
            'transfor-hom': {
                family: 'transfor-action',
                dimension: 'hom',
                variance: 'off-diagonal',
                full: 'transfor-hom-full',
                capped: 'transfor-hom-capped',
                evaluator: 'functor-object'
            }
        });
        assert.deepEqual(
            CORE_OWNER_SCHEMAS['functor-hom-full'].slots.map(
                slot => [slot.name, slot.plicity]
            ),
            [
                ['A', 'implicit'],
                ['B', 'implicit'],
                ['F', 'explicit'],
                ['X', 'implicit'],
                ['Y', 'implicit']
            ]
        );
        assert.equal(
            LAMBDAPI_V32_OWNER_BINDINGS['functor-hom-full'].serializedName,
            'fapp1_func'
        );
        assert.equal(
            LAMBDAPI_V32_OWNER_BINDINGS['transfor-component-full']
                .serializedName,
            'tapp0_func'
        );
        assert.equal(
            LAMBDAPI_V32_OWNER_BINDINGS['transfor-hom-full'].serializedName,
            'tapp1_func'
        );
    });

    it('rejects malformed generic operation arity at the operation span', () => {
        const malformed = surfaceOperation(
            'functor.object',
            [ref('elab0_F', 19)],
            at(19, 1, 12)
        );
        assert.throws(
            () => elaborateSurfaceTerm(buildContext(), malformed),
            (error: unknown) => {
                assert.ok(error instanceof V32ElaborationError);
                assert.equal(error.code, 'OPERATION_ARITY_MISMATCH');
                assert.equal(error.span.start.line, 19);
                return true;
            }
        );
    });

    it('recovers both category slots for fapp0', () => {
        const result = elaborateSurfaceTerm(buildContext(), fapp0Case());
        assert.equal(
            serializeKernelExpression(result.term),
            '@fapp0 elab0_A elab0_B elab0_F elab0_x'
        );
        assert.deepEqual(
            result.recovered.map(slot => slot.slot),
            ['A', 'B']
        );

        assert.equal(result.term.tag, 'application');
        const application = result.term as KernelApplication;
        assert.deepEqual(
            application.arguments.map(argument => argument.plicity),
            ['implicit', 'implicit', 'explicit', 'explicit']
        );
        assert.deepEqual(
            application.arguments.map(argument => argument.provenance.origin),
            ['recovered', 'recovered', 'surface', 'surface']
        );
    });

    it('lowers tapp0_fapp0 with an exact diagonal result classifier', () => {
        const result = elaborateSurfaceTerm(buildContext(), tapp0Case());
        assert.equal(
            serializeKernelExpression(result.term),
            '@tapp0_fapp0 elab0_A elab0_B elab0_F elab0_G ' +
            'elab0_x elab0_eta'
        );
        assert.deepEqual(
            result.recovered.map(slot => slot.slot),
            ['A', 'B', 'F', 'G']
        );
        assert.equal(
            serializeKernelExpression(coreTypeToKernelType(
                result.type,
                result.sourceSpan,
                'ELAB-1A exact tapp0 result'
            )),
            'τ (Hom elab0_B ' +
            '(@fapp0 elab0_A elab0_B elab0_F elab0_x) ' +
            '(@fapp0 elab0_A elab0_B elab0_G elab0_x))'
        );

        assert.equal(result.term.tag, 'application');
        const application = result.term as KernelApplication;
        assert.deepEqual(
            application.arguments.map(argument => argument.plicity),
            [
                'implicit',
                'implicit',
                'implicit',
                'implicit',
                'explicit',
                'explicit'
            ]
        );
    });

    it('lowers fapp1_fapp0 and tapp1_fapp0 with every implicit slot explicit', () => {
        const context = buildContext();
        const fapp1 = elaborateSurfaceTerm(context, fapp1Case());
        const tapp1 = elaborateSurfaceTerm(context, tapp1Case());

        assert.equal(
            serializeKernelExpression(fapp1.term),
            '@fapp1_fapp0 elab0_A elab0_B elab0_F ' +
            'elab0_x elab0_y elab0_f'
        );
        assert.deepEqual(
            fapp1.recovered.map(slot => slot.slot),
            ['A', 'B', 'X', 'Y']
        );
        assert.equal(
            serializeKernelExpression(tapp1.term),
            '@tapp1_fapp0 elab0_A elab0_B elab0_F elab0_G ' +
            'elab0_x elab0_y elab0_eta elab0_f'
        );
        assert.deepEqual(
            tapp1.recovered.map(slot => slot.slot),
            ['A', 'B', 'F', 'G', 'X', 'Y']
        );
    });

    it('lowers every full projection with its exact functor classifier', () => {
        const context = buildContext();
        const fapp1 = elaborateSurfaceTerm(context, fapp1FuncCase());
        const tapp0 = elaborateSurfaceTerm(context, tapp0FuncCase());
        const tapp1 = elaborateSurfaceTerm(context, tapp1FuncCase());

        assert.equal(
            serializeKernelExpression(fapp1.term),
            '@fapp1_func elab0_A elab0_B elab0_F elab0_x elab0_y'
        );
        assert.equal(
            serializeKernelExpression(coreTypeToKernelType(
                fapp1.type,
                fapp1.sourceSpan,
                'ELAB-1B exact full fapp1 result'
            )),
            'τ (Functor (Hom_cat elab0_A elab0_x elab0_y) ' +
            '(Hom_cat elab0_B ' +
            '(@fapp0 elab0_A elab0_B elab0_F elab0_x) ' +
            '(@fapp0 elab0_A elab0_B elab0_F elab0_y)))'
        );

        assert.equal(
            serializeKernelExpression(tapp0.term),
            '@tapp0_func elab0_A elab0_B elab0_F elab0_G elab0_x'
        );
        assert.equal(
            serializeKernelExpression(coreTypeToKernelType(
                tapp0.type,
                tapp0.sourceSpan,
                'ELAB-1B exact full tapp0 result'
            )),
            'τ (Functor (@Transf_cat elab0_A elab0_B elab0_F elab0_G) ' +
            '(Hom_cat elab0_B ' +
            '(@fapp0 elab0_A elab0_B elab0_F elab0_x) ' +
            '(@fapp0 elab0_A elab0_B elab0_G elab0_x)))'
        );

        assert.equal(
            serializeKernelExpression(tapp1.term),
            '@tapp1_func elab0_A elab0_B elab0_F elab0_G ' +
            'elab0_x elab0_y elab0_eta'
        );
        assert.equal(
            serializeKernelExpression(coreTypeToKernelType(
                tapp1.type,
                tapp1.sourceSpan,
                'ELAB-1B exact full tapp1 result'
            )),
            'τ (Functor (Hom_cat elab0_A elab0_x elab0_y) ' +
            '(Hom_cat elab0_B ' +
            '(@fapp0 elab0_A elab0_B elab0_F elab0_x) ' +
            '(@fapp0 elab0_A elab0_B elab0_G elab0_y)))'
        );
    });

    it('recurses through ordinary full hom action for a 2-cell', () => {
        const result = elaborateSurfaceTerm(
            buildContext(),
            recursiveFapp1Case()
        );
        assert.equal(result.term.tag, 'application');
        const finalEvaluation = result.term as KernelApplication;
        assert.equal(finalEvaluation.owner, 'functor-object');

        const secondAction = finalEvaluation.arguments[2].value;
        assert.equal(secondAction.tag, 'application');
        assert.equal(
            (secondAction as KernelApplication).owner,
            'functor-hom-full'
        );

        const firstAction =
            (secondAction as KernelApplication).arguments[2].value;
        assert.equal(firstAction.tag, 'application');
        assert.equal(
            (firstAction as KernelApplication).owner,
            'functor-hom-full'
        );
        assert.equal(finalEvaluation.arguments[3].value.tag, 'reference');

        const serialized = serializeKernelExpression(result.term);
        assert.doesNotMatch(serialized, /fapp2/);
        assert.match(serialized, /Hom_cat \(Hom_cat elab0_A/);
    });

    it('rejects a wrong endpoint in the recursive inner hom category', () => {
        const bad = surfaceFapp1Func(
            fapp1FuncCase(),
            ref('elab0_f', 35),
            ref('elab0_h', 36),
            at(35, 1, 54)
        );

        assert.throws(
            () => elaborateSurfaceTerm(buildContext(), bad),
            (error: unknown) => {
                assert.ok(error instanceof V32ElaborationError);
                assert.equal(error.code, 'CATEGORY_MISMATCH');
                assert.equal(error.span.start.line, 36);
                assert.match(error.message, /full functor hom action/);
                assert.match(
                    error.message,
                    /Hom_cat elab0_A elab0_x elab0_y/
                );
                assert.match(
                    error.message,
                    /Hom_cat elab0_C elab0_u elab0_v/
                );
                return true;
            }
        );
    });

    it('rejects a tapp0 component object from the wrong source category', () => {
        const bad = surfaceTapp0(
            ref('elab0_eta', 32),
            ref('elab0_u', 33),
            at(32, 1, 30)
        );

        assert.throws(
            () => elaborateSurfaceTerm(buildContext(), bad),
            (error: unknown) => {
                assert.ok(error instanceof V32ElaborationError);
                assert.equal(error.code, 'CATEGORY_MISMATCH');
                assert.equal(error.span.start.line, 33);
                assert.match(error.message, /transfor point component/);
                assert.match(error.message, /elab0_A/);
                assert.match(error.message, /elab0_C/);
                return true;
            }
        );
    });

    it('rejects a wrong source category at the arrow source span', () => {
        const bad = surfaceFapp1(
            ref('elab0_F', 30),
            ref('elab0_h', 31),
            at(30, 1, 28)
        );

        assert.throws(
            () => elaborateSurfaceTerm(buildContext(), bad),
            (error: unknown) => {
                assert.ok(error instanceof V32ElaborationError);
                assert.equal(error.code, 'CATEGORY_MISMATCH');
                assert.equal(error.span.start.line, 31);
                assert.match(error.message, /elab0_A/);
                assert.match(error.message, /elab0_C/);
                return true;
            }
        );
    });

    it('serializes a deterministic probe and generated-line source map', () => {
        const compiled = compilePositiveProbe(buildContext());
        const source = compiled.serialized.source;

        assert.match(source, /symbol elab0_A : Cat;/);
        assert.match(
            source,
            /symbol elab0_F : τ \(Functor elab0_A elab0_B\);/
        );
        assert.match(
            source,
            /symbol elab0_eta : τ \(@Transf elab0_A elab0_B elab0_F elab0_G\);/
        );
        assert.match(
            source,
            /assert ⊢ @fapp0 elab0_A elab0_B elab0_F elab0_x : τ \(Obj elab0_B\);/
        );
        assert.match(
            source,
            /assert ⊢ @fapp1_fapp0 elab0_A elab0_B elab0_F elab0_x elab0_y elab0_f :/
        );
        assert.match(
            source,
            /assert ⊢ @tapp0_fapp0 elab0_A elab0_B elab0_F elab0_G elab0_x elab0_eta :/
        );
        assert.match(
            source,
            /assert ⊢ @tapp1_fapp0 elab0_A elab0_B elab0_F elab0_G elab0_x elab0_y elab0_eta elab0_f :/
        );

        const assertionEntries = compiled.serialized.sourceMap.filter(
            entry => entry.kind === 'assertion'
        );
        assert.deepEqual(
            assertionEntries.map(entry => entry.sourceSpan.start.line),
            [20, 21, 22, 23]
        );
        for (const entry of assertionEntries) {
            assert.match(
                source.split('\n')[entry.generatedLine - 1],
                /^assert ⊢/
            );
        }
    });

    it('serializes full owners and all evaluator conversions deterministically', () => {
        const compiled = compileFullProjectionProbe(buildContext());
        const source = compiled.serialized.source;

        assert.match(
            source,
            /symbol elab0_alpha : τ \(Hom \(Hom_cat elab0_A elab0_x elab0_y\) elab0_f elab0_g\);/
        );
        assert.match(
            source,
            /assert ⊢ @fapp1_func elab0_A elab0_B elab0_F elab0_x elab0_y :/
        );
        assert.match(
            source,
            /assert ⊢ @tapp0_func elab0_A elab0_B elab0_F elab0_G elab0_x :/
        );
        assert.match(
            source,
            /assert ⊢ @tapp1_func elab0_A elab0_B elab0_F elab0_G elab0_x elab0_y elab0_eta :/
        );
        assert.doesNotMatch(source, /fapp2/);
        assert.match(
            source,
            /assert ⊢ @fapp0 [^\n]*@fapp1_func[^\n]*elab0_f[^\n]*≡ @fapp1_fapp0/
        );
        assert.match(
            source,
            /assert ⊢ @fapp0 [^\n]*@tapp0_func[^\n]*elab0_eta[^\n]*≡ @tapp0_fapp0/
        );
        assert.match(
            source,
            /assert ⊢ @fapp0 [^\n]*@tapp1_func[^\n]*elab0_f[^\n]*≡ @tapp1_fapp0/
        );

        const conversionEntries = compiled.serialized.sourceMap.filter(
            entry => entry.kind === 'conversion'
        );
        assert.deepEqual(
            conversionEntries.map(entry => entry.sourceSpan.start.line),
            [28, 29, 30]
        );
        for (const entry of conversionEntries) {
            assert.match(
                source.split('\n')[entry.generatedLine - 1],
                /^assert ⊢ .* ≡ .*;$/
            );
        }
    });

    it(
        'has a generated positive consumer accepted by Lambdapi',
        { skip: process.env.EMDASH_RUN_LAMBDAPI_PROBES !== '1' },
        () => {
            const compiled = compilePositiveProbe(buildContext());
            const result = checkLambdapiProbe(compiled.serialized, {
                packageRoot: resolve(__dirname, '../emdash2'),
                timeoutMs: 30_000
            });

            assert.equal(
                result.accepted,
                true,
                `Expected positive probe acceptance:\n${result.diagnostics}`
            );
            assert.equal(result.timedOut, false);
        }
    );

    it(
        'has recursive full owners and evaluator conversions accepted by Lambdapi',
        { skip: process.env.EMDASH_RUN_LAMBDAPI_PROBES !== '1' },
        () => {
            const compiled = compileFullProjectionProbe(buildContext());
            const result = checkLambdapiProbe(compiled.serialized, {
                packageRoot: resolve(__dirname, '../emdash2'),
                timeoutMs: 30_000
            });

            assert.equal(
                result.accepted,
                true,
                `Expected ELAB-1B probe acceptance:\n${result.diagnostics}\n` +
                compiled.serialized.source
            );
            assert.equal(result.timedOut, false);
        }
    );

    it(
        'has a corrupted recursive full endpoint rejected by Lambdapi',
        { skip: process.env.EMDASH_RUN_LAMBDAPI_PROBES !== '1' },
        () => {
            const context = buildContext();
            const first = elaborateSurfaceTerm(context, fapp1FuncCase());
            assert.equal(first.type.tag, 'functor');
            if (first.type.tag !== 'functor') {
                throw new Error('Expected the first full action to be a functor');
            }
            const valid = elaborateSurfaceTerm(
                context,
                surfaceFapp1Func(
                    fapp1FuncCase(),
                    ref('elab0_f', 42),
                    ref('elab0_g', 42),
                    at(42, 1, 52)
                )
            );
            const lookup = (name: string) => {
                const binding = context.lookup(name);
                assert.ok(binding, `Missing test binding ${name}`);
                return binding.reference;
            };
            const badSpan = at(43, 1, 55);
            const badTerm = kernelApplication('functor-hom-full', [
                { value: first.type.sourceCategory },
                { value: first.type.targetCategory },
                { value: first.term },
                { value: lookup('elab0_f') },
                // `h` is an object of Hom_C(u,v), not Hom_A(x,y).
                { value: lookup('elab0_h') }
            ], provenance(
                'surface',
                'deliberately corrupted recursive full target',
                badSpan
            ));
            const badProbe: KernelProbe = {
                requiredModule: LAMBDAPI_V32_MODULE,
                declarations: declarationsFromSurfaceContext(context),
                assertions: [{
                    label: 'ELAB-1B negative wrong inner hom endpoint',
                    term: badTerm,
                    type: coreTypeToKernelType(
                        valid.type,
                        badSpan,
                        'expected type for corrupted recursive full target'
                    ),
                    span: badSpan
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
                'Expected Lambdapi to reject an endpoint from the wrong inner hom'
            );
            assert.equal(result.timedOut, false);
            assert.notEqual(result.status, 0);
        }
    );

    it(
        'has a corrupted wrong-endpoint target rejected by Lambdapi',
        { skip: process.env.EMDASH_RUN_LAMBDAPI_PROBES !== '1' },
        () => {
            const context = buildContext();
            const valid = elaborateSurfaceTerm(context, fapp1Case());
            const lookup = (name: string) => {
                const binding = context.lookup(name);
                assert.ok(binding, `Missing test binding ${name}`);
                return binding.reference;
            };
            const badSpan = at(40, 1, 42);
            const badTerm = kernelApplication('functor-hom-capped', [
                { value: lookup('elab0_A') },
                { value: lookup('elab0_B') },
                { value: lookup('elab0_F') },
                { value: lookup('elab0_x') },
                { value: lookup('elab0_y') },
                // This is a C-arrow, not an A-arrow. The explicit target IR
                // is untrusted, so Lambdapi must reject the corruption.
                { value: lookup('elab0_h') }
            ], provenance('surface', 'deliberately corrupted target', badSpan));
            const badProbe: KernelProbe = {
                requiredModule: LAMBDAPI_V32_MODULE,
                declarations: declarationsFromSurfaceContext(context),
                assertions: [{
                    label: 'ELAB-0 negative wrong endpoint',
                    term: badTerm,
                    type: coreTypeToKernelType(
                        valid.type,
                        badSpan,
                        'expected type for corrupted target'
                    ),
                    span: badSpan
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
                'Expected Lambdapi to reject a C-arrow in an A-arrow slot'
            );
            assert.equal(result.timedOut, false);
            assert.notEqual(result.status, 0);
        }
    );

    it(
        'has a corrupted tapp0 object target rejected by Lambdapi',
        { skip: process.env.EMDASH_RUN_LAMBDAPI_PROBES !== '1' },
        () => {
            const context = buildContext();
            const valid = elaborateSurfaceTerm(context, tapp0Case());
            const lookup = (name: string) => {
                const binding = context.lookup(name);
                assert.ok(binding, `Missing test binding ${name}`);
                return binding.reference;
            };
            const badSpan = at(41, 1, 42);
            const badTerm = kernelApplication(
                'transfor-component-capped',
                [
                    { value: lookup('elab0_A') },
                    { value: lookup('elab0_B') },
                    { value: lookup('elab0_F') },
                    { value: lookup('elab0_G') },
                    // This is a C-object, not an A-object.
                    { value: lookup('elab0_u') },
                    { value: lookup('elab0_eta') }
                ],
                provenance(
                    'surface',
                    'deliberately corrupted tapp0 target',
                    badSpan
                )
            );
            const badProbe: KernelProbe = {
                requiredModule: LAMBDAPI_V32_MODULE,
                declarations: declarationsFromSurfaceContext(context),
                assertions: [{
                    label: 'ELAB-1A negative wrong component object',
                    term: badTerm,
                    type: coreTypeToKernelType(
                        valid.type,
                        badSpan,
                        'expected type for corrupted tapp0 target'
                    ),
                    span: badSpan
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
                'Expected Lambdapi to reject a C-object in an A-object slot'
            );
            assert.equal(result.timedOut, false);
            assert.notEqual(result.status, 0);
        }
    );
});
