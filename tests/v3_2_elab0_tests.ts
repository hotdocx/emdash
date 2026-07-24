/**
 * Focused ELAB-0 tests for the active v3.2 target boundary.
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
    surfaceOperation,
    surfaceReference,
    surfaceTapp0,
    surfaceTapp1,
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

function compilePositiveProbe(context: SurfaceContext) {
    return compileSurfaceProbe(context, [
        { label: 'ELAB-0 object application', term: fapp0Case() },
        { label: 'ELAB-0 arrow application', term: fapp1Case() },
        { label: 'ELAB-1A transfor component', term: tapp0Case() },
        { label: 'ELAB-0 transfor application', term: tapp1Case() }
    ]);
}

describe('TypeScript v3.2 ELAB-0 compatibility and ELAB-1A schemas', () => {
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
