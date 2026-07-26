/**
 * Focused USABILITY-1B/1C contextual IR, eta, and basic bracket tests.
 */

import assert from 'node:assert/strict';
import {
    readFileSync
} from 'node:fs';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_MVP_MANIFEST,
    CORE_OWNER_SCHEMAS,
    CoreCategoricalFrontendError,
    CoreCategoricalScopedBuilder,
    CoreCategoricalTerm,
    KernelApplication,
    KernelCall,
    SurfaceContext,
    categoryType,
    coreTypeEquals,
    coreCategoricalStructuralCoreName,
    elaborateSurfaceOperationFromOperands,
    elaborateSurfaceTerm,
    functorType,
    homCategory,
    homType,
    kernelExpressionEquals,
    objectType,
    provenance,
    selectCoreCategoricalAbstraction,
    sourceSpan,
    surfaceBinding,
    surfaceFapp0,
    surfaceReference
} from '../src/v3_2';

const fixture = 'tests/fixtures/categorical-surface.ts';
const at = (
    line: number,
    startColumn = 1,
    endColumn = startColumn + 1
) => sourceSpan(
    fixture,
    line,
    startColumn,
    line,
    endColumn
);

const here = (line: number, detail: string) =>
    provenance('surface', detail, at(line));

const buildContext = (): SurfaceContext => new SurfaceContext([
    surfaceBinding('cat_A', categoryType(), at(1)),
    surfaceBinding('cat_B', categoryType(), at(2)),
    surfaceBinding('cat_C', categoryType(), at(3)),
    surfaceBinding('cat_x', objectType('cat_A'), at(4)),
    surfaceBinding('cat_y', objectType('cat_A'), at(5)),
    surfaceBinding('cat_b', objectType('cat_B'), at(6)),
    surfaceBinding('cat_c', objectType('cat_C'), at(7)),
    surfaceBinding(
        'cat_F',
        functorType('cat_A', 'cat_B'),
        at(8)
    ),
    surfaceBinding(
        'cat_G',
        functorType('cat_B', 'cat_C'),
        at(9)
    ),
    surfaceBinding(
        'cat_f',
        homType('cat_A', 'cat_x', 'cat_y'),
        at(10)
    ),
    surfaceBinding(
        'cat_H',
        functorType(
            homCategory('cat_A', 'cat_x', 'cat_y'),
            'cat_B'
        ),
        at(11)
    )
]);

const ref = (
    context: SurfaceContext,
    name: string,
    line: number
) => elaborateSurfaceTerm(
    context,
    surfaceReference(name, at(line))
);

const assertFrontendError = (
    action: () => unknown,
    code: CoreCategoricalFrontendError['code'],
    message?: RegExp
): void => {
    assert.throws(
        action,
        error =>
            error instanceof CoreCategoricalFrontendError &&
            error.code === code &&
            (message === undefined || message.test(error.message))
    );
};

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    if (value instanceof Map) return;
    Reflect.ownKeys(value).forEach(key =>
        assertDeepFrozen(
            (value as Record<PropertyKey, unknown>)[key]
        )
    );
};

describe('TypeScript v3.2 USABILITY-1B/1C categorical surface', () => {
    it('reuses the declarative operation interpreter for typed operands', () => {
        const context = buildContext();
        const F = ref(context, 'cat_F', 20);
        const x = ref(context, 'cat_x', 20);
        const direct = elaborateSurfaceOperationFromOperands(
            'functor.object',
            [F, x],
            at(20)
        );
        const legacy = elaborateSurfaceTerm(
            context,
            surfaceFapp0(
                surfaceReference('cat_F', at(20)),
                surfaceReference('cat_x', at(20)),
                at(20)
            )
        );
        assert.equal(kernelExpressionEquals(direct.term, legacy.term), true);
        assert.equal(coreTypeEquals(direct.type, legacy.type), true);
        assert.deepEqual(
            direct.recovered.map(slot => [slot.owner, slot.slot]),
            legacy.recovered.map(slot => [slot.owner, slot.slot])
        );
    });

    it('selects and emits ordinary object and capped-arrow action', () => {
        const context = buildContext();
        const builder = new CoreCategoricalScopedBuilder();
        const F = builder.fromElaborated(ref(context, 'cat_F', 30));
        const x = builder.fromElaborated(ref(context, 'cat_x', 30));
        const f = builder.fromElaborated(ref(context, 'cat_f', 31));

        const Fx = builder.compile(builder.apply(
            F,
            x,
            undefined,
            here(30, 'F at x')
        ));
        const Ff = builder.compile(builder.apply(
            F,
            f,
            undefined,
            here(31, 'F at f')
        ));
        assert.equal(Fx.term.tag, 'application');
        assert.equal(Ff.term.tag, 'application');
        assert.equal(
            (Fx.term as KernelApplication).owner,
            'functor-object'
        );
        assert.equal(
            (Ff.term as KernelApplication).owner,
            'functor-hom-capped'
        );
        assert.equal(Fx.type.tag, 'object');
        assert.equal(Ff.type.tag, 'hom');
        assert.deepEqual(
            (Ff.term as KernelApplication).arguments.map(
                argument => argument.plicity
            ),
            [
                'implicit',
                'implicit',
                'explicit',
                'implicit',
                'implicit',
                'explicit'
            ]
        );
    });

    it('selects higher object application rather than base arrow action', () => {
        const context = buildContext();
        const builder = new CoreCategoricalScopedBuilder();
        const H = builder.fromElaborated(ref(context, 'cat_H', 35));
        const f = builder.fromElaborated(ref(context, 'cat_f', 35));
        const Hf = builder.compile(builder.apply(
            H,
            f,
            undefined,
            here(35, 'H at the Hom-category object f')
        ));
        assert.equal(Hf.term.tag, 'application');
        assert.equal(
            (Hf.term as KernelApplication).owner,
            'functor-object'
        );
        assert.equal(Hf.type.tag, 'object');
    });

    it('selects a whole hom action without erasing a term', () => {
        const context = buildContext();
        const builder = new CoreCategoricalScopedBuilder();
        const F = builder.fromElaborated(ref(context, 'cat_F', 40));
        const x = builder.fromElaborated(ref(context, 'cat_x', 40));
        const y = builder.fromElaborated(ref(context, 'cat_y', 40));
        const A = ref(context, 'cat_A', 40).term;
        const boundary = builder.homBoundary(
            A,
            x,
            y,
            here(40, 'Hom A x y boundary')
        );
        const full = builder.apply(
            F,
            boundary,
            'whole-hom-action',
            here(40, 'whole F hom action')
        );
        const compiled = builder.compile(full);
        const inspected = builder.inspect(full);

        assert.equal(compiled.term.tag, 'application');
        assert.equal(
            (compiled.term as KernelApplication).owner,
            'functor-hom-full'
        );
        assert.equal(compiled.type.tag, 'functor');
        assert.equal(inspected.ir.tag, 'typed-application');
        if (inspected.ir.tag === 'typed-application') {
            assert.equal(inspected.ir.argument.tag, 'hom-boundary');
            assert.equal(inspected.ir.target, 'functor-hom-full');
        }
    });

    it('compiles a callback eta abstraction to the underlying functor', () => {
        const context = buildContext();
        const builder = new CoreCategoricalScopedBuilder();
        const FElaborated = ref(context, 'cat_F', 50);
        const F = builder.fromElaborated(FElaborated);
        const A = ref(context, 'cat_A', 50).term;
        const B = ref(context, 'cat_B', 50).term;
        let callbackCount = 0;

        const h = builder.categoricalLambda(
            'u',
            A,
            B,
            u => {
                callbackCount += 1;
                return builder.apply(
                    F,
                    u,
                    undefined,
                    here(50, 'F at categorical slot u')
                );
            },
            {
                provenance: here(50, 'functorial eta abstraction')
            }
        );
        const compiled = builder.compile(h);
        const inspected = builder.inspect(h);

        assert.equal(callbackCount, 1);
        assert.equal(
            kernelExpressionEquals(compiled.term, FElaborated.term),
            true
        );
        assert.equal(compiled.type.tag, 'functor');
        assert.equal(inspected.usage.length, 0);
        assert.equal(inspected.abstractions.length, 1);
        assert.equal(
            inspected.abstractions[0].rule,
            'categorical.eta'
        );
        const body = inspected.abstractions[0].body;
        assert.equal(body.tag, 'typed-application');
        if (
            body.tag === 'typed-application' &&
            body.argument.tag === 'slot-reference'
        ) {
            assert.equal(body.argument.index, 0);
            assert.equal(body.argument.hint, 'u');
            assert.equal(body.target, 'functor-object');
        } else {
            assert.fail('Expected eta body applied to slot index zero');
        }
        assertDeepFrozen(inspected);
    });

    it('applies an eta abstraction at both objects and arrows', () => {
        const context = buildContext();
        const builder = new CoreCategoricalScopedBuilder();
        const F = builder.fromElaborated(ref(context, 'cat_F', 60));
        const x = builder.fromElaborated(ref(context, 'cat_x', 60));
        const f = builder.fromElaborated(ref(context, 'cat_f', 61));
        const A = ref(context, 'cat_A', 60).term;
        const B = ref(context, 'cat_B', 60).term;
        const h = builder.categoricalLambda(
            'u',
            A,
            B,
            u => builder.apply(F, u),
            { provenance: here(60, 'eta h') }
        );

        const hx = builder.compile(builder.apply(h, x));
        const hf = builder.compile(builder.apply(h, f));
        assert.equal(
            (hx.term as KernelApplication).owner,
            'functor-object'
        );
        assert.equal(
            (hf.term as KernelApplication).owner,
            'functor-hom-capped'
        );
        assert.equal(
            kernelExpressionEquals(
                (hx.term as KernelApplication).arguments[2].value,
                ref(context, 'cat_F', 62).term
            ),
            true
        );
        assert.equal(
            kernelExpressionEquals(
                (hf.term as KernelApplication).arguments[2].value,
                ref(context, 'cat_F', 63).term
            ),
            true
        );
    });

    it('fails closed on classifier and whole-action mismatches', () => {
        const context = buildContext();
        const builder = new CoreCategoricalScopedBuilder();
        const F = builder.fromElaborated(ref(context, 'cat_F', 70));
        const c = builder.fromElaborated(ref(context, 'cat_c', 70));
        const x = builder.fromElaborated(ref(context, 'cat_x', 71));
        const y = builder.fromElaborated(ref(context, 'cat_y', 71));
        const B = ref(context, 'cat_B', 71).term;

        assertFrontendError(
            () => builder.apply(F, c),
            'CLASSIFIER_ARGUMENT_MISMATCH',
            /neither an object nor an arrow/
        );
        assertFrontendError(
            () => builder.apply(F, x, 'whole-hom-action'),
            'CLASSIFIER_ARGUMENT_MISMATCH',
            /concrete ordinary argument/
        );
        assertFrontendError(
            () => builder.apply(
                F,
                builder.homBoundary(B, x, y)
            ),
            'CLASSIFIER_ARGUMENT_MISMATCH'
        );
    });

    it('reports abstraction ambiguity instead of guessing a layer', () => {
        assertFrontendError(
            () => selectCoreCategoricalAbstraction({
                provenance: here(80, 'ambiguous lambda')
            }),
            'AMBIGUOUS_ABSTRACTION_LAYER'
        );
        assertFrontendError(
            () => selectCoreCategoricalAbstraction({
                requestedLayer: 'outer-lf',
                expectedClassifier: 'ordinary-functor',
                provenance: here(81, 'conflicting lambda')
            }),
            'CLASSIFIER_ARGUMENT_MISMATCH'
        );
        assert.equal(
            selectCoreCategoricalAbstraction({
                expectedClassifier: 'outer-lf-pi'
            }).id,
            'outer-lf-abstraction'
        );
        assert.equal(
            selectCoreCategoricalAbstraction({
                expectedClassifier: 'ordinary-functor'
            }).id,
            'ordinary-functorial-abstraction'
        );
    });

    it('rejects object-only, natural, and contrary ordinary binders', () => {
        const context = buildContext();
        const builder = new CoreCategoricalScopedBuilder();
        const A = ref(context, 'cat_A', 90).term;
        const B = ref(context, 'cat_B', 90).term;
        const F = builder.fromElaborated(ref(context, 'cat_F', 90));
        let callbackCount = 0;
        const body = (_: CoreCategoricalTerm) => {
            callbackCount += 1;
            return F;
        };

        assertFrontendError(
            () => builder.categoricalLambda(
                'u',
                A,
                B,
                body,
                { variation: 'object-only' }
            ),
            'OBJECT_ONLY_ARROW_USE'
        );
        assertFrontendError(
            () => builder.categoricalLambda(
                'u',
                A,
                B,
                body,
                { variation: 'natural' }
            ),
            'UNAVAILABLE_DISPLAYED_ACTION'
        );
        assertFrontendError(
            () => builder.categoricalLambda(
                'u',
                A,
                B,
                body,
                { polarity: 'contravariant' }
            ),
            'POLARITY_MISMATCH'
        );
        assert.equal(callbackCount, 0);
    });

    it('lowers constant and identity brackets through active owners', () => {
        const context = buildContext();
        const builder = new CoreCategoricalScopedBuilder();
        const A = ref(context, 'cat_A', 100).term;
        const B = ref(context, 'cat_B', 100).term;
        const b = builder.fromElaborated(ref(context, 'cat_b', 100));

        const constant = builder.categoricalLambda(
            'u',
            A,
            B,
            _u => b,
            { provenance: here(100, 'constant body') }
        );
        const identity = builder.categoricalLambda(
            'u',
            A,
            A,
            u => u,
            { provenance: here(101, 'identity body') }
        );
        const compiledConstant = builder.compile(constant);
        const compiledIdentity = builder.compile(identity);
        assert.equal(compiledConstant.term.tag, 'application');
        assert.equal(
            (compiledConstant.term as KernelApplication).owner,
            'functor-object'
        );
        assert.equal(compiledIdentity.term.tag, 'call');
        assert.equal(
            ((compiledIdentity.term as KernelCall).callee as {
                readonly name: string;
            }).name,
            coreCategoricalStructuralCoreName('identity-functor')
        );
        assert.deepEqual(
            builder.inspect(constant).abstractions[0]
                .structuralPrerequisites,
            ['constant-functor-abstraction']
        );
        assert.deepEqual(
            builder.inspect(identity).abstractions[0]
                .structuralPrerequisites,
            ['identity-functor']
        );
    });

    it('rejects foreign terms and escaped callback slots', () => {
        const context = buildContext();
        const first = new CoreCategoricalScopedBuilder();
        const second = new CoreCategoricalScopedBuilder();
        const F = first.fromElaborated(ref(context, 'cat_F', 110));
        const x = second.fromElaborated(ref(context, 'cat_x', 110));
        assertFrontendError(
            () => second.apply(F, x),
            'FOREIGN_TERM'
        );

        const A = ref(context, 'cat_A', 111).term;
        const B = ref(context, 'cat_B', 111).term;
        let escaped: CoreCategoricalTerm | undefined;
        first.categoricalLambda(
            'u',
            A,
            B,
            u => {
                escaped = u;
                return first.apply(F, u);
            }
        );
        assert.ok(escaped);
        assertFrontendError(
            () => first.apply(F, escaped as CoreCategoricalTerm),
            'ESCAPED_SLOT'
        );
    });

    it('preserves the frozen profile and root-only product boundary', () => {
        assert.equal(Object.keys(CORE_OWNER_SCHEMAS).length, 24);
        assert.equal(CORE_MVP_MANIFEST.revision, 'emdash-v3.2-mvp-1');
        const browserSource = readFileSync('src/v3_2/browser.ts', 'utf8');
        assert.doesNotMatch(
            browserSource,
            /categorical_surface|CoreCategoricalScopedBuilder/
        );
    });
});
