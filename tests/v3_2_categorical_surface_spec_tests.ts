/**
 * Focused executable checks for the USABILITY-1A categorical surface RFC.
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
    CORE_CATEGORICAL_SURFACE_SPECIFICATION,
    CORE_DIRECTED_1C_REVIEW,
    CORE_MVP_MANIFEST,
    CORE_OWNER_SCHEMAS,
    CoreCategoricalSurfaceError,
    LAMBDAPI_V32_CATEGORICAL_SURFACE_BINDINGS,
    LAMBDAPI_V32_OWNER_BINDINGS,
    selectCoreCategoricalApplication,
    validateCoreCategoricalSurfaceSpecification
} from '../src/v3_2';

const clone = <T>(value: T): any =>
    JSON.parse(JSON.stringify(value));

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(assertDeepFrozen);
};

const assertSelectionError = (
    query: Parameters<typeof selectCoreCategoricalApplication>[0],
    code: CoreCategoricalSurfaceError['code']
): void => {
    assert.throws(
        () => selectCoreCategoricalApplication(query),
        error =>
            error instanceof CoreCategoricalSurfaceError &&
            error.code === code
    );
};

describe('TypeScript v3.2 USABILITY-1A categorical surface spec', () => {
    it('separates outer LF and categorical abstraction with five axes', () => {
        const specification = CORE_CATEGORICAL_SURFACE_SPECIFICATION;
        assert.equal(specification.revision, 'USABILITY-1A');
        assert.equal(
            specification.architectureDecision,
            'outer-lf-and-categorical-abstraction-are-distinct'
        );
        assert.deepEqual(
            specification.axes.map(axis => [
                axis.axis,
                axis.values
            ]),
            [
                ['plicity', ['explicit', 'implicit']],
                [
                    'variation',
                    ['functorial', 'natural', 'object-only']
                ],
                ['polarity', ['covariant', 'contravariant']],
                [
                    'cell-level',
                    ['object', 'arrow', 'transfor', 'higher']
                ],
                ['dependency', ['ordinary', 'displayed']]
            ]
        );
        assert.deepEqual(
            specification.abstractions.map(abstraction => [
                abstraction.id,
                abstraction.layer,
                abstraction.lowering,
                abstraction.implementationStage
            ]),
            [
                [
                    'outer-lf-abstraction',
                    'outer-lf',
                    'kernel-lambda',
                    'available'
                ],
                [
                    'ordinary-functorial-abstraction',
                    'categorical',
                    'categorical-contextual-ir',
                    'USABILITY-1B'
                ],
                [
                    'natural-indexed-abstraction',
                    'categorical',
                    'categorical-contextual-ir',
                    'USABILITY-2A'
                ],
                [
                    'object-only-abstraction',
                    'categorical',
                    'restricted-object-family',
                    'notation-and-capability-review'
                ]
            ]
        );
    });

    it('selects exact ordinary object, arrow, and whole-action owners', () => {
        const object = selectCoreCategoricalApplication({
            layer: 'categorical',
            subjectClassifier: 'ordinary-functor',
            subjectForm: 'term',
            argumentDimension: 'object',
            dependency: 'ordinary'
        });
        const arrow = selectCoreCategoricalApplication({
            layer: 'categorical',
            subjectClassifier: 'ordinary-functor',
            subjectForm: 'term',
            argumentDimension: 'arrow',
            dependency: 'ordinary'
        });
        const full = selectCoreCategoricalApplication({
            layer: 'categorical',
            subjectClassifier: 'ordinary-functor',
            subjectForm: 'term',
            argumentDimension: 'hom-boundary',
            expectedShape: 'whole-hom-action',
            dependency: 'ordinary'
        });
        assert.deepEqual(
            [object.target, arrow.target, full.target],
            [
                'functor-object',
                'functor-hom-capped',
                'functor-hom-full'
            ]
        );
        assert.deepEqual(
            [object.target, arrow.target, full.target].map(
                target =>
                    LAMBDAPI_V32_OWNER_BINDINGS[
                        target as keyof typeof LAMBDAPI_V32_OWNER_BINDINGS
                    ].serializedName
            ),
            ['fapp0', 'fapp1_fapp0', 'fapp1_func']
        );
    });

    it('never erases a concrete transfor to request a full evaluator', () => {
        const family = selectCoreCategoricalApplication({
            layer: 'categorical',
            subjectClassifier: 'ordinary-transfor',
            subjectForm: 'classifier-family',
            argumentDimension: 'object',
            dependency: 'ordinary'
        });
        const component = selectCoreCategoricalApplication({
            layer: 'categorical',
            subjectClassifier: 'ordinary-transfor',
            subjectForm: 'term',
            argumentDimension: 'object',
            dependency: 'ordinary'
        });
        assert.deepEqual(
            [
                family.target,
                family.consumesSubjectTerm,
                component.target,
                component.consumesSubjectTerm
            ],
            [
                'transfor-component-full',
                false,
                'transfor-component-capped',
                true
            ]
        );
    });

    it('reuses reviewed section evaluation and gates section arrow action', () => {
        const sectionObject = selectCoreCategoricalApplication({
            layer: 'categorical',
            subjectClassifier: 'dependent-section',
            subjectForm: 'term',
            argumentDimension: 'object',
            dependency: 'displayed'
        });
        assert.equal(sectionObject.target, 'section-object-evaluation');
        assert.equal(
            CORE_DIRECTED_1C_REVIEW.authorization.ownerIds.includes(
                'section-object-evaluation'
            ),
            true
        );
        assertSelectionError(
            {
                layer: 'categorical',
                subjectClassifier: 'dependent-section',
                subjectForm: 'term',
                argumentDimension: 'arrow',
                dependency: 'displayed'
            },
            'UNAVAILABLE_DEPENDENT_ACTION'
        );
    });

    it('fails closed for displayed ambiguity, gaps, and reserved naturality', () => {
        assertSelectionError(
            {
                layer: 'categorical',
                subjectClassifier: 'displayed-functor',
                subjectForm: 'term',
                argumentDimension: 'arrow',
                dependency: 'displayed'
            },
            'MISSING_EXPECTED_ACTION_SHAPE'
        );
        assertSelectionError(
            {
                layer: 'categorical',
                subjectClassifier: 'displayed-functor',
                subjectForm: 'term',
                argumentDimension: 'arrow',
                expectedShape: 'transport-functor',
                dependency: 'displayed'
            },
            'UNAVAILABLE_DISPLAYED_ACTION'
        );
        assertSelectionError(
            {
                layer: 'categorical',
                subjectClassifier: 'displayed-functor',
                subjectForm: 'term',
                argumentDimension: 'arrow',
                expectedShape: 'whole-laxity-transfor',
                dependency: 'displayed'
            },
            'UNAVAILABLE_DISPLAYED_ACTION'
        );
        assertSelectionError(
            {
                layer: 'categorical',
                subjectClassifier: 'ordinary-transfor',
                subjectForm: 'term',
                argumentDimension: 'arrow',
                dependency: 'ordinary'
            },
            'RESERVED_NATURALITY_ACTION'
        );
    });

    it('records exact ordinary bracket-abstraction prerequisites', () => {
        assert.deepEqual(
            CORE_CATEGORICAL_SURFACE_SPECIFICATION
                .structuralPrerequisites.map(entry => entry.target),
            [
                'identity-functor',
                'constant-functor-abstraction',
                'exchange-functor-abstraction',
                'diagonal-functor-abstraction',
                'product-category',
                'product-left-projection',
                'product-right-projection',
                'product-pair',
                'product-map',
                'evaluation-functor',
                'functor-composition',
                'curry-package',
                'uncurry-package'
            ]
        );
        for (
            const prerequisite of
                CORE_CATEGORICAL_SURFACE_SPECIFICATION
                    .structuralPrerequisites
        ) {
            assert.equal(
                prerequisite.target in CORE_OWNER_SCHEMAS,
                false
            );
            assert.equal(
                prerequisite.implementationStatus,
                'active-kernel-untransferred'
            );
        }
    });

    it('relocates exact active names and verifies source evidence', () => {
        const source = readFileSync('emdash2/emdash3_2.lp', 'utf8');
        for (
            const binding of
                LAMBDAPI_V32_CATEGORICAL_SURFACE_BINDINGS
        ) {
            assert.equal(
                source.includes(binding.provenance.sourceFragment),
                true,
                binding.target
            );
        }
        const semantic =
            JSON.stringify(CORE_CATEGORICAL_SURFACE_SPECIFICATION);
        assert.doesNotMatch(
            semantic,
            /piapp|fapp[01]|tapp[01]|tdapp|Fibre_func|emdash2\//
        );
    });

    it('keeps notation, frozen MVP, and browser scope unchanged', () => {
        assert.deepEqual(
            CORE_CATEGORICAL_SURFACE_SPECIFICATION.notationPolicy,
            {
                canonicalNaturalBinder: ':^n',
                functorialBinder:
                    'internal-typescript-mode-final-notation-unsettled',
                objectOnlyBinder:
                    'internal-typescript-mode-final-notation-unsettled'
            }
        );
        assert.equal(CORE_MVP_MANIFEST.revision, 'emdash-v3.2-mvp-1');
        assert.equal(Object.keys(CORE_OWNER_SCHEMAS).length, 24);
        const browserSource = readFileSync('src/v3_2/browser.ts', 'utf8');
        assert.doesNotMatch(
            browserSource,
            /categorical_surface_spec|CORE_CATEGORICAL_SURFACE/
        );
    });

    it('is deeply frozen and validates exact authority boundaries', () => {
        assertDeepFrozen(CORE_CATEGORICAL_SURFACE_SPECIFICATION);
        assertDeepFrozen(LAMBDAPI_V32_CATEGORICAL_SURFACE_BINDINGS);
        assert.doesNotThrow(
            () => validateCoreCategoricalSurfaceSpecification()
        );
    });

    it('rejects specification and backend-evidence drift', () => {
        const duplicate = clone(
            CORE_CATEGORICAL_SURFACE_SPECIFICATION
        );
        duplicate.applications.push(duplicate.applications[0]);
        assert.throws(
            () => validateCoreCategoricalSurfaceSpecification(duplicate),
            error =>
                error instanceof CoreCategoricalSurfaceError &&
                error.code === 'INVALID_SPECIFICATION'
        );

        const changed = clone(
            CORE_CATEGORICAL_SURFACE_SPECIFICATION
        );
        changed.applications[0].rule = 'changed';
        assert.throws(
            () => validateCoreCategoricalSurfaceSpecification(changed),
            error =>
                error instanceof CoreCategoricalSurfaceError &&
                error.code === 'SPECIFICATION_DRIFT'
        );

        const bindings = clone(
            LAMBDAPI_V32_CATEGORICAL_SURFACE_BINDINGS
        );
        bindings[0].serializedName = '';
        assert.throws(
            () => validateCoreCategoricalSurfaceSpecification(
                CORE_CATEGORICAL_SURFACE_SPECIFICATION,
                bindings
            ),
            error =>
                error instanceof CoreCategoricalSurfaceError &&
                error.code === 'INVALID_BACKEND_BINDING'
        );
    });

    it('reports classifier mismatch instead of guessing a layer', () => {
        assertSelectionError(
            {
                layer: 'outer-lf',
                subjectClassifier: 'ordinary-functor',
                subjectForm: 'term',
                argumentDimension: 'object',
                dependency: 'ordinary'
            },
            'CLASSIFIER_ARGUMENT_MISMATCH'
        );
        assert.equal(
            CORE_CATEGORICAL_SURFACE_SPECIFICATION.diagnostics.some(
                diagnostic =>
                    diagnostic.code === 'AMBIGUOUS_ABSTRACTION_LAYER'
            ),
            true
        );
        assert.equal(
            CORE_CATEGORICAL_SURFACE_SPECIFICATION.diagnostics.some(
                diagnostic =>
                    diagnostic.code === 'OBJECT_ONLY_ARROW_USE'
            ),
            true
        );
    });
});
