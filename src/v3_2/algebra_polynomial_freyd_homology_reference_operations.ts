/** Native operations and canonical data for polynomial Freyd homology. */

import {
    AlgebraElement,
    AlgebraParent,
    sameAlgebraParent
} from './algebra_parent';
import {
    AlgebraOperation,
    AlgebraRuntimeSchema,
    algebraAlgorithmIdentity,
    defineAlgebraOperation,
    defineAlgebraRuntimeSchema
} from './algebra_engine';
import {
    AlgebraPolynomialFreydAbelianCategoryModel
} from './algebra_polynomial_freyd_abelian_category';
import {
    AlgebraPolynomialRing,
    algebraPolynomialText
} from './algebra_polynomial';
import {
    AlgebraPresentedPolynomialModule
} from './algebra_polynomial_presentation';
import {
    AlgebraPolynomialPresentationMorphism
} from './algebra_polynomial_presentation_morphism';
import {
    serializeAlgebraPolynomialPresentationAgreement,
    serializeAlgebraPolynomialPresentationMorphism
} from './algebra_polynomial_presentation_morphism_reference_operations';
import {
    AlgebraPolynomialFreydChainPair,
    AlgebraPolynomialFreydExactnessAt,
    AlgebraPolynomialFreydHomologyAt,
    algebraPolynomialFreydChainPair,
    algebraPolynomialFreydExactnessAt,
    algebraPolynomialFreydHomologyAt
} from './algebra_polynomial_freyd_homology';
import {
    AlgebraPolynomialFreydHomologyChainMap,
    AlgebraPolynomialFreydInducedHomologyMap,
    algebraPolynomialFreydHomologyChainMap,
    algebraPolynomialFreydInducedHomologyMap
} from './algebra_polynomial_freyd_functorial_homology';
import {
    AlgebraReferenceImplementation,
    defineAlgebraReferenceImplementation
} from './algebra_reference_engine';
import {
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';

export const ALGEBRA_POLYNOMIAL_FREYD_HOMOLOGY_REFERENCE_PROFILE =
    Object.freeze({
        revision: 'emdash-polynomial-freyd-homology-reference-v1' as const,
        algorithmRevision:
            'typescript-polynomial-freyd-homology-v1' as const,
        wholeResults: true as const,
        performsIo: false as const
    });

export interface AlgebraPolynomialFreydChainPairInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly dNext: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly d: AlgebraPolynomialPresentationMorphism<P, C, I>;
}

export interface AlgebraPolynomialFreydHomologyChainMapInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly source: AlgebraPolynomialFreydHomologyAt<P, C, I>;
    readonly target: AlgebraPolynomialFreydHomologyAt<P, C, I>;
    readonly fNext: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly f: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly fPrev: AlgebraPolynomialPresentationMorphism<P, C, I>;
}

export interface AlgebraPolynomialFreydHomologyReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly chainPairInputSchema:
        AlgebraRuntimeSchema<AlgebraPolynomialFreydChainPairInput<P, C, I>>;
    readonly chainPair: AlgebraOperation<
        AlgebraPolynomialFreydChainPairInput<P, C, I>,
        AlgebraPolynomialFreydChainPair<P, C, I>
    >;
    readonly homologyAt: AlgebraOperation<
        AlgebraPolynomialFreydChainPair<P, C, I>,
        AlgebraPolynomialFreydHomologyAt<P, C, I>
    >;
    readonly exactnessAt: AlgebraOperation<
        AlgebraPolynomialFreydHomologyAt<P, C, I>,
        AlgebraPolynomialFreydExactnessAt<P, C, I>
    >;
    readonly chainMapInputSchema:
        AlgebraRuntimeSchema<AlgebraPolynomialFreydHomologyChainMapInput<P, C, I>>;
    readonly chainMap: AlgebraOperation<
        AlgebraPolynomialFreydHomologyChainMapInput<P, C, I>,
        AlgebraPolynomialFreydHomologyChainMap<P, C, I>
    >;
    readonly inducedHomologyMap: AlgebraOperation<
        AlgebraPolynomialFreydHomologyChainMap<P, C, I>,
        AlgebraPolynomialFreydInducedHomologyMap<P, C, I>
    >;
    readonly implementations: readonly AlgebraReferenceImplementation[];
}

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

const presentationData = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPresentedPolynomialModule<P, C, I>) => Object.freeze({
    ambientRank: value.ambient.rank,
    relations: value.relations.generators.map(relation =>
        relation.components.map(algebraPolynomialText)
    )
});

export const serializeAlgebraPolynomialFreydChainPair = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydChainPair<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        kind: value.kind,
        dNext: serializeAlgebraPolynomialPresentationMorphism(value.dNext),
        d: serializeAlgebraPolynomialPresentationMorphism(value.d),
        composite:
            serializeAlgebraPolynomialPresentationMorphism(value.composite),
        zero: serializeAlgebraPolynomialPresentationMorphism(value.zero),
        chainAgreement:
            serializeAlgebraPolynomialPresentationAgreement(
                value.chainAgreement
            ),
        isChainPair: value.isChainPair
    }, 'polynomialFreydChainPair');

export const serializeAlgebraPolynomialFreydHomologyAt = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydHomologyAt<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        kind: value.kind,
        pair: serializeAlgebraPolynomialFreydChainPair(value.pair),
        cycleObject: presentationData(value.cycleObject),
        cycleEmbedding:
            serializeAlgebraPolynomialPresentationMorphism(
                value.cycleEmbedding
            ),
        cycleAnnihilation:
            serializeAlgebraPolynomialPresentationAgreement(
                value.cycles.annihilationAgreement
            ),
        boundary:
            serializeAlgebraPolynomialPresentationMorphism(
                value.boundaryMorphism
            ),
        boundaryReconstruction:
            serializeAlgebraPolynomialPresentationAgreement(
                value.boundaryReconstruction
            ),
        homologyObject: presentationData(value.homologyObject),
        homologyProjection:
            serializeAlgebraPolynomialPresentationMorphism(
                value.homologyProjection
            ),
        homologyAnnihilation:
            serializeAlgebraPolynomialPresentationAgreement(
                value.homologyAnnihilation
            )
    }, 'polynomialFreydHomologyAt');

export const serializeAlgebraPolynomialFreydExactnessAt = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydExactnessAt<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        kind: value.kind,
        homology: serializeAlgebraPolynomialFreydHomologyAt(value.homology),
        zeroProjection:
            serializeAlgebraPolynomialPresentationMorphism(value.zeroProjection),
        projectionZeroAgreement:
            serializeAlgebraPolynomialPresentationAgreement(
                value.projectionZeroAgreement
            ),
        exact: value.exact,
        epimorphism: value.epimorphism === undefined
            ? null
            : {
                epic: value.epimorphism.epic,
                cokernelZeroAgreement:
                    serializeAlgebraPolynomialPresentationAgreement(
                        value.epimorphism.cokernelZeroAgreement
                    )
            }
    }, 'polynomialFreydExactnessAt');

export const serializeAlgebraPolynomialFreydHomologyChainMap = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydHomologyChainMap<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        kind: value.kind,
        source: serializeAlgebraPolynomialFreydHomologyAt(value.source),
        target: serializeAlgebraPolynomialFreydHomologyAt(value.target),
        fNext: serializeAlgebraPolynomialPresentationMorphism(value.fNext),
        f: serializeAlgebraPolynomialPresentationMorphism(value.f),
        fPrev: serializeAlgebraPolynomialPresentationMorphism(value.fPrev),
        upperTargetAfterComponent:
            serializeAlgebraPolynomialPresentationMorphism(
                value.upperTargetAfterComponent
            ),
        upperComponentAfterSource:
            serializeAlgebraPolynomialPresentationMorphism(
                value.upperComponentAfterSource
            ),
        upperAgreement:
            serializeAlgebraPolynomialPresentationAgreement(value.upperAgreement),
        lowerTargetAfterComponent:
            serializeAlgebraPolynomialPresentationMorphism(
                value.lowerTargetAfterComponent
            ),
        lowerComponentAfterSource:
            serializeAlgebraPolynomialPresentationMorphism(
                value.lowerComponentAfterSource
            ),
        lowerAgreement:
            serializeAlgebraPolynomialPresentationAgreement(value.lowerAgreement),
        isChainMap: value.isChainMap
    }, 'polynomialFreydHomologyChainMap');

export const serializeAlgebraPolynomialFreydInducedHomologyMap = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydInducedHomologyMap<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        kind: value.kind,
        chainMap: serializeAlgebraPolynomialFreydHomologyChainMap(value.chainMap),
        cyclesTest:
            serializeAlgebraPolynomialPresentationMorphism(value.cyclesTest),
        cyclesMorphism:
            serializeAlgebraPolynomialPresentationMorphism(value.cyclesMorphism),
        cyclesReconstruction:
            serializeAlgebraPolynomialPresentationAgreement(
                value.cyclesReconstruction
            ),
        cyclesAfterBoundary:
            serializeAlgebraPolynomialPresentationMorphism(
                value.cyclesAfterBoundary
            ),
        boundaryAfterNext:
            serializeAlgebraPolynomialPresentationMorphism(value.boundaryAfterNext),
        boundaryCompatibility:
            serializeAlgebraPolynomialPresentationAgreement(
                value.boundaryCompatibility
            ),
        quotientTest:
            serializeAlgebraPolynomialPresentationMorphism(value.quotientTest),
        sourceBoundaryComposite:
            serializeAlgebraPolynomialPresentationMorphism(
                value.sourceBoundaryComposite
            ),
        sourceBoundaryZero:
            serializeAlgebraPolynomialPresentationMorphism(
                value.sourceBoundaryZero
            ),
        sourceBoundaryZeroAgreement:
            serializeAlgebraPolynomialPresentationAgreement(
                value.sourceBoundaryZeroAgreement
            ),
        homologyMap:
            serializeAlgebraPolynomialPresentationMorphism(value.homologyMap),
        homologyReconstruction:
            serializeAlgebraPolynomialPresentationAgreement(
                value.homologyReconstruction
            )
    }, 'polynomialFreydInducedHomologyMap');

const wholeSchema = <T extends { readonly kind: string }>(input: {
    readonly id: string;
    readonly kind: T['kind'];
    readonly ringOf: (value: T) => AlgebraParent;
    readonly ring: AlgebraParent;
}): AlgebraRuntimeSchema<T> => defineAlgebraRuntimeSchema({
    id: input.id,
    revision: ALGEBRA_POLYNOMIAL_FREYD_HOMOLOGY_REFERENCE_PROFILE.revision,
    normalize(value: unknown, path: string) {
        if (
            !record(value) ||
            value.kind !== input.kind ||
            !sameAlgebraParent(input.ringOf(value as T), input.ring)
        ) throw new Error(`${input.kind} for the selected ring expected at ${path}`);
        return value as T;
    }
});

export function algebraPolynomialFreydHomologyReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    base: AlgebraPolynomialFreydAbelianCategoryModel<P, C, I>,
    selectedRing: AlgebraPolynomialRing<P, C, I>
):
    AlgebraPolynomialFreydHomologyReferenceOperations<P, C, I> {
    const revision = ALGEBRA_POLYNOMIAL_FREYD_HOMOLOGY_REFERENCE_PROFILE.revision;
    const morphismSchema = base.category.morphismSchema;
    const chainPairInputSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialFreydChainPairInput<P, C, I>
    >({
        id: `algebra.polynomial-freyd-chain-pair-input/` +
            selectedRing.identity.id,
        revision,
        normalize(value: unknown, path: string) {
            if (!record(value)) {
                throw new Error(`Freyd chain-pair input expected at ${path}`);
            }
            return Object.freeze({
                dNext: morphismSchema.normalize(value.dNext, `${path}.dNext`),
                d: morphismSchema.normalize(value.d, `${path}.d`)
            });
        }
    });
    const pairSchema = wholeSchema<AlgebraPolynomialFreydChainPair<P, C, I>>({
        id: `algebra.polynomial-freyd-chain-pair-result/` +
            selectedRing.identity.id,
        kind: 'algebra-polynomial-freyd-chain-pair',
        ring: selectedRing,
        ringOf: value => value.dNext.source.ambient.ring
    });
    const homologySchema = wholeSchema<
        AlgebraPolynomialFreydHomologyAt<P, C, I>
    >({
        id: `algebra.polynomial-freyd-homology-result/` +
            selectedRing.identity.id,
        kind: 'algebra-polynomial-freyd-homology-at',
        ring: selectedRing,
        ringOf: value => value.pair.dNext.source.ambient.ring
    });
    const exactnessSchema = wholeSchema<
        AlgebraPolynomialFreydExactnessAt<P, C, I>
    >({
        id: `algebra.polynomial-freyd-exactness-result/` +
            selectedRing.identity.id,
        kind: 'algebra-polynomial-freyd-exactness-at',
        ring: selectedRing,
        ringOf: value => value.homology.pair.dNext.source.ambient.ring
    });
    const chainMapInputSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialFreydHomologyChainMapInput<P, C, I>
    >({
        id: `algebra.polynomial-freyd-homology-chain-map-input/` +
            selectedRing.identity.id,
        revision,
        normalize(value: unknown, path: string) {
            if (!record(value)) {
                throw new Error(`Freyd homology chain-map input expected at ${path}`);
            }
            return Object.freeze({
                source: homologySchema.normalize(value.source, `${path}.source`),
                target: homologySchema.normalize(value.target, `${path}.target`),
                fNext: morphismSchema.normalize(value.fNext, `${path}.fNext`),
                f: morphismSchema.normalize(value.f, `${path}.f`),
                fPrev: morphismSchema.normalize(value.fPrev, `${path}.fPrev`)
            });
        }
    });
    const chainMapSchema = wholeSchema<
        AlgebraPolynomialFreydHomologyChainMap<P, C, I>
    >({
        id: `algebra.polynomial-freyd-homology-chain-map-result/` +
            selectedRing.identity.id,
        kind: 'algebra-polynomial-freyd-homology-chain-map',
        ring: selectedRing,
        ringOf: value => value.source.pair.dNext.source.ambient.ring
    });
    const inducedMapSchema = wholeSchema<
        AlgebraPolynomialFreydInducedHomologyMap<P, C, I>
    >({
        id: `algebra.polynomial-freyd-induced-homology-map-result/` +
            selectedRing.identity.id,
        kind: 'algebra-polynomial-freyd-induced-homology-map',
        ring: selectedRing,
        ringOf: value => value.chainMap.source.pair.dNext.source.ambient.ring
    });
    const prefix = `algebra.polynomial-freyd-homology/` +
        selectedRing.identity.id;
    const chainPair = defineAlgebraOperation({
        id: `${prefix}/chain-pair`,
        revision,
        input: chainPairInputSchema,
        output: pairSchema
    });
    const homologyAt = defineAlgebraOperation({
        id: `${prefix}/homology-at`,
        revision,
        input: pairSchema,
        output: homologySchema
    });
    const exactnessAt = defineAlgebraOperation({
        id: `${prefix}/exactness-at`,
        revision,
        input: homologySchema,
        output: exactnessSchema
    });
    const chainMap = defineAlgebraOperation({
        id: `${prefix}/chain-map`,
        revision,
        input: chainMapInputSchema,
        output: chainMapSchema
    });
    const inducedHomologyMap = defineAlgebraOperation({
        id: `${prefix}/induced-map`,
        revision,
        input: chainMapSchema,
        output: inducedMapSchema
    });
    const algorithm = (operation: AlgebraOperation<unknown, unknown>) =>
        algebraAlgorithmIdentity(
            `algebra.typescript-reference/${operation.identity.id}`,
            ALGEBRA_POLYNOMIAL_FREYD_HOMOLOGY_REFERENCE_PROFILE
                .algorithmRevision
        );
    const implementation = <Input, Output>(
        operation: AlgebraOperation<Input, Output>,
        execute: (input: Input) => Output
    ): AlgebraReferenceImplementation => defineAlgebraReferenceImplementation({
        operation,
        algorithm: algorithm(operation as AlgebraOperation<unknown, unknown>),
        execute
    });
    return Object.freeze({
        chainPairInputSchema,
        chainPair,
        homologyAt,
        exactnessAt,
        chainMapInputSchema,
        chainMap,
        inducedHomologyMap,
        implementations: Object.freeze([
            implementation(chainPair, input =>
                algebraPolynomialFreydChainPair(input.dNext, input.d)),
            implementation(homologyAt, algebraPolynomialFreydHomologyAt),
            implementation(exactnessAt, algebraPolynomialFreydExactnessAt),
            implementation(chainMap, algebraPolynomialFreydHomologyChainMap),
            implementation(inducedHomologyMap,
                algebraPolynomialFreydInducedHomologyMap)
        ])
    });
}
