/** Native whole operations for presentation morphisms and their equations. */

import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    AlgebraOperation,
    AlgebraRuntimeSchema,
    algebraAlgorithmIdentity,
    defineAlgebraOperation,
    defineAlgebraRuntimeSchema
} from './algebra_engine';
import {
    AlgebraPolynomialModuleMap,
    AlgebraPresentedPolynomialModule
} from './algebra_polynomial_presentation';
import {
    AlgebraPolynomialChainMapSquare,
    AlgebraPolynomialPresentationMorphism,
    AlgebraPolynomialPresentationMorphismAgreement,
    algebraPolynomialChainMapSquare,
    algebraPolynomialPresentationMorphism,
    algebraPolynomialPresentationMorphismAgreement
} from './algebra_polynomial_presentation_morphism';
import {
    AlgebraReferenceImplementation,
    defineAlgebraReferenceImplementation
} from './algebra_reference_engine';
import {
    algebraPolynomialText
} from './algebra_polynomial';
import {
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';

export const ALGEBRA_POLYNOMIAL_PRESENTATION_MORPHISM_REFERENCE_PROFILE =
    Object.freeze({
        revision:
            'emdash-algebra-polynomial-presentation-morphism-reference-v1' as const,
        algorithmRevision:
            'typescript-presentation-membership-witness-v1' as const,
        wholeResults: true as const,
        nodeBuiltinDependency: false as const,
        performsIo: false as const
    });

export interface AlgebraPolynomialPresentationMorphismInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly source: AlgebraPresentedPolynomialModule<P, C, I>;
    readonly target: AlgebraPresentedPolynomialModule<P, C, I>;
    readonly map: AlgebraPolynomialModuleMap<P, C, I>;
}

export interface AlgebraPolynomialPresentationAgreementInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly source: AlgebraPresentedPolynomialModule<P, C, I>;
    readonly target: AlgebraPresentedPolynomialModule<P, C, I>;
    readonly left: AlgebraPolynomialModuleMap<P, C, I>;
    readonly right: AlgebraPolynomialModuleMap<P, C, I>;
}

export interface AlgebraPolynomialChainMapSquareInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly differentialSource: AlgebraPolynomialModuleMap<P, C, I>;
    readonly differentialTarget: AlgebraPolynomialModuleMap<P, C, I>;
    readonly componentPrevious: AlgebraPolynomialModuleMap<P, C, I>;
    readonly componentNow: AlgebraPolynomialModuleMap<P, C, I>;
}

export interface AlgebraPolynomialPresentationMorphismReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly morphismInputSchema: AlgebraRuntimeSchema<
        AlgebraPolynomialPresentationMorphismInput<P, C, I>
    >;
    readonly agreementInputSchema: AlgebraRuntimeSchema<
        AlgebraPolynomialPresentationAgreementInput<P, C, I>
    >;
    readonly chainSquareInputSchema: AlgebraRuntimeSchema<
        AlgebraPolynomialChainMapSquareInput<P, C, I>
    >;
    readonly morphism: AlgebraOperation<
        AlgebraPolynomialPresentationMorphismInput<P, C, I>,
        AlgebraPolynomialPresentationMorphism<P, C, I>
    >;
    readonly agreement: AlgebraOperation<
        AlgebraPolynomialPresentationAgreementInput<P, C, I>,
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>
    >;
    readonly chainSquare: AlgebraOperation<
        AlgebraPolynomialChainMapSquareInput<P, C, I>,
        AlgebraPolynomialChainMapSquare<P, C, I>
    >;
    readonly implementations: readonly AlgebraReferenceImplementation[];
}

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

const presentation = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: unknown, path: string): AlgebraPresentedPolynomialModule<P, C, I> => {
    if (
        !record(value) ||
        value.kind !== 'algebra-presented-polynomial-module' ||
        !record(value.ambient) ||
        !record(value.relations) ||
        !record(value.relationBasis)
    ) throw new Error(`presented polynomial module expected at ${path}`);
    return value as unknown as AlgebraPresentedPolynomialModule<P, C, I>;
};

const map = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    value: unknown,
    path: string
): AlgebraPolynomialModuleMap<P, C, I> => {
    if (
        !record(value) ||
        value.kind !== 'algebra-polynomial-module-map' ||
        !record(value.source) ||
        !record(value.target) ||
        !Array.isArray(value.columns)
    ) throw new Error(`polynomial module map expected at ${path}`);
    return value as unknown as AlgebraPolynomialModuleMap<P, C, I>;
};

const mapData = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    value: AlgebraPolynomialModuleMap<P, C, I>
) => Object.freeze({
    sourceRank: value.source.rank,
    targetRank: value.target.rank,
    columns: value.columns.map(column =>
        column.components.map(algebraPolynomialText)
    )
});

const membershipData = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    value: AlgebraPolynomialPresentationMorphism<P, C, I>['relationImages'][number]
) => Object.freeze({
    index: value.index,
    image: value.image.components.map(algebraPolynomialText),
    member: value.membership.member,
    coefficients: value.membership.coefficients.map(algebraPolynomialText),
    remainder: value.membership.remainder.components.map(algebraPolynomialText),
    steps: value.membership.reductionSteps
});

export const serializeAlgebraPolynomialPresentationMorphism = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialPresentationMorphism<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        kind: value.kind,
        map: mapData(value.map),
        relationImages: value.relationImages.map(membershipData),
        relationWitness: mapData(value.relationWitness),
        targetAfterWitness: mapData(value.targetAfterWitness),
        mapAfterSource: mapData(value.mapAfterSource),
        preservesRelations: value.preservesRelations,
        reductionSteps: value.reductionSteps
    }, 'polynomialPresentationMorphism');

export const serializeAlgebraPolynomialPresentationAgreement = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialPresentationMorphismAgreement<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        kind: value.kind,
        left: mapData(value.left),
        right: mapData(value.right),
        difference: mapData(value.difference),
        columns: value.columns.map(entry => Object.freeze({
            index: entry.index,
            difference: entry.difference.components.map(algebraPolynomialText),
            member: entry.membership.member,
            coefficients: entry.membership.coefficients.map(algebraPolynomialText),
            remainder: entry.membership.remainder.components.map(
                algebraPolynomialText
            ),
            steps: entry.membership.reductionSteps
        })),
        agreementWitness: mapData(value.agreementWitness),
        targetAfterWitness: mapData(value.targetAfterWitness),
        agrees: value.agrees,
        reductionSteps: value.reductionSteps
    }, 'polynomialPresentationMorphismAgreement');

export const serializeAlgebraPolynomialChainMapSquare = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialChainMapSquare<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        kind: value.kind,
        differentialSource: mapData(value.differentialSource),
        differentialTarget: mapData(value.differentialTarget),
        componentPrevious: mapData(value.componentPrevious),
        componentNow: mapData(value.componentNow),
        targetAfterComponent: mapData(value.targetAfterComponent),
        componentAfterSource: mapData(value.componentAfterSource),
        commutes: value.commutes
    }, 'polynomialChainMapSquare');

const wholeSchema = <T extends { readonly kind: string }>(
    id: string,
    kind: T['kind']
): AlgebraRuntimeSchema<T> => defineAlgebraRuntimeSchema({
    id,
    revision: ALGEBRA_POLYNOMIAL_PRESENTATION_MORPHISM_REFERENCE_PROFILE.revision,
    normalize(value: unknown, path: string) {
        if (!record(value) || value.kind !== kind) {
            throw new Error(`${kind} expected at ${path}`);
        }
        return value as unknown as T;
    }
});

const algorithm = (id: string) => algebraAlgorithmIdentity(
    `algebra.typescript-reference/${id}`,
    ALGEBRA_POLYNOMIAL_PRESENTATION_MORPHISM_REFERENCE_PROFILE.algorithmRevision
);

export function algebraPolynomialPresentationMorphismReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(): AlgebraPolynomialPresentationMorphismReferenceOperations<P, C, I> {
    const revision =
        ALGEBRA_POLYNOMIAL_PRESENTATION_MORPHISM_REFERENCE_PROFILE.revision;
    const morphismInputSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialPresentationMorphismInput<P, C, I>
    >({
        id: 'algebra.polynomial-presentation-morphism-input',
        revision,
        normalize(value: unknown, path: string) {
            if (!record(value)) throw new Error(`record expected at ${path}`);
            return Object.freeze({
                source: presentation<P, C, I>(value.source, `${path}.source`),
                target: presentation<P, C, I>(value.target, `${path}.target`),
                map: map<P, C, I>(value.map, `${path}.map`)
            });
        }
    });
    const agreementInputSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialPresentationAgreementInput<P, C, I>
    >({
        id: 'algebra.polynomial-presentation-agreement-input',
        revision,
        normalize(value: unknown, path: string) {
            if (!record(value)) throw new Error(`record expected at ${path}`);
            return Object.freeze({
                source: presentation<P, C, I>(value.source, `${path}.source`),
                target: presentation<P, C, I>(value.target, `${path}.target`),
                left: map<P, C, I>(value.left, `${path}.left`),
                right: map<P, C, I>(value.right, `${path}.right`)
            });
        }
    });
    const chainSquareInputSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialChainMapSquareInput<P, C, I>
    >({
        id: 'algebra.polynomial-chain-map-square-input',
        revision,
        normalize(value: unknown, path: string) {
            if (!record(value)) throw new Error(`record expected at ${path}`);
            return Object.freeze({
                differentialSource: map<P, C, I>(
                    value.differentialSource,
                    `${path}.differentialSource`
                ),
                differentialTarget: map<P, C, I>(
                    value.differentialTarget,
                    `${path}.differentialTarget`
                ),
                componentPrevious: map<P, C, I>(
                    value.componentPrevious,
                    `${path}.componentPrevious`
                ),
                componentNow: map<P, C, I>(
                    value.componentNow,
                    `${path}.componentNow`
                )
            });
        }
    });
    const morphism = defineAlgebraOperation({
        id: 'algebra.polynomial-presentation.morphism',
        revision,
        input: morphismInputSchema,
        output: wholeSchema<AlgebraPolynomialPresentationMorphism<P, C, I>>(
            'algebra.polynomial-presentation-morphism-result',
            'algebra-polynomial-presentation-morphism'
        )
    });
    const agreement = defineAlgebraOperation({
        id: 'algebra.polynomial-presentation.agreement',
        revision,
        input: agreementInputSchema,
        output: wholeSchema<
            AlgebraPolynomialPresentationMorphismAgreement<P, C, I>
        >(
            'algebra.polynomial-presentation-agreement-result',
            'algebra-polynomial-presentation-morphism-agreement'
        )
    });
    const chainSquare = defineAlgebraOperation({
        id: 'algebra.polynomial-presentation.chain-square',
        revision,
        input: chainSquareInputSchema,
        output: wholeSchema<AlgebraPolynomialChainMapSquare<P, C, I>>(
            'algebra.polynomial-chain-map-square-result',
            'algebra-polynomial-chain-map-square'
        )
    });
    const implementations = Object.freeze([
        defineAlgebraReferenceImplementation({
            operation: morphism,
            algorithm: algorithm(morphism.identity.id),
            execute: algebraPolynomialPresentationMorphism
        }),
        defineAlgebraReferenceImplementation({
            operation: agreement,
            algorithm: algorithm(agreement.identity.id),
            execute: algebraPolynomialPresentationMorphismAgreement
        }),
        defineAlgebraReferenceImplementation({
            operation: chainSquare,
            algorithm: algorithm(chainSquare.identity.id),
            execute: algebraPolynomialChainMapSquare
        })
    ]);
    return Object.freeze({
        morphismInputSchema,
        agreementInputSchema,
        chainSquareInputSchema,
        morphism,
        agreement,
        chainSquare,
        implementations
    });
}
