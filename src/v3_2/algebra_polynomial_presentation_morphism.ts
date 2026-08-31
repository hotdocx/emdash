/** Whole relation-witness and congruence computations for polynomial presentations. */

import {
    AlgebraElement,
    AlgebraParent,
    sameAlgebraParent
} from './algebra_parent';
import {
    AlgebraPolynomialFreeModule,
    AlgebraPolynomialModuleMembership,
    AlgebraPolynomialModuleVector,
    algebraPolynomialFreeModule,
    algebraPolynomialModuleEquals,
    algebraPolynomialModuleMembership,
    algebraPolynomialModuleSubtract,
    algebraPolynomialModuleVector
} from './algebra_polynomial_module';
import {
    AlgebraPolynomialModuleMap,
    AlgebraPresentedPolynomialModule,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleMapApply,
    algebraPolynomialModuleMapCompose
} from './algebra_polynomial_presentation';

export const ALGEBRA_POLYNOMIAL_PRESENTATION_MORPHISM_PROFILE = Object.freeze({
    revision: 'emdash-algebra-polynomial-presentation-morphism-v1' as const,
    relationOrder: 'original-presentation-generators' as const,
    relationEquation: 'target-relations-after-witness-equals-map-after-source' as const,
    agreementEquation: 'target-relations-after-witness-equals-left-minus-right' as const,
    wholeMemberships: true as const,
    quotientCarrier: false as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraPolynomialPresentationMorphismErrorCode =
    | 'FOREIGN_PRESENTATION_RING'
    | 'INVALID_MAP_ENDPOINTS'
    | 'INCOMPARABLE_MAPS';

export class AlgebraPolynomialPresentationMorphismError extends Error {
    constructor(
        public readonly code: AlgebraPolynomialPresentationMorphismErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraPolynomialPresentationMorphismError';
    }
}

const fail = (
    code: AlgebraPolynomialPresentationMorphismErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraPolynomialPresentationMorphismError(code, path, message);
};

const sameMapEndpoints = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomialModuleMap<P, C, I>,
    right: AlgebraPolynomialModuleMap<P, C, I>
): boolean => sameAlgebraParent(left.source, right.source) &&
    sameAlgebraParent(left.target, right.target);

export const algebraPolynomialModuleMapEquals = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomialModuleMap<P, C, I>,
    right: AlgebraPolynomialModuleMap<P, C, I>
): boolean => sameMapEndpoints(left, right) &&
    left.columns.length === right.columns.length &&
    left.columns.every((column, index) =>
        algebraPolynomialModuleEquals(column, right.columns[index])
    );

export function algebraPolynomialModuleMapSubtract<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomialModuleMap<P, C, I>,
    right: AlgebraPolynomialModuleMap<P, C, I>
): AlgebraPolynomialModuleMap<P, C, I> {
    if (!sameMapEndpoints(left, right)) {
        return fail(
            'INCOMPARABLE_MAPS',
            'polynomialModuleMapSubtract',
            'Map subtraction requires identical free-module endpoints'
        );
    }
    return algebraPolynomialModuleMap(
        left.source,
        left.target,
        left.columns.map((column, index) =>
            algebraPolynomialModuleSubtract(column, right.columns[index])
        )
    );
}

export const algebraPolynomialPresentationRelationModule = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(presentation: AlgebraPresentedPolynomialModule<P, C, I>):
    AlgebraPolynomialFreeModule<P, C, I> => algebraPolynomialFreeModule(
        presentation.ambient.ring,
        presentation.relations.generators.length,
        'term-over-position'
    );

export const algebraPolynomialPresentationRelationMap = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(presentation: AlgebraPresentedPolynomialModule<P, C, I>):
    AlgebraPolynomialModuleMap<P, C, I> => algebraPolynomialModuleMap(
        algebraPolynomialPresentationRelationModule(presentation),
        presentation.ambient,
        presentation.relations.generators
    );

const validateCandidateMap = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly source: AlgebraPresentedPolynomialModule<P, C, I>;
    readonly target: AlgebraPresentedPolynomialModule<P, C, I>;
    readonly map: AlgebraPolynomialModuleMap<P, C, I>;
}): void => {
    if (!sameAlgebraParent(
        input.source.ambient.ring,
        input.target.ambient.ring
    )) {
        return fail(
            'FOREIGN_PRESENTATION_RING',
            'presentationMorphism.target',
            'Fixed-ring presentation morphisms require one polynomial ring'
        );
    }
    if (
        !sameAlgebraParent(input.map.source, input.source.ambient) ||
        !sameAlgebraParent(input.map.target, input.target.ambient)
    ) {
        return fail(
            'INVALID_MAP_ENDPOINTS',
            'presentationMorphism.map',
            'Candidate map does not connect the selected presentations'
        );
    }
};

export interface AlgebraPolynomialPresentationRelationImage<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly index: number;
    readonly relation: AlgebraPolynomialModuleVector<P, C, I>;
    readonly image: AlgebraPolynomialModuleVector<P, C, I>;
    readonly membership: AlgebraPolynomialModuleMembership<P, C, I>;
}

export interface AlgebraPolynomialPresentationMorphism<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-presentation-morphism';
    readonly source: AlgebraPresentedPolynomialModule<P, C, I>;
    readonly target: AlgebraPresentedPolynomialModule<P, C, I>;
    readonly map: AlgebraPolynomialModuleMap<P, C, I>;
    readonly relationImages:
        readonly AlgebraPolynomialPresentationRelationImage<P, C, I>[];
    readonly relationWitness: AlgebraPolynomialModuleMap<P, C, I>;
    readonly targetAfterWitness: AlgebraPolynomialModuleMap<P, C, I>;
    readonly mapAfterSource: AlgebraPolynomialModuleMap<P, C, I>;
    readonly preservesRelations: boolean;
    readonly reductionSteps: number;
}

/**
 * Compute W columnwise from target-relation membership. Negative outputs keep
 * the candidate coefficient matrix and every nonzero remainder.
 */
export function algebraPolynomialPresentationMorphism<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly source: AlgebraPresentedPolynomialModule<P, C, I>;
    readonly target: AlgebraPresentedPolynomialModule<P, C, I>;
    readonly map: AlgebraPolynomialModuleMap<P, C, I>;
}): AlgebraPolynomialPresentationMorphism<P, C, I> {
    validateCandidateMap(input);
    const targetRelationModule =
        algebraPolynomialPresentationRelationModule(input.target);
    const relationImages = Object.freeze(input.source.relations.generators.map(
        (relation, index) => {
            const image = algebraPolynomialModuleMapApply(input.map, relation);
            return Object.freeze({
                index,
                relation,
                image,
                membership: algebraPolynomialModuleMembership(
                    image,
                    input.target.relationBasis
                )
            });
        }
    ));
    const relationWitness = algebraPolynomialModuleMap(
        algebraPolynomialPresentationRelationModule(input.source),
        targetRelationModule,
        relationImages.map(entry => algebraPolynomialModuleVector(
            targetRelationModule,
            entry.membership.coefficients
        ))
    );
    const targetAfterWitness = algebraPolynomialModuleMapCompose(
        algebraPolynomialPresentationRelationMap(input.target),
        relationWitness
    );
    const mapAfterSource = algebraPolynomialModuleMapCompose(
        input.map,
        algebraPolynomialPresentationRelationMap(input.source)
    );
    return Object.freeze({
        kind: 'algebra-polynomial-presentation-morphism',
        source: input.source,
        target: input.target,
        map: input.map,
        relationImages,
        relationWitness,
        targetAfterWitness,
        mapAfterSource,
        preservesRelations: relationImages.every(entry =>
            entry.membership.member
        ) && algebraPolynomialModuleMapEquals(
            targetAfterWitness,
            mapAfterSource
        ),
        reductionSteps: relationImages.reduce(
            (total, entry) => total + entry.membership.reductionSteps,
            0
        )
    });
}

export interface AlgebraPolynomialPresentationAgreementColumn<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly index: number;
    readonly difference: AlgebraPolynomialModuleVector<P, C, I>;
    readonly membership: AlgebraPolynomialModuleMembership<P, C, I>;
}

export interface AlgebraPolynomialPresentationMorphismAgreement<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-presentation-morphism-agreement';
    readonly source: AlgebraPresentedPolynomialModule<P, C, I>;
    readonly target: AlgebraPresentedPolynomialModule<P, C, I>;
    readonly left: AlgebraPolynomialModuleMap<P, C, I>;
    readonly right: AlgebraPolynomialModuleMap<P, C, I>;
    readonly difference: AlgebraPolynomialModuleMap<P, C, I>;
    readonly columns:
        readonly AlgebraPolynomialPresentationAgreementColumn<P, C, I>[];
    readonly agreementWitness: AlgebraPolynomialModuleMap<P, C, I>;
    readonly targetAfterWitness: AlgebraPolynomialModuleMap<P, C, I>;
    readonly agrees: boolean;
    readonly reductionSteps: number;
}

/** Compute H from target membership of every column of F-G. */
export function algebraPolynomialPresentationMorphismAgreement<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly source: AlgebraPresentedPolynomialModule<P, C, I>;
    readonly target: AlgebraPresentedPolynomialModule<P, C, I>;
    readonly left: AlgebraPolynomialModuleMap<P, C, I>;
    readonly right: AlgebraPolynomialModuleMap<P, C, I>;
}): AlgebraPolynomialPresentationMorphismAgreement<P, C, I> {
    validateCandidateMap({
        source: input.source,
        target: input.target,
        map: input.left
    });
    validateCandidateMap({
        source: input.source,
        target: input.target,
        map: input.right
    });
    const difference = algebraPolynomialModuleMapSubtract(
        input.left,
        input.right
    );
    const columns = Object.freeze(difference.columns.map(
        (column, index) => Object.freeze({
            index,
            difference: column,
            membership: algebraPolynomialModuleMembership(
                column,
                input.target.relationBasis
            )
        })
    ));
    const targetRelationModule =
        algebraPolynomialPresentationRelationModule(input.target);
    const agreementWitness = algebraPolynomialModuleMap(
        input.source.ambient,
        targetRelationModule,
        columns.map(entry => algebraPolynomialModuleVector(
            targetRelationModule,
            entry.membership.coefficients
        ))
    );
    const targetAfterWitness = algebraPolynomialModuleMapCompose(
        algebraPolynomialPresentationRelationMap(input.target),
        agreementWitness
    );
    return Object.freeze({
        kind: 'algebra-polynomial-presentation-morphism-agreement',
        source: input.source,
        target: input.target,
        left: input.left,
        right: input.right,
        difference,
        columns,
        agreementWitness,
        targetAfterWitness,
        agrees: columns.every(entry => entry.membership.member) &&
            algebraPolynomialModuleMapEquals(targetAfterWitness, difference),
        reductionSteps: columns.reduce(
            (total, entry) => total + entry.membership.reductionSteps,
            0
        )
    });
}

export interface AlgebraPolynomialChainMapSquare<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-chain-map-square';
    readonly differentialSource: AlgebraPolynomialModuleMap<P, C, I>;
    readonly differentialTarget: AlgebraPolynomialModuleMap<P, C, I>;
    readonly componentPrevious: AlgebraPolynomialModuleMap<P, C, I>;
    readonly componentNow: AlgebraPolynomialModuleMap<P, C, I>;
    readonly targetAfterComponent: AlgebraPolynomialModuleMap<P, C, I>;
    readonly componentAfterSource: AlgebraPolynomialModuleMap<P, C, I>;
    readonly commutes: boolean;
}

export function algebraPolynomialChainMapSquare<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly differentialSource: AlgebraPolynomialModuleMap<P, C, I>;
    readonly differentialTarget: AlgebraPolynomialModuleMap<P, C, I>;
    readonly componentPrevious: AlgebraPolynomialModuleMap<P, C, I>;
    readonly componentNow: AlgebraPolynomialModuleMap<P, C, I>;
}): AlgebraPolynomialChainMapSquare<P, C, I> {
    const targetAfterComponent = algebraPolynomialModuleMapCompose(
        input.differentialTarget,
        input.componentNow
    );
    const componentAfterSource = algebraPolynomialModuleMapCompose(
        input.componentPrevious,
        input.differentialSource
    );
    return Object.freeze({
        kind: 'algebra-polynomial-chain-map-square',
        ...input,
        targetAfterComponent,
        componentAfterSource,
        commutes: algebraPolynomialModuleMapEquals(
            targetAfterComponent,
            componentAfterSource
        )
    });
}
