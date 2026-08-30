/** Bounded chain complexes and whole homology for presented field modules. */

import {
    AlgebraElement,
    AlgebraParent,
    sameAlgebraParent
} from './algebra_parent';
import {
    AlgebraFieldDomain
} from './algebra_exact';
import {
    AlgebraModuleCokernel,
    AlgebraModuleKernel,
    AlgebraModuleMorphism,
    AlgebraPresentedModule,
    algebraFreeModule,
    algebraModuleCokernelColift,
    algebraModuleCokernel,
    algebraModuleCompose,
    algebraModuleIdentity,
    algebraModuleKernel,
    algebraModuleKernelLift,
    algebraModuleLiftAlongEpimorphism,
    algebraModuleLiftAlongMonomorphism,
    algebraModuleMorphismIsZero,
    algebraModuleMorphismEquivalent,
    algebraModuleZeroMorphism,
    algebraPresentedModuleEquals
} from './algebra_module';

export const ALGEBRA_HOMOLOGICAL_PROFILE = Object.freeze({
    revision: 'emdash-algebra-homological-v1' as const,
    grading: 'bounded-consecutive-safe-integers' as const,
    differentialOrientation: 'd_n-from-C_n-to-C_n-minus-1' as const,
    homologyConstruction: 'cokernel-of-boundary-lift-into-kernel' as const,
    quotientAwareChainCondition: true as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraHomologicalErrorCode =
    | 'INVALID_COMPLEX'
    | 'DUPLICATE_DEGREE'
    | 'NON_CONSECUTIVE_DEGREES'
    | 'INVALID_DIFFERENTIAL'
    | 'CHAIN_CONDITION_FAILED'
    | 'INVALID_CHAIN_MAP'
    | 'CHAIN_MAP_CONDITION_FAILED'
    | 'INVALID_SHORT_EXACT_SEQUENCE'
    | 'SHORT_EXACTNESS_FAILED'
    | 'DEGREE_OUT_OF_RANGE';

export class AlgebraHomologicalError extends Error {
    constructor(
        public readonly code: AlgebraHomologicalErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraHomologicalError';
    }
}

const fail = (
    code: AlgebraHomologicalErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraHomologicalError(code, path, message);
};

const degree = (value: number, path: string): number => {
    if (Number.isSafeInteger(value)) return value;
    return fail(
        'INVALID_COMPLEX',
        path,
        'A chain-complex degree must be a safe integer'
    );
};

export interface AlgebraModuleComplexTerm<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly degree: number;
    readonly object: AlgebraPresentedModule<P, C, I>;
}

export interface AlgebraModuleComplexDifferential<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    /** The differential d_degree: C_degree -> C_(degree - 1). */
    readonly degree: number;
    readonly morphism: AlgebraModuleMorphism<P, C, I>;
}

export interface AlgebraModuleChainComplex<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-module-chain-complex';
    readonly field: AlgebraFieldDomain<P, C, I>;
    readonly minimumDegree: number;
    readonly maximumDegree: number;
    readonly terms: readonly AlgebraModuleComplexTerm<P, C, I>[];
    readonly differentials: readonly AlgebraModuleComplexDifferential<P, C, I>[];
}

export function algebraModuleChainComplex<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    field: AlgebraFieldDomain<P, C, I>,
    termInput: readonly AlgebraModuleComplexTerm<P, C, I>[],
    differentialInput: readonly AlgebraModuleComplexDifferential<P, C, I>[]
): AlgebraModuleChainComplex<P, C, I> {
    if (termInput.length === 0) {
        return fail(
            'INVALID_COMPLEX',
            'complex.terms',
            'A bounded chain complex requires at least one term'
        );
    }
    const terms = [...termInput]
        .map((term, index) => Object.freeze({
            degree: degree(term.degree, `complex.terms[${index}].degree`),
            object: term.object
        }))
        .sort((left, right) => left.degree - right.degree);
    terms.forEach((term, index) => {
        if (!sameAlgebraParent(term.object.field.parent, field.parent)) {
            fail(
                'INVALID_COMPLEX',
                `complex.terms[${index}].object`,
                'Every complex term must use the selected field'
            );
        }
        if (index > 0 && term.degree === terms[index - 1].degree) {
            fail(
                'DUPLICATE_DEGREE',
                `complex.terms[${index}].degree`,
                `Degree ${term.degree} occurs more than once`
            );
        }
        if (index > 0 && term.degree !== terms[index - 1].degree + 1) {
            fail(
                'NON_CONSECUTIVE_DEGREES',
                `complex.terms[${index}].degree`,
                'The first bounded profile requires consecutive terms'
            );
        }
    });
    if (differentialInput.length !== terms.length - 1) {
        return fail(
            'INVALID_DIFFERENTIAL',
            'complex.differentials',
            'A differential is required between every consecutive pair'
        );
    }
    const differentials = [...differentialInput]
        .map((entry, index) => Object.freeze({
            degree: degree(
                entry.degree,
                `complex.differentials[${index}].degree`
            ),
            morphism: entry.morphism
        }))
        .sort((left, right) => left.degree - right.degree);
    differentials.forEach((entry, index) => {
        const expectedDegree = terms[0].degree + index + 1;
        const source = terms[index + 1].object;
        const target = terms[index].object;
        if (
            entry.degree !== expectedDegree ||
            !algebraPresentedModuleEquals(entry.morphism.source, source) ||
            !algebraPresentedModuleEquals(entry.morphism.target, target)
        ) {
            fail(
                'INVALID_DIFFERENTIAL',
                `complex.differentials[${index}]`,
                `Expected d_${expectedDegree}: C_${expectedDegree} -> ` +
                    `C_${expectedDegree - 1}`
            );
        }
    });
    for (let index = 1; index < differentials.length; index++) {
        const composite = algebraModuleCompose(
            differentials[index - 1].morphism,
            differentials[index].morphism
        );
        if (!algebraModuleMorphismIsZero(composite)) {
            fail(
                'CHAIN_CONDITION_FAILED',
                `complex.differentials[${index}]`,
                `d_${differentials[index - 1].degree} * ` +
                    `d_${differentials[index].degree} is not zero`
            );
        }
    }
    return Object.freeze({
        kind: 'algebra-module-chain-complex',
        field,
        minimumDegree: terms[0].degree,
        maximumDegree: terms[terms.length - 1].degree,
        terms: Object.freeze(terms),
        differentials: Object.freeze(differentials)
    });
}

export function algebraModuleChainComplexTerm<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    complex: AlgebraModuleChainComplex<P, C, I>,
    degreeInput: number
): AlgebraPresentedModule<P, C, I> {
    const requested = degree(degreeInput, 'complex.term.degree');
    if (
        requested < complex.minimumDegree ||
        requested > complex.maximumDegree
    ) {
        return fail(
            'DEGREE_OUT_OF_RANGE',
            'complex.term.degree',
            `Degree ${requested} is outside the bounded complex`
        );
    }
    return complex.terms[requested - complex.minimumDegree].object;
}

export function algebraModuleChainComplexDifferential<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    complex: AlgebraModuleChainComplex<P, C, I>,
    degreeInput: number
): AlgebraModuleMorphism<P, C, I> {
    const requested = degree(degreeInput, 'complex.differential.degree');
    if (
        requested <= complex.minimumDegree ||
        requested > complex.maximumDegree
    ) {
        return fail(
            'DEGREE_OUT_OF_RANGE',
            'complex.differential.degree',
            `The bounded complex has no d_${requested}`
        );
    }
    return complex.differentials[
        requested - complex.minimumDegree - 1
    ].morphism;
}

export const algebraModuleChainComplexEquals = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraModuleChainComplex<P, C, I>,
    right: AlgebraModuleChainComplex<P, C, I>
): boolean =>
    left.minimumDegree === right.minimumDegree &&
    left.maximumDegree === right.maximumDegree &&
    sameAlgebraParent(left.field.parent, right.field.parent) &&
    left.terms.every((term, index) => algebraPresentedModuleEquals(
        term.object,
        right.terms[index].object
    )) &&
    left.differentials.every((entry, index) =>
        algebraModuleMorphismEquivalent(
            entry.morphism,
            right.differentials[index].morphism
        )
    );

export interface AlgebraModuleChainMapComponent<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly degree: number;
    readonly morphism: AlgebraModuleMorphism<P, C, I>;
}

export interface AlgebraModuleChainMap<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-module-chain-map';
    readonly source: AlgebraModuleChainComplex<P, C, I>;
    readonly target: AlgebraModuleChainComplex<P, C, I>;
    readonly components: readonly AlgebraModuleChainMapComponent<P, C, I>[];
}

export function algebraModuleChainMap<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    source: AlgebraModuleChainComplex<P, C, I>,
    target: AlgebraModuleChainComplex<P, C, I>,
    componentInput: readonly AlgebraModuleChainMapComponent<P, C, I>[]
): AlgebraModuleChainMap<P, C, I> {
    if (
        source.minimumDegree !== target.minimumDegree ||
        source.maximumDegree !== target.maximumDegree ||
        !sameAlgebraParent(source.field.parent, target.field.parent) ||
        componentInput.length !== source.terms.length
    ) {
        return fail(
            'INVALID_CHAIN_MAP',
            'chainMap',
            'The first chain-map profile requires equal bounded degree ranges'
        );
    }
    const components = [...componentInput]
        .map((component, index) => Object.freeze({
            degree: degree(
                component.degree,
                `chainMap.components[${index}].degree`
            ),
            morphism: component.morphism
        }))
        .sort((left, right) => left.degree - right.degree);
    components.forEach((component, index) => {
        const expectedDegree = source.minimumDegree + index;
        if (
            component.degree !== expectedDegree ||
            !algebraPresentedModuleEquals(
                component.morphism.source,
                source.terms[index].object
            ) ||
            !algebraPresentedModuleEquals(
                component.morphism.target,
                target.terms[index].object
            )
        ) {
            fail(
                'INVALID_CHAIN_MAP',
                `chainMap.components[${index}]`,
                `Expected a component C_${expectedDegree} -> D_` +
                    `${expectedDegree}`
            );
        }
    });
    for (let index = 1; index < components.length; index++) {
        const targetAfterComponent = algebraModuleCompose(
            target.differentials[index - 1].morphism,
            components[index].morphism
        );
        const componentAfterSource = algebraModuleCompose(
            components[index - 1].morphism,
            source.differentials[index - 1].morphism
        );
        if (!algebraModuleMorphismEquivalent(
            targetAfterComponent,
            componentAfterSource
        )) {
            fail(
                'CHAIN_MAP_CONDITION_FAILED',
                `chainMap.components[${index}]`,
                `The component in degree ${components[index].degree} ` +
                    'does not commute with the differential'
            );
        }
    }
    return Object.freeze({
        kind: 'algebra-module-chain-map',
        source,
        target,
        components: Object.freeze(components)
    });
}

export function algebraModuleChainMapComponentAt<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    chainMap: AlgebraModuleChainMap<P, C, I>,
    degreeInput: number
): AlgebraModuleMorphism<P, C, I> {
    const requested = degree(degreeInput, 'chainMap.component.degree');
    if (
        requested < chainMap.source.minimumDegree ||
        requested > chainMap.source.maximumDegree
    ) {
        return fail(
            'DEGREE_OUT_OF_RANGE',
            'chainMap.component.degree',
            `The chain map has no component in degree ${requested}`
        );
    }
    return chainMap.components[
        requested - chainMap.source.minimumDegree
    ].morphism;
}

export const algebraModuleChainMapIdentity = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(complex: AlgebraModuleChainComplex<P, C, I>): AlgebraModuleChainMap<P, C, I> =>
    algebraModuleChainMap(
        complex,
        complex,
        complex.terms.map(term => ({
            degree: term.degree,
            morphism: algebraModuleIdentity(term.object)
        }))
    );

export function algebraModuleChainMapCompose<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    after: AlgebraModuleChainMap<P, C, I>,
    before: AlgebraModuleChainMap<P, C, I>
): AlgebraModuleChainMap<P, C, I> {
    if (!algebraModuleChainComplexEquals(before.target, after.source)) {
        return fail(
            'INVALID_CHAIN_MAP',
            'chainMapCompose',
            'Chain maps are not composable'
        );
    }
    return algebraModuleChainMap(
        before.source,
        after.target,
        before.components.map((component, index) => ({
            degree: component.degree,
            morphism: algebraModuleCompose(
                after.components[index].morphism,
                component.morphism
            )
        }))
    );
}

export interface AlgebraModuleShortExactDegree<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly degree: number;
    readonly projectionKernel: AlgebraModuleKernel<P, C, I>;
    readonly inclusionToKernel: AlgebraModuleMorphism<P, C, I>;
    readonly kernelToSubcomplex: AlgebraModuleMorphism<P, C, I>;
    readonly projectionSection: AlgebraModuleMorphism<P, C, I>;
}

export interface AlgebraModuleShortExactSequence<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-module-short-exact-sequence';
    readonly subcomplex: AlgebraModuleChainComplex<P, C, I>;
    readonly middle: AlgebraModuleChainComplex<P, C, I>;
    readonly quotient: AlgebraModuleChainComplex<P, C, I>;
    readonly inclusion: AlgebraModuleChainMap<P, C, I>;
    readonly projection: AlgebraModuleChainMap<P, C, I>;
    readonly degrees: readonly AlgebraModuleShortExactDegree<P, C, I>[];
}

export function algebraModuleShortExactSequence<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    inclusion: AlgebraModuleChainMap<P, C, I>,
    projection: AlgebraModuleChainMap<P, C, I>
): AlgebraModuleShortExactSequence<P, C, I> {
    if (!algebraModuleChainComplexEquals(
        inclusion.target,
        projection.source
    )) {
        return fail(
            'INVALID_SHORT_EXACT_SEQUENCE',
            'shortExactSequence',
            'The inclusion target must be the projection source'
        );
    }
    const degrees = inclusion.components.map((entry, index) => {
        const iota = entry.morphism;
        const epsilon = projection.components[index].morphism;
        if (!algebraModuleMorphismIsZero(algebraModuleCompose(
            epsilon,
            iota
        ))) {
            return fail(
                'SHORT_EXACTNESS_FAILED',
                `shortExactSequence.degrees[${index}]`,
                `The degree-${entry.degree} projection-inclusion ` +
                    'composite is not zero'
            );
        }
        try {
            const projectionKernel = algebraModuleKernel(epsilon);
            const inclusionToKernel = algebraModuleKernelLift(
                projectionKernel,
                iota
            );
            const kernelToSubcomplex = algebraModuleLiftAlongMonomorphism(
                iota,
                projectionKernel.inclusion
            );
            const projectionSection = algebraModuleLiftAlongEpimorphism(
                epsilon,
                algebraModuleIdentity(epsilon.target)
            );
            if (
                !algebraModuleMorphismEquivalent(
                    algebraModuleCompose(
                        kernelToSubcomplex,
                        inclusionToKernel
                    ),
                    algebraModuleIdentity(iota.source)
                ) ||
                !algebraModuleMorphismEquivalent(
                    algebraModuleCompose(
                        inclusionToKernel,
                        kernelToSubcomplex
                    ),
                    algebraModuleIdentity(projectionKernel.object)
                )
            ) {
                return fail(
                    'SHORT_EXACTNESS_FAILED',
                    `shortExactSequence.degrees[${index}]`,
                    'The inclusion image is not the projection kernel'
                );
            }
            return Object.freeze({
                degree: entry.degree,
                projectionKernel,
                inclusionToKernel,
                kernelToSubcomplex,
                projectionSection
            });
        } catch (error: unknown) {
            if (error instanceof AlgebraHomologicalError) throw error;
            return fail(
                'SHORT_EXACTNESS_FAILED',
                `shortExactSequence.degrees[${index}]`,
                `The degree-${entry.degree} sequence is not short exact`
            );
        }
    });
    return Object.freeze({
        kind: 'algebra-module-short-exact-sequence',
        subcomplex: inclusion.source,
        middle: inclusion.target,
        quotient: projection.target,
        inclusion,
        projection,
        degrees: Object.freeze(degrees)
    });
}

export interface AlgebraModuleHomology<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-module-homology';
    readonly incoming: AlgebraModuleMorphism<P, C, I>;
    readonly outgoing: AlgebraModuleMorphism<P, C, I>;
    readonly cycles: AlgebraModuleKernel<P, C, I>;
    readonly boundaryLift: AlgebraModuleMorphism<P, C, I>;
    readonly quotient: AlgebraModuleCokernel<P, C, I>;
    readonly object: AlgebraPresentedModule<P, C, I>;
}

/** Compute ker(outgoing) / im(incoming), requiring outgoing * incoming = 0. */
export function algebraModuleHomology<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    incoming: AlgebraModuleMorphism<P, C, I>,
    outgoing: AlgebraModuleMorphism<P, C, I>
): AlgebraModuleHomology<P, C, I> {
    if (!algebraPresentedModuleEquals(incoming.target, outgoing.source)) {
        return fail(
            'INVALID_DIFFERENTIAL',
            'homology',
            'Homology requires a composable incoming/outgoing pair'
        );
    }
    if (!algebraModuleMorphismIsZero(algebraModuleCompose(
        outgoing,
        incoming
    ))) {
        return fail(
            'CHAIN_CONDITION_FAILED',
            'homology',
            'Homology requires an outgoing-incoming zero composite'
        );
    }
    const cycles = algebraModuleKernel(outgoing);
    const boundaryLift = algebraModuleKernelLift(cycles, incoming);
    const quotient = algebraModuleCokernel(boundaryLift);
    return Object.freeze({
        kind: 'algebra-module-homology',
        incoming,
        outgoing,
        cycles,
        boundaryLift,
        quotient,
        object: quotient.object
    });
}

export interface AlgebraModuleComplexHomology<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> extends Omit<AlgebraModuleHomology<P, C, I>, 'kind'> {
    readonly kind: 'algebra-module-complex-homology';
    readonly complex: AlgebraModuleChainComplex<P, C, I>;
    readonly degree: number;
}

export function algebraModuleChainComplexHomology<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    complex: AlgebraModuleChainComplex<P, C, I>,
    degreeInput: number
): AlgebraModuleComplexHomology<P, C, I> {
    const requested = degree(degreeInput, 'homology.degree');
    const center = algebraModuleChainComplexTerm(complex, requested);
    const zero = algebraFreeModule(complex.field, 0);
    const incoming = requested === complex.maximumDegree
        ? algebraModuleZeroMorphism(zero, center)
        : algebraModuleChainComplexDifferential(complex, requested + 1);
    const outgoing = requested === complex.minimumDegree
        ? algebraModuleZeroMorphism(center, zero)
        : algebraModuleChainComplexDifferential(complex, requested);
    const homology = algebraModuleHomology(incoming, outgoing);
    return Object.freeze({
        ...homology,
        kind: 'algebra-module-complex-homology',
        complex,
        degree: requested
    });
}

export interface AlgebraModuleHomologyMap<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-module-homology-map';
    readonly chainMap: AlgebraModuleChainMap<P, C, I>;
    readonly degree: number;
    readonly sourceHomology: AlgebraModuleComplexHomology<P, C, I>;
    readonly targetHomology: AlgebraModuleComplexHomology<P, C, I>;
    readonly cycleMap: AlgebraModuleMorphism<P, C, I>;
    readonly morphism: AlgebraModuleMorphism<P, C, I>;
}

/** Restrict a chain-map component to cycles and descend through boundaries. */
export function algebraModuleChainMapHomology<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    chainMap: AlgebraModuleChainMap<P, C, I>,
    degreeInput: number
): AlgebraModuleHomologyMap<P, C, I> {
    const requested = degree(degreeInput, 'chainMapHomology.degree');
    const sourceHomology = algebraModuleChainComplexHomology(
        chainMap.source,
        requested
    );
    const targetHomology = algebraModuleChainComplexHomology(
        chainMap.target,
        requested
    );
    const component = algebraModuleChainMapComponentAt(chainMap, requested);
    const cycleMap = algebraModuleKernelLift(
        targetHomology.cycles,
        algebraModuleCompose(component, sourceHomology.cycles.inclusion)
    );
    const morphism = algebraModuleCokernelColift(
        sourceHomology.quotient,
        algebraModuleCompose(targetHomology.quotient.projection, cycleMap)
    );
    return Object.freeze({
        kind: 'algebra-module-homology-map',
        chainMap,
        degree: requested,
        sourceHomology,
        targetHomology,
        cycleMap,
        morphism
    });
}

export interface AlgebraModuleConnectingMorphism<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-module-connecting-morphism';
    readonly sequence: AlgebraModuleShortExactSequence<P, C, I>;
    readonly degree: number;
    readonly sourceHomology: AlgebraModuleComplexHomology<P, C, I>;
    readonly targetHomology: AlgebraModuleComplexHomology<P, C, I>;
    readonly liftedCyclesToMiddle: AlgebraModuleMorphism<P, C, I>;
    readonly middleBoundary: AlgebraModuleMorphism<P, C, I>;
    readonly boundaryInProjectionKernel: AlgebraModuleMorphism<P, C, I>;
    readonly liftedBoundaryToSubcomplex: AlgebraModuleMorphism<P, C, I>;
    readonly cycleMap: AlgebraModuleMorphism<P, C, I>;
    readonly morphism: AlgebraModuleMorphism<P, C, I>;
}

/** Compute the connecting map H_n(quotient) -> H_(n-1)(subcomplex). */
export function algebraModuleConnectingMorphism<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    sequence: AlgebraModuleShortExactSequence<P, C, I>,
    degreeInput: number
): AlgebraModuleConnectingMorphism<P, C, I> {
    const requested = degree(degreeInput, 'connectingMorphism.degree');
    if (
        requested <= sequence.middle.minimumDegree ||
        requested > sequence.middle.maximumDegree
    ) {
        return fail(
            'DEGREE_OUT_OF_RANGE',
            'connectingMorphism.degree',
            'A connecting morphism requires both degree n and n - 1'
        );
    }
    const sourceHomology = algebraModuleChainComplexHomology(
        sequence.quotient,
        requested
    );
    const targetHomology = algebraModuleChainComplexHomology(
        sequence.subcomplex,
        requested - 1
    );
    const degreeData = sequence.degrees[
        requested - sequence.middle.minimumDegree
    ];
    const previousDegreeData = sequence.degrees[
        requested - sequence.middle.minimumDegree - 1
    ];
    const liftedCyclesToMiddle = algebraModuleCompose(
        degreeData.projectionSection,
        sourceHomology.cycles.inclusion
    );
    const middleBoundary = algebraModuleCompose(
        algebraModuleChainComplexDifferential(sequence.middle, requested),
        liftedCyclesToMiddle
    );
    const boundaryInProjectionKernel = algebraModuleKernelLift(
        previousDegreeData.projectionKernel,
        middleBoundary
    );
    const liftedBoundaryToSubcomplex = algebraModuleCompose(
        previousDegreeData.kernelToSubcomplex,
        boundaryInProjectionKernel
    );
    const cycleMap = algebraModuleKernelLift(
        targetHomology.cycles,
        liftedBoundaryToSubcomplex
    );
    const morphism = algebraModuleCokernelColift(
        sourceHomology.quotient,
        algebraModuleCompose(targetHomology.quotient.projection, cycleMap)
    );
    return Object.freeze({
        kind: 'algebra-module-connecting-morphism',
        sequence,
        degree: requested,
        sourceHomology,
        targetHomology,
        liftedCyclesToMiddle,
        middleBoundary,
        boundaryInProjectionKernel,
        liftedBoundaryToSubcomplex,
        cycleMap,
        morphism
    });
}
