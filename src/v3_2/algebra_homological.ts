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
    algebraModuleCokernel,
    algebraModuleCompose,
    algebraModuleKernel,
    algebraModuleKernelLift,
    algebraModuleMorphismIsZero,
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
