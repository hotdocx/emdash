/** Sparse polynomial free modules and a transparent module Buchberger engine. */

import {
    AlgebraElement,
    AlgebraParent,
    defineAlgebraParent,
    sameAlgebraParent
} from './algebra_parent';
import {
    AlgebraFieldDomain
} from './algebra_exact';
import {
    AlgebraComputationContext,
    AlgebraComputationContextInput,
    AlgebraRuntimeSchema,
    defineAlgebraRuntimeSchema,
    normalizeAlgebraComputationContext
} from './algebra_engine';
import {
    AlgebraMonomial,
    AlgebraPolynomial,
    AlgebraPolynomialRing,
    AlgebraPolynomialTerm,
    algebraPolynomialAdd,
    algebraPolynomialConstant,
    algebraPolynomialEquals,
    algebraPolynomialFromMonomial,
    algebraPolynomialLeadingTerm,
    algebraPolynomialMultiply,
    algebraPolynomialSchema,
    algebraPolynomialSubtract,
    algebraPolynomialZero,
    compareAlgebraMonomials,
    validateAlgebraPolynomial
} from './algebra_polynomial';

export const ALGEBRA_POLYNOMIAL_MODULE_PROFILE = Object.freeze({
    revision: 'emdash-algebra-polynomial-module-v1' as const,
    schemaRevision: 'emdash-algebra-polynomial-module-schema-v1' as const,
    vectorRepresentation: 'canonical-polynomial-components' as const,
    termOrders: ['position-over-term', 'term-over-position'] as const,
    positionTieBreak: 'lower-index-first' as const,
    algorithm: 'deterministic-module-buchberger-reference' as const,
    maximumRank: 100_000,
    maximumGenerators: 10_000,
    maximumBasisSize: 10_000,
    maximumPairs: 1_000_000,
    maximumReductionStepsPerPair: 1_000_000,
    maximumTotalReductionSteps: 10_000_000,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraPolynomialModuleTermOrder =
    | 'position-over-term'
    | 'term-over-position';

export type AlgebraPolynomialModuleErrorCode =
    | 'INVALID_FREE_MODULE'
    | 'INVALID_TERM_ORDER'
    | 'INVALID_VECTOR'
    | 'FOREIGN_FREE_MODULE'
    | 'NON_FIELD_COEFFICIENTS'
    | 'ZERO_DIVISOR'
    | 'INVALID_SUBMODULE'
    | 'INVALID_TRANSFORMATION'
    | 'INVALID_OPTIONS'
    | 'MODULE_LIMIT_EXCEEDED'
    | 'CANCELLED';

export class AlgebraPolynomialModuleError extends Error {
    constructor(
        public readonly code: AlgebraPolynomialModuleErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraPolynomialModuleError';
    }
}

const fail = (
    code: AlgebraPolynomialModuleErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraPolynomialModuleError(code, path, message);
};

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

export interface AlgebraPolynomialFreeModule<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> extends AlgebraParent<'polynomial-free-module'> {
    readonly ring: AlgebraPolynomialRing<P, C, I>;
    readonly rank: number;
    readonly termOrder: AlgebraPolynomialModuleTermOrder;
}

export interface AlgebraPolynomialModuleVector<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> extends AlgebraElement<AlgebraPolynomialFreeModule<P, C, I>> {
    readonly kind: 'algebra-polynomial-module-vector';
    readonly components: readonly AlgebraPolynomial<P, C, I>[];
}

export interface AlgebraPolynomialModuleTerm<
    P extends AlgebraParent,
    C extends AlgebraElement<P>
> extends AlgebraPolynomialTerm<P, C> {
    readonly position: number;
}

const assertOrder = (
    value: unknown
): AlgebraPolynomialModuleTermOrder => {
    if (value === 'position-over-term' || value === 'term-over-position') {
        return value;
    }
    return fail(
        'INVALID_TERM_ORDER',
        'polynomialModule.termOrder',
        'Expected position-over-term or term-over-position'
    );
};

const rank = (value: unknown): number => {
    if (
        Number.isSafeInteger(value) &&
        (value as number) >= 0 &&
        (value as number) <= ALGEBRA_POLYNOMIAL_MODULE_PROFILE.maximumRank
    ) return value as number;
    return fail(
        'INVALID_FREE_MODULE',
        'polynomialModule.rank',
        'Free-module rank must be a bounded nonnegative safe integer'
    );
};

export function algebraPolynomialFreeModule<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ring: AlgebraPolynomialRing<P, C, I>,
    rankInput: number,
    orderInput: AlgebraPolynomialModuleTermOrder = 'term-over-position'
): AlgebraPolynomialFreeModule<P, C, I> {
    const normalizedRank = rank(rankInput);
    const termOrder = assertOrder(orderInput);
    const parent = defineAlgebraParent(
        'polynomial-free-module',
        `algebra.polynomial-free-module/${ring.identity.id}/` +
            `${normalizedRank}/${termOrder}`,
        `v1.${ring.identity.revision}`
    );
    return Object.freeze({
        ...parent,
        ring,
        rank: normalizedRank,
        termOrder
    });
}

export function algebraPolynomialModuleVector<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    module: AlgebraPolynomialFreeModule<P, C, I>,
    componentInput: readonly AlgebraPolynomial<P, C, I>[]
): AlgebraPolynomialModuleVector<P, C, I> {
    if (!Array.isArray(componentInput) || componentInput.length !== module.rank) {
        return fail(
            'INVALID_VECTOR',
            'polynomialModuleVector.components',
            `Expected exactly ${module.rank} polynomial components`
        );
    }
    const components = componentInput.map((component, index) => {
        try {
            return validateAlgebraPolynomial(
                module.ring,
                component,
                `polynomialModuleVector.components[${index}]`
            );
        } catch {
            return fail(
                'FOREIGN_FREE_MODULE',
                `polynomialModuleVector.components[${index}]`,
                'Vector component belongs to a foreign polynomial ring'
            );
        }
    });
    return Object.freeze({
        kind: 'algebra-polynomial-module-vector',
        parent: module,
        components: Object.freeze(components)
    });
}

export function validateAlgebraPolynomialModuleVector<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    module: AlgebraPolynomialFreeModule<P, C, I>,
    value: unknown,
    path = 'polynomialModuleVector'
): AlgebraPolynomialModuleVector<P, C, I> {
    if (
        !record(value) ||
        value.kind !== 'algebra-polynomial-module-vector' ||
        !record(value.parent) ||
        !sameAlgebraParent(
            value.parent as unknown as AlgebraParent,
            module
        ) ||
        !Array.isArray(value.components)
    ) {
        return fail(
            'INVALID_VECTOR',
            path,
            'Expected one vector in the selected polynomial free module'
        );
    }
    const polynomialSchema = algebraPolynomialSchema(module.ring);
    return algebraPolynomialModuleVector(
        module,
        value.components.map((component, index) =>
            polynomialSchema.normalize(component, `${path}.components[${index}]`)
        )
    );
}

export function algebraPolynomialModuleVectorSchema<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(module: AlgebraPolynomialFreeModule<P, C, I>): AlgebraRuntimeSchema<
    AlgebraPolynomialModuleVector<P, C, I>
> {
    return defineAlgebraRuntimeSchema({
        id: `algebra.polynomial-module-vector/${module.identity.id}`,
        revision: module.identity.revision,
        normalize: (value, path) => validateAlgebraPolynomialModuleVector(
            module,
            value,
            path
        )
    });
}

export const algebraPolynomialModuleZero = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(module: AlgebraPolynomialFreeModule<P, C, I>):
    AlgebraPolynomialModuleVector<P, C, I> => algebraPolynomialModuleVector(
        module,
        Array.from({ length: module.rank }, () =>
            algebraPolynomialZero(module.ring)
        )
    );

const sameModule = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomialModuleVector<P, C, I>,
    right: AlgebraPolynomialModuleVector<P, C, I>,
    path: string
): AlgebraPolynomialFreeModule<P, C, I> => {
    if (!sameAlgebraParent(left.parent, right.parent)) {
        return fail(
            'FOREIGN_FREE_MODULE',
            path,
            'Polynomial-module vectors inhabit different free modules'
        );
    }
    return left.parent;
};

export const compareAlgebraPolynomialModuleTerms = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    module: AlgebraPolynomialFreeModule<P, C, I>,
    left: AlgebraPolynomialModuleTerm<P, C>,
    right: AlgebraPolynomialModuleTerm<P, C>
): -1 | 0 | 1 => {
    const positionComparison = left.position === right.position
        ? 0
        : left.position < right.position ? 1 : -1;
    if (module.termOrder === 'position-over-term' && positionComparison !== 0) {
        return positionComparison;
    }
    const monomialComparison = compareAlgebraMonomials(
        module.ring.monomialOrder,
        left.monomial,
        right.monomial
    );
    if (monomialComparison !== 0) return monomialComparison;
    return positionComparison;
};

export const algebraPolynomialModuleLeadingTerm = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(vector: AlgebraPolynomialModuleVector<P, C, I>):
    AlgebraPolynomialModuleTerm<P, C> | undefined => {
    let leading: AlgebraPolynomialModuleTerm<P, C> | undefined;
    vector.components.forEach((component, position) => {
        const term = algebraPolynomialLeadingTerm(component);
        if (term === undefined) return;
        const candidate = Object.freeze({ ...term, position });
        if (
            leading === undefined ||
            compareAlgebraPolynomialModuleTerms(
                vector.parent,
                candidate,
                leading
            ) > 0
        ) leading = candidate;
    });
    return leading;
};

export const algebraPolynomialModuleAdd = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomialModuleVector<P, C, I>,
    right: AlgebraPolynomialModuleVector<P, C, I>
): AlgebraPolynomialModuleVector<P, C, I> => {
    const module = sameModule(left, right, 'polynomialModuleAdd');
    return algebraPolynomialModuleVector(
        module,
        left.components.map((component, index) =>
            algebraPolynomialAdd(component, right.components[index])
        )
    );
};

export const algebraPolynomialModuleSubtract = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomialModuleVector<P, C, I>,
    right: AlgebraPolynomialModuleVector<P, C, I>
): AlgebraPolynomialModuleVector<P, C, I> => {
    const module = sameModule(left, right, 'polynomialModuleSubtract');
    return algebraPolynomialModuleVector(
        module,
        left.components.map((component, index) =>
            algebraPolynomialSubtract(component, right.components[index])
        )
    );
};

export const algebraPolynomialModuleScale = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    scalar: AlgebraPolynomial<P, C, I>,
    vector: AlgebraPolynomialModuleVector<P, C, I>
): AlgebraPolynomialModuleVector<P, C, I> => algebraPolynomialModuleVector(
        vector.parent,
        vector.components.map(component =>
            algebraPolynomialMultiply(scalar, component)
        )
    );

export const algebraPolynomialModuleEquals = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomialModuleVector<P, C, I>,
    right: AlgebraPolynomialModuleVector<P, C, I>
): boolean => sameAlgebraParent(left.parent, right.parent) &&
    left.components.every((component, index) =>
        algebraPolynomialEquals(component, right.components[index])
    );

const singleTermVector = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    module: AlgebraPolynomialFreeModule<P, C, I>,
    term: AlgebraPolynomialModuleTerm<P, C>
): AlgebraPolynomialModuleVector<P, C, I> => algebraPolynomialModuleVector(
        module,
        Array.from({ length: module.rank }, (_, position) =>
            position === term.position
                ? algebraPolynomialFromMonomial(
                    module.ring,
                    term.coefficient,
                    term.monomial.exponents
                )
                : algebraPolynomialZero(module.ring)
        )
    );

const monomialDivides = (
    divisor: AlgebraMonomial,
    dividend: AlgebraMonomial
): boolean => divisor.exponents.every((value, index) =>
    value <= dividend.exponents[index]
);

const monomialQuotient = (
    dividend: AlgebraMonomial,
    divisor: AlgebraMonomial
): readonly bigint[] => Object.freeze(dividend.exponents.map((value, index) =>
    value - divisor.exponents[index]
));

const fieldDomain = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(ring: AlgebraPolynomialRing<P, C, I>): AlgebraFieldDomain<P, C, I> => {
    const field = ring.coefficientDomain as Partial<AlgebraFieldDomain<P, C, I>>;
    if (
        field.field !== true ||
        typeof field.divide !== 'function' ||
        typeof field.inverse !== 'function'
    ) {
        return fail(
            'NON_FIELD_COEFFICIENTS',
            'polynomialModule.ring',
            'Module division and Groebner bases require a coefficient field'
        );
    }
    return field as AlgebraFieldDomain<P, C, I>;
};

export interface AlgebraPolynomialModuleDivision<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly quotients: readonly AlgebraPolynomial<P, C, I>[];
    readonly remainder: AlgebraPolynomialModuleVector<P, C, I>;
    readonly steps: number;
}

export function algebraPolynomialModuleDivide<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    dividend: AlgebraPolynomialModuleVector<P, C, I>,
    divisorInput: readonly AlgebraPolynomialModuleVector<P, C, I>[],
    maximumSteps: number =
        ALGEBRA_POLYNOMIAL_MODULE_PROFILE.maximumReductionStepsPerPair
): AlgebraPolynomialModuleDivision<P, C, I> {
    const field = fieldDomain(dividend.parent.ring);
    if (!Number.isSafeInteger(maximumSteps) || maximumSteps <= 0) {
        return fail(
            'MODULE_LIMIT_EXCEEDED',
            'polynomialModuleDivision.maximumSteps',
            'Division step limit must be a positive safe integer'
        );
    }
    const divisors = divisorInput.map((divisor, index) => {
        sameModule(dividend, divisor, `polynomialModuleDivision.divisors[${index}]`);
        if (algebraPolynomialModuleLeadingTerm(divisor) === undefined) {
            return fail(
                'ZERO_DIVISOR',
                `polynomialModuleDivision.divisors[${index}]`,
                'Module divisor must be nonzero'
            );
        }
        return divisor;
    });
    const quotients = divisors.map(() =>
        algebraPolynomialZero(dividend.parent.ring)
    );
    let current = dividend;
    let remainder = algebraPolynomialModuleZero(dividend.parent);
    let steps = 0;
    while (algebraPolynomialModuleLeadingTerm(current) !== undefined) {
        if (steps >= maximumSteps) {
            return fail(
                'MODULE_LIMIT_EXCEEDED',
                'polynomialModuleDivision.steps',
                `Module division exceeded ${maximumSteps} steps`
            );
        }
        steps++;
        const currentLead = algebraPolynomialModuleLeadingTerm(current)!;
        let reduced = false;
        for (let index = 0; index < divisors.length; index++) {
            const divisorLead = algebraPolynomialModuleLeadingTerm(divisors[index])!;
            if (
                currentLead.position !== divisorLead.position ||
                !monomialDivides(divisorLead.monomial, currentLead.monomial)
            ) continue;
            const quotient = algebraPolynomialFromMonomial(
                dividend.parent.ring,
                field.divide(
                    currentLead.coefficient,
                    divisorLead.coefficient
                ),
                monomialQuotient(
                    currentLead.monomial,
                    divisorLead.monomial
                )
            );
            quotients[index] = algebraPolynomialAdd(quotients[index], quotient);
            current = algebraPolynomialModuleSubtract(
                current,
                algebraPolynomialModuleScale(quotient, divisors[index])
            );
            reduced = true;
            break;
        }
        if (!reduced) {
            const leadingVector = singleTermVector(dividend.parent, currentLead);
            remainder = algebraPolynomialModuleAdd(remainder, leadingVector);
            current = algebraPolynomialModuleSubtract(current, leadingVector);
        }
    }
    return Object.freeze({
        quotients: Object.freeze(quotients),
        remainder,
        steps
    });
}

export interface AlgebraPolynomialSubmodule<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-submodule';
    readonly module: AlgebraPolynomialFreeModule<P, C, I>;
    readonly generators: readonly AlgebraPolynomialModuleVector<P, C, I>[];
}

export function algebraPolynomialSubmodule<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    module: AlgebraPolynomialFreeModule<P, C, I>,
    generatorInput: readonly AlgebraPolynomialModuleVector<P, C, I>[]
): AlgebraPolynomialSubmodule<P, C, I> {
    if (
        !Array.isArray(generatorInput) ||
        generatorInput.length > ALGEBRA_POLYNOMIAL_MODULE_PROFILE.maximumGenerators
    ) {
        return fail(
            'INVALID_SUBMODULE',
            'polynomialSubmodule.generators',
            'Submodule generators must be one bounded array'
        );
    }
    const generators = generatorInput.map((generator, index) => {
        if (!sameAlgebraParent(module, generator.parent)) {
            return fail(
                'FOREIGN_FREE_MODULE',
                `polynomialSubmodule.generators[${index}]`,
                'Submodule generator belongs to a foreign free module'
            );
        }
        return generator;
    });
    return Object.freeze({
        kind: 'algebra-polynomial-submodule',
        module,
        generators: Object.freeze(generators)
    });
}

export interface AlgebraPolynomialModuleGroebnerBasis<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-module-groebner-basis';
    readonly submodule: AlgebraPolynomialSubmodule<P, C, I>;
    readonly basis: readonly AlgebraPolynomialModuleVector<P, C, I>[];
    /** basis[i] = sum_j transformations[i][j] * generators[j]. */
    readonly transformations: readonly (
        readonly AlgebraPolynomial<P, C, I>[]
    )[];
    readonly pairsProcessed: number;
    readonly reductionSteps: number;
}

export interface AlgebraPolynomialModuleGroebnerOptions {
    readonly maximumBasisSize?: number;
    readonly maximumPairs?: number;
    readonly maximumReductionStepsPerPair?: number;
    readonly maximumTotalReductionSteps?: number;
    readonly context?: AlgebraComputationContextInput;
}

const positiveLimit = (
    value: unknown,
    fallback: number,
    path: string
): number => {
    if (value === undefined) return fallback;
    if (Number.isSafeInteger(value) && (value as number) > 0) {
        return value as number;
    }
    return fail(
        'MODULE_LIMIT_EXCEEDED',
        path,
        'Module algorithm limit must be a positive safe integer'
    );
};

const zeroRow = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(ring: AlgebraPolynomialRing<P, C, I>, length: number):
    AlgebraPolynomial<P, C, I>[] => Array.from(
        { length },
        () => algebraPolynomialZero(ring)
    );

const unitRow = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(ring: AlgebraPolynomialRing<P, C, I>, length: number, index: number):
    AlgebraPolynomial<P, C, I>[] => zeroRow(ring, length).map(
        (value, position) => position === index
            ? algebraPolynomialConstant(ring, ring.coefficientDomain.one)
            : value
    );

const rowSubtract = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: readonly AlgebraPolynomial<P, C, I>[],
    right: readonly AlgebraPolynomial<P, C, I>[]
): AlgebraPolynomial<P, C, I>[] => {
    if (left.length !== right.length) {
        return fail(
            'INVALID_TRANSFORMATION',
            'moduleGroebner.transformation',
            'Transformation rows have different lengths'
        );
    }
    return left.map((value, index) =>
        algebraPolynomialSubtract(value, right[index])
    );
};

const rowScale = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    scalar: AlgebraPolynomial<P, C, I>,
    row: readonly AlgebraPolynomial<P, C, I>[]
): AlgebraPolynomial<P, C, I>[] => row.map(value =>
    algebraPolynomialMultiply(scalar, value)
);

const lcmExponents = (
    left: AlgebraMonomial,
    right: AlgebraMonomial
): readonly bigint[] => Object.freeze(left.exponents.map((value, index) =>
    value > right.exponents[index] ? value : right.exponents[index]
));

const monicVectorAndRow = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    vector: AlgebraPolynomialModuleVector<P, C, I>,
    row: readonly AlgebraPolynomial<P, C, I>[],
    field: AlgebraFieldDomain<P, C, I>
): {
    readonly vector: AlgebraPolynomialModuleVector<P, C, I>;
    readonly row: AlgebraPolynomial<P, C, I>[];
} => {
    const leading = algebraPolynomialModuleLeadingTerm(vector);
    if (leading === undefined) return { vector, row: [...row] };
    const scalar = algebraPolynomialConstant(
        vector.parent.ring,
        field.inverse(leading.coefficient)
    );
    return {
        vector: algebraPolynomialModuleScale(scalar, vector),
        row: rowScale(scalar, row)
    };
};

const sPairWithRow = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomialModuleVector<P, C, I>,
    leftRow: readonly AlgebraPolynomial<P, C, I>[],
    right: AlgebraPolynomialModuleVector<P, C, I>,
    rightRow: readonly AlgebraPolynomial<P, C, I>[],
    field: AlgebraFieldDomain<P, C, I>
): {
    readonly vector: AlgebraPolynomialModuleVector<P, C, I>;
    readonly row: AlgebraPolynomial<P, C, I>[];
} => {
    const leftLead = algebraPolynomialModuleLeadingTerm(left)!;
    const rightLead = algebraPolynomialModuleLeadingTerm(right)!;
    const lcm = lcmExponents(leftLead.monomial, rightLead.monomial);
    const leftMultiplier = algebraPolynomialFromMonomial(
        left.parent.ring,
        field.inverse(leftLead.coefficient),
        Object.freeze(lcm.map((value, index) =>
            value - leftLead.monomial.exponents[index]
        ))
    );
    const rightMultiplier = algebraPolynomialFromMonomial(
        left.parent.ring,
        field.inverse(rightLead.coefficient),
        Object.freeze(lcm.map((value, index) =>
            value - rightLead.monomial.exponents[index]
        ))
    );
    return {
        vector: algebraPolynomialModuleSubtract(
            algebraPolynomialModuleScale(leftMultiplier, left),
            algebraPolynomialModuleScale(rightMultiplier, right)
        ),
        row: rowSubtract(
            rowScale(leftMultiplier, leftRow),
            rowScale(rightMultiplier, rightRow)
        )
    };
};

export function algebraPolynomialModuleCombination<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    generators: readonly AlgebraPolynomialModuleVector<P, C, I>[],
    coefficients: readonly AlgebraPolynomial<P, C, I>[]
): AlgebraPolynomialModuleVector<P, C, I> {
    if (generators.length === 0) {
        return fail(
            'INVALID_TRANSFORMATION',
            'moduleCombination.generators',
            'A combination requires at least one ambient-module witness'
        );
    }
    if (generators.length !== coefficients.length) {
        return fail(
            'INVALID_TRANSFORMATION',
            'moduleCombination.coefficients',
            'Combination coefficient count disagrees with generators'
        );
    }
    return generators.reduce(
        (sum, generator, index) => algebraPolynomialModuleAdd(
            sum,
            algebraPolynomialModuleScale(coefficients[index], generator)
        ),
        algebraPolynomialModuleZero(generators[0].parent)
    );
}

export function algebraPolynomialModuleGroebnerBasis<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    submodule: AlgebraPolynomialSubmodule<P, C, I>,
    optionsInput: AlgebraPolynomialModuleGroebnerOptions = {}
): AlgebraPolynomialModuleGroebnerBasis<P, C, I> {
    if (!record(optionsInput)) {
        return fail(
            'INVALID_OPTIONS',
            'moduleGroebner.options',
            'Module Groebner options must be a record'
        );
    }
    const field = fieldDomain(submodule.module.ring);
    const maximumBasisSize = positiveLimit(
        optionsInput.maximumBasisSize,
        ALGEBRA_POLYNOMIAL_MODULE_PROFILE.maximumBasisSize,
        'moduleGroebner.maximumBasisSize'
    );
    const maximumPairs = positiveLimit(
        optionsInput.maximumPairs,
        ALGEBRA_POLYNOMIAL_MODULE_PROFILE.maximumPairs,
        'moduleGroebner.maximumPairs'
    );
    const maximumReductionStepsPerPair = positiveLimit(
        optionsInput.maximumReductionStepsPerPair,
        ALGEBRA_POLYNOMIAL_MODULE_PROFILE.maximumReductionStepsPerPair,
        'moduleGroebner.maximumReductionStepsPerPair'
    );
    const maximumTotalReductionSteps = positiveLimit(
        optionsInput.maximumTotalReductionSteps,
        ALGEBRA_POLYNOMIAL_MODULE_PROFILE.maximumTotalReductionSteps,
        'moduleGroebner.maximumTotalReductionSteps'
    );
    const context: AlgebraComputationContext = normalizeAlgebraComputationContext(
        optionsInput.context
    );
    const basis: AlgebraPolynomialModuleVector<P, C, I>[] = [];
    const transformations: AlgebraPolynomial<P, C, I>[][] = [];
    submodule.generators.forEach((generator, index) => {
        if (algebraPolynomialModuleLeadingTerm(generator) === undefined) return;
        const normalized = monicVectorAndRow(
            generator,
            unitRow(
                submodule.module.ring,
                submodule.generators.length,
                index
            ),
            field
        );
        if (!basis.some(value => algebraPolynomialModuleEquals(
            value,
            normalized.vector
        ))) {
            basis.push(normalized.vector);
            transformations.push(normalized.row);
        }
    });
    if (basis.length > maximumBasisSize) {
        return fail(
            'MODULE_LIMIT_EXCEEDED',
            'moduleGroebner.basis',
            'Initial module basis exceeds the selected limit'
        );
    }
    const pairs: [number, number][] = [];
    const enqueueWith = (right: number): void => {
        const rightLead = algebraPolynomialModuleLeadingTerm(basis[right])!;
        for (let left = 0; left < right; left++) {
            if (
                algebraPolynomialModuleLeadingTerm(basis[left])!.position ===
                rightLead.position
            ) pairs.push([left, right]);
        }
    };
    for (let right = 1; right < basis.length; right++) enqueueWith(right);
    let pairCursor = 0;
    let pairsProcessed = 0;
    let reductionSteps = 0;
    while (pairCursor < pairs.length) {
        if (context.cancellation?.requested()) {
            return fail(
                'CANCELLED',
                'moduleGroebner.pairs',
                context.cancellation.reason?.() ?? 'Module Groebner cancelled'
            );
        }
        if (pairsProcessed >= maximumPairs) {
            return fail(
                'MODULE_LIMIT_EXCEEDED',
                'moduleGroebner.pairs',
                'Module Groebner pair limit exceeded'
            );
        }
        const [leftIndex, rightIndex] = pairs[pairCursor++];
        pairsProcessed++;
        context.onProgress?.({
            phase: 'algebra.polynomial-module.buchberger',
            completed: pairsProcessed,
            total: pairs.length
        });
        const pair = sPairWithRow(
            basis[leftIndex],
            transformations[leftIndex],
            basis[rightIndex],
            transformations[rightIndex],
            field
        );
        const division = algebraPolynomialModuleDivide(
            pair.vector,
            basis,
            maximumReductionStepsPerPair
        );
        let row = [...pair.row];
        division.quotients.forEach((quotient, index) => {
            row = rowSubtract(row, rowScale(quotient, transformations[index]));
        });
        reductionSteps += division.steps;
        if (reductionSteps > maximumTotalReductionSteps) {
            return fail(
                'MODULE_LIMIT_EXCEEDED',
                'moduleGroebner.reductionSteps',
                'Module Groebner total reduction limit exceeded'
            );
        }
        if (algebraPolynomialModuleLeadingTerm(division.remainder) === undefined) {
            continue;
        }
        const normalized = monicVectorAndRow(division.remainder, row, field);
        if (basis.some(value => algebraPolynomialModuleEquals(
            value,
            normalized.vector
        ))) continue;
        if (basis.length >= maximumBasisSize) {
            return fail(
                'MODULE_LIMIT_EXCEEDED',
                'moduleGroebner.basis',
                'Module Groebner basis limit exceeded'
            );
        }
        basis.push(normalized.vector);
        transformations.push(normalized.row);
        enqueueWith(basis.length - 1);
    }
    return Object.freeze({
        kind: 'algebra-polynomial-module-groebner-basis',
        submodule,
        basis: Object.freeze(basis),
        transformations: Object.freeze(transformations.map(row =>
            Object.freeze(row)
        )),
        pairsProcessed,
        reductionSteps
    });
}

export interface AlgebraPolynomialModuleMembership<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-module-membership';
    readonly vector: AlgebraPolynomialModuleVector<P, C, I>;
    readonly basis: AlgebraPolynomialModuleGroebnerBasis<P, C, I>;
    readonly member: boolean;
    readonly coefficients: readonly AlgebraPolynomial<P, C, I>[];
    readonly remainder: AlgebraPolynomialModuleVector<P, C, I>;
    readonly basisQuotients: readonly AlgebraPolynomial<P, C, I>[];
    readonly reductionSteps: number;
}

export function algebraPolynomialModuleMembership<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    vector: AlgebraPolynomialModuleVector<P, C, I>,
    basis: AlgebraPolynomialModuleGroebnerBasis<P, C, I>,
    maximumSteps: number =
        ALGEBRA_POLYNOMIAL_MODULE_PROFILE.maximumReductionStepsPerPair
): AlgebraPolynomialModuleMembership<P, C, I> {
    sameModule(
        vector,
        algebraPolynomialModuleZero(basis.submodule.module),
        'moduleMembership.vector'
    );
    const division = algebraPolynomialModuleDivide(vector, basis.basis, maximumSteps);
    let coefficients = zeroRow(
        basis.submodule.module.ring,
        basis.submodule.generators.length
    );
    division.quotients.forEach((quotient, index) => {
        const contribution = rowScale(quotient, basis.transformations[index]);
        coefficients = coefficients.map((value, position) =>
            algebraPolynomialAdd(value, contribution[position])
        );
    });
    return Object.freeze({
        kind: 'algebra-polynomial-module-membership',
        vector,
        basis,
        member: algebraPolynomialModuleLeadingTerm(division.remainder) === undefined,
        coefficients: Object.freeze(coefficients),
        remainder: division.remainder,
        basisQuotients: division.quotients,
        reductionSteps: division.steps
    });
}
