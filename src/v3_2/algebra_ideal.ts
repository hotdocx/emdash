/** Ideals and a transparent Buchberger reference algorithm. */

import {
    AlgebraElement,
    AlgebraParent
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
    AlgebraPolynomialDivision,
    AlgebraPolynomialRing,
    algebraPolynomialAdd,
    algebraPolynomialConstant,
    algebraPolynomialDivide,
    algebraPolynomialEquals,
    algebraPolynomialFromMonomial,
    algebraPolynomialLeadingTerm,
    algebraPolynomialMultiply,
    algebraPolynomialSchema,
    algebraPolynomialSubtract,
    algebraPolynomialText,
    algebraPolynomialZero,
    compareAlgebraMonomials,
    validateAlgebraPolynomial
} from './algebra_polynomial';

export const ALGEBRA_IDEAL_PROFILE = Object.freeze({
    revision: 'emdash-algebra-ideal-v1' as const,
    serializationRevision: 'emdash-algebra-ideal-json-v1' as const,
    algorithm: 'deterministic-buchberger-reference' as const,
    maximumGenerators: 10_000,
    maximumBasisSize: 10_000,
    maximumPairs: 1_000_000,
    maximumReductionStepsPerPair: 1_000_000,
    maximumTotalReductionSteps: 10_000_000,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraIdealErrorCode =
    | 'INVALID_IDEAL'
    | 'FOREIGN_POLYNOMIAL_RING'
    | 'NON_FIELD_COEFFICIENTS'
    | 'INVALID_GROEBNER_BASIS'
    | 'INVALID_TRANSFORMATION'
    | 'IDEAL_LIMIT_EXCEEDED'
    | 'CANCELLED';

export class AlgebraIdealError extends Error {
    constructor(
        public readonly code: AlgebraIdealErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraIdealError';
    }
}

const fail = (
    code: AlgebraIdealErrorCode,
    path: string,
    message: string,
    underlying?: unknown
): never => {
    throw new AlgebraIdealError(
        code,
        path,
        message,
        underlying instanceof Error ? underlying : undefined
    );
};

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

export interface AlgebraPolynomialIdeal<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-ideal';
    readonly ring: AlgebraPolynomialRing<P, C, I>;
    readonly generators: readonly AlgebraPolynomial<P, C, I>[];
}

export interface AlgebraGroebnerBasis<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-groebner-basis';
    readonly ideal: AlgebraPolynomialIdeal<P, C, I>;
    readonly basis: readonly AlgebraPolynomial<P, C, I>[];
    /** basis[i] = sum_j transformations[i][j] * ideal.generators[j]. */
    readonly transformations: readonly (
        readonly AlgebraPolynomial<P, C, I>[]
    )[];
    readonly pairsProcessed: number;
    readonly reductionSteps: number;
    readonly reduced: boolean;
}

export interface AlgebraIdealMembership<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-ideal-membership';
    readonly polynomial: AlgebraPolynomial<P, C, I>;
    readonly basis: AlgebraGroebnerBasis<P, C, I>;
    readonly member: boolean;
    /** polynomial = sum_j coefficients[j] * generators[j] + remainder. */
    readonly coefficients: readonly AlgebraPolynomial<P, C, I>[];
    readonly remainder: AlgebraPolynomial<P, C, I>;
    readonly basisQuotients: readonly AlgebraPolynomial<P, C, I>[];
    readonly reductionSteps: number;
}

export interface AlgebraGroebnerOptions {
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
        'IDEAL_LIMIT_EXCEEDED',
        path,
        'Ideal algorithm limit must be a positive safe integer'
    );
};

const fieldDomain = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ring: AlgebraPolynomialRing<P, C, I>
): AlgebraFieldDomain<P, C, I> => {
    const domain = ring.coefficientDomain as Partial<
        AlgebraFieldDomain<P, C, I>
    >;
    if (
        domain.field !== true ||
        typeof domain.divide !== 'function' ||
        typeof domain.inverse !== 'function'
    ) {
        return fail(
            'NON_FIELD_COEFFICIENTS',
            'ideal.ring.coefficientDomain',
            'Groebner computation requires an operational coefficient field'
        );
    }
    return domain as AlgebraFieldDomain<P, C, I>;
};

export function algebraPolynomialIdeal<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ring: AlgebraPolynomialRing<P, C, I>,
    generatorInput: readonly AlgebraPolynomial<P, C, I>[]
): AlgebraPolynomialIdeal<P, C, I> {
    if (!Array.isArray(generatorInput)) {
        return fail(
            'INVALID_IDEAL',
            'ideal.generators',
            'Ideal generators must be an array'
        );
    }
    if (generatorInput.length > ALGEBRA_IDEAL_PROFILE.maximumGenerators) {
        return fail(
            'IDEAL_LIMIT_EXCEEDED',
            'ideal.generators',
            `Ideal exceeds ${ALGEBRA_IDEAL_PROFILE.maximumGenerators} generators`
        );
    }
    const generators = generatorInput.map((generator, index) => {
        try {
            return validateAlgebraPolynomial(
                ring,
                generator,
                `ideal.generators[${index}]`
            );
        } catch (error: unknown) {
            return fail(
                'FOREIGN_POLYNOMIAL_RING',
                `ideal.generators[${index}]`,
                'Ideal generator does not inhabit the selected ring',
                error
            );
        }
    });
    return Object.freeze({
        kind: 'algebra-polynomial-ideal',
        ring,
        generators: Object.freeze(generators)
    });
}

export function algebraPolynomialIdealSchema<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ring: AlgebraPolynomialRing<P, C, I>
): AlgebraRuntimeSchema<AlgebraPolynomialIdeal<P, C, I>> {
    const polynomialSchema = algebraPolynomialSchema(ring);
    return defineAlgebraRuntimeSchema({
        id: `algebra.ideal/${ring.identity.id}`,
        revision: ring.identity.revision,
        normalize(value: unknown, path: string) {
            if (
                !record(value) ||
                value.kind !== 'algebra-polynomial-ideal' ||
                !Array.isArray(value.generators)
            ) {
                throw new Error(`polynomial ideal expected at ${path}`);
            }
            return algebraPolynomialIdeal(
                ring,
                value.generators.map((generator, index) =>
                    polynomialSchema.normalize(
                        generator,
                        `${path}.generators[${index}]`
                    )
                )
            );
        }
    });
}

const zeroVector = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ring: AlgebraPolynomialRing<P, C, I>,
    length: number
): AlgebraPolynomial<P, C, I>[] => Array.from(
    { length },
    () => algebraPolynomialZero(ring)
);

const unitVector = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ring: AlgebraPolynomialRing<P, C, I>,
    length: number,
    index: number
): AlgebraPolynomial<P, C, I>[] => zeroVector(ring, length).map(
    (value, position) => position === index
        ? algebraPolynomialConstant(ring, ring.coefficientDomain.one)
        : value
);

const vectorAdd = <
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
            'transformation',
            'Transformation rows have different lengths'
        );
    }
    return left.map((value, index) => algebraPolynomialAdd(value, right[index]));
};

const vectorSubtract = <
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
            'transformation',
            'Transformation rows have different lengths'
        );
    }
    return left.map((value, index) =>
        algebraPolynomialSubtract(value, right[index])
    );
};

const vectorScale = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    scalar: AlgebraPolynomial<P, C, I>,
    row: readonly AlgebraPolynomial<P, C, I>[]
): AlgebraPolynomial<P, C, I>[] => row.map(value =>
    algebraPolynomialMultiply(scalar, value)
);

const lcmMonomial = (
    left: AlgebraMonomial,
    right: AlgebraMonomial
): readonly bigint[] => Object.freeze(left.exponents.map((value, index) =>
    value > right.exponents[index] ? value : right.exponents[index]
));

const monomialQuotientExponents = (
    dividend: readonly bigint[],
    divisor: AlgebraMonomial
): readonly bigint[] => Object.freeze(dividend.map((value, index) =>
    value - divisor.exponents[index]
));

const monomialDivides = (
    divisor: AlgebraMonomial,
    dividend: AlgebraMonomial
): boolean => divisor.exponents.every((value, index) =>
    value <= dividend.exponents[index]
);

const monicPolynomialAndRow = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    polynomial: AlgebraPolynomial<P, C, I>,
    row: readonly AlgebraPolynomial<P, C, I>[],
    field: AlgebraFieldDomain<P, C, I>
): {
    readonly polynomial: AlgebraPolynomial<P, C, I>;
    readonly row: AlgebraPolynomial<P, C, I>[];
} => {
    const leading = algebraPolynomialLeadingTerm(polynomial);
    if (leading === undefined) return { polynomial, row: [...row] };
    const scalar = algebraPolynomialConstant(
        polynomial.parent,
        field.inverse(leading.coefficient)
    );
    return {
        polynomial: algebraPolynomialMultiply(scalar, polynomial),
        row: vectorScale(scalar, row)
    };
};

export const algebraPolynomialSPolynomial = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomial<P, C, I>,
    right: AlgebraPolynomial<P, C, I>
): AlgebraPolynomial<P, C, I> => {
    if (
        left.parent.identity.id !== right.parent.identity.id ||
        left.parent.identity.revision !== right.parent.identity.revision
    ) {
        return fail(
            'FOREIGN_POLYNOMIAL_RING',
            'sPolynomial.right.parent',
            'S-polynomial inputs must inhabit the same polynomial ring'
        );
    }
    const field = fieldDomain(left.parent);
    const leftLead = algebraPolynomialLeadingTerm(left);
    const rightLead = algebraPolynomialLeadingTerm(right);
    if (leftLead === undefined || rightLead === undefined) {
        return algebraPolynomialZero(left.parent);
    }
    const lcm = lcmMonomial(leftLead.monomial, rightLead.monomial);
    const leftMultiplier = algebraPolynomialFromMonomial(
        left.parent,
        field.inverse(leftLead.coefficient),
        monomialQuotientExponents(lcm, leftLead.monomial)
    );
    const rightMultiplier = algebraPolynomialFromMonomial(
        left.parent,
        field.inverse(rightLead.coefficient),
        monomialQuotientExponents(lcm, rightLead.monomial)
    );
    return algebraPolynomialSubtract(
        algebraPolynomialMultiply(leftMultiplier, left),
        algebraPolynomialMultiply(rightMultiplier, right)
    );
};

const sPolynomialWithRow = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomial<P, C, I>,
    leftRow: readonly AlgebraPolynomial<P, C, I>[],
    right: AlgebraPolynomial<P, C, I>,
    rightRow: readonly AlgebraPolynomial<P, C, I>[],
    field: AlgebraFieldDomain<P, C, I>
): {
    readonly polynomial: AlgebraPolynomial<P, C, I>;
    readonly row: AlgebraPolynomial<P, C, I>[];
} => {
    const leftLead = algebraPolynomialLeadingTerm(left)!;
    const rightLead = algebraPolynomialLeadingTerm(right)!;
    const lcm = lcmMonomial(leftLead.monomial, rightLead.monomial);
    const leftMultiplier = algebraPolynomialFromMonomial(
        left.parent,
        field.inverse(leftLead.coefficient),
        monomialQuotientExponents(lcm, leftLead.monomial)
    );
    const rightMultiplier = algebraPolynomialFromMonomial(
        left.parent,
        field.inverse(rightLead.coefficient),
        monomialQuotientExponents(lcm, rightLead.monomial)
    );
    return {
        polynomial: algebraPolynomialSubtract(
            algebraPolynomialMultiply(leftMultiplier, left),
            algebraPolynomialMultiply(rightMultiplier, right)
        ),
        row: vectorSubtract(
            vectorScale(leftMultiplier, leftRow),
            vectorScale(rightMultiplier, rightRow)
        )
    };
};

const reduceWithRows = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    polynomial: AlgebraPolynomial<P, C, I>,
    row: readonly AlgebraPolynomial<P, C, I>[],
    basis: readonly AlgebraPolynomial<P, C, I>[],
    rows: readonly (readonly AlgebraPolynomial<P, C, I>[])[],
    maximumSteps: number
): {
    readonly polynomial: AlgebraPolynomial<P, C, I>;
    readonly row: AlgebraPolynomial<P, C, I>[];
    readonly division: AlgebraPolynomialDivision<P, C, I>;
} => {
    const division = algebraPolynomialDivide(polynomial, basis, maximumSteps);
    let resultRow = [...row];
    division.quotients.forEach((quotient, index) => {
        resultRow = vectorSubtract(
            resultRow,
            vectorScale(quotient, rows[index])
        );
    });
    return {
        polynomial: division.remainder,
        row: resultRow,
        division
    };
};

const normalizedOptions = (
    input: AlgebraGroebnerOptions = {}
): Required<Omit<AlgebraGroebnerOptions, 'context'>> & {
    readonly context: AlgebraComputationContext;
} => {
    if (!record(input)) {
        return fail(
            'INVALID_IDEAL',
            'groebner.options',
            'Groebner options must be a record'
        );
    }
    return {
        maximumBasisSize: positiveLimit(
            input.maximumBasisSize,
            ALGEBRA_IDEAL_PROFILE.maximumBasisSize,
            'groebner.options.maximumBasisSize'
        ),
        maximumPairs: positiveLimit(
            input.maximumPairs,
            ALGEBRA_IDEAL_PROFILE.maximumPairs,
            'groebner.options.maximumPairs'
        ),
        maximumReductionStepsPerPair: positiveLimit(
            input.maximumReductionStepsPerPair,
            ALGEBRA_IDEAL_PROFILE.maximumReductionStepsPerPair,
            'groebner.options.maximumReductionStepsPerPair'
        ),
        maximumTotalReductionSteps: positiveLimit(
            input.maximumTotalReductionSteps,
            ALGEBRA_IDEAL_PROFILE.maximumTotalReductionSteps,
            'groebner.options.maximumTotalReductionSteps'
        ),
        context: normalizeAlgebraComputationContext(
            input.context as AlgebraComputationContextInput | undefined
        )
    };
};

const checkCancellation = (
    context: AlgebraComputationContext,
    path: string
): void => {
    if (context.cancellation?.requested()) {
        fail(
            'CANCELLED',
            path,
            context.cancellation.reason?.() ?? 'Groebner computation cancelled'
        );
    }
};

export function algebraGroebnerBasis<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ideal: AlgebraPolynomialIdeal<P, C, I>,
    optionInput: AlgebraGroebnerOptions = {}
): AlgebraGroebnerBasis<P, C, I> {
    const options = normalizedOptions(optionInput);
    const field = fieldDomain(ideal.ring);
    const basis: AlgebraPolynomial<P, C, I>[] = [];
    const transformations: AlgebraPolynomial<P, C, I>[][] = [];

    ideal.generators.forEach((generator, index) => {
        if (generator.terms.length === 0) return;
        const normalized = monicPolynomialAndRow(
            generator,
            unitVector(ideal.ring, ideal.generators.length, index),
            field
        );
        if (!basis.some(value => algebraPolynomialEquals(
            value,
            normalized.polynomial
        ))) {
            basis.push(normalized.polynomial);
            transformations.push(normalized.row);
        }
    });
    if (basis.length > options.maximumBasisSize) {
        return fail(
            'IDEAL_LIMIT_EXCEEDED',
            'groebner.basis',
            `Initial basis exceeds ${options.maximumBasisSize} elements`
        );
    }

    const pairs: [number, number][] = [];
    for (let right = 1; right < basis.length; right++) {
        for (let left = 0; left < right; left++) pairs.push([left, right]);
    }
    let pairCursor = 0;
    let pairsProcessed = 0;
    let reductionSteps = 0;

    while (pairCursor < pairs.length) {
        checkCancellation(options.context, 'groebner.pairs');
        if (pairsProcessed >= options.maximumPairs) {
            return fail(
                'IDEAL_LIMIT_EXCEEDED',
                'groebner.pairs',
                `Groebner computation exceeds ${options.maximumPairs} pairs`
            );
        }
        const [leftIndex, rightIndex] = pairs[pairCursor++];
        pairsProcessed++;
        options.context.onProgress?.({
            phase: 'algebra.ideal.buchberger',
            completed: pairsProcessed,
            total: pairs.length,
            message: `Reducing S-pair ${leftIndex},${rightIndex}`
        });
        const s = sPolynomialWithRow(
            basis[leftIndex],
            transformations[leftIndex],
            basis[rightIndex],
            transformations[rightIndex],
            field
        );
        const reduced = reduceWithRows(
            s.polynomial,
            s.row,
            basis,
            transformations,
            options.maximumReductionStepsPerPair
        );
        reductionSteps += reduced.division.steps;
        if (reductionSteps > options.maximumTotalReductionSteps) {
            return fail(
                'IDEAL_LIMIT_EXCEEDED',
                'groebner.reductionSteps',
                `Groebner reductions exceed ` +
                    `${options.maximumTotalReductionSteps} total steps`
            );
        }
        if (reduced.polynomial.terms.length === 0) continue;
        const normalized = monicPolynomialAndRow(
            reduced.polynomial,
            reduced.row,
            field
        );
        if (basis.some(value => algebraPolynomialEquals(
            value,
            normalized.polynomial
        ))) {
            continue;
        }
        if (basis.length >= options.maximumBasisSize) {
            return fail(
                'IDEAL_LIMIT_EXCEEDED',
                'groebner.basis',
                `Groebner basis exceeds ${options.maximumBasisSize} elements`
            );
        }
        const next = basis.length;
        basis.push(normalized.polynomial);
        transformations.push(normalized.row);
        for (let index = 0; index < next; index++) pairs.push([index, next]);
    }

    return Object.freeze({
        kind: 'algebra-groebner-basis',
        ideal,
        basis: Object.freeze(basis),
        transformations: Object.freeze(transformations.map(row =>
            Object.freeze(row)
        )),
        pairsProcessed,
        reductionSteps,
        reduced: false
    });
}

export function algebraReducedGroebnerBasis<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    source: AlgebraGroebnerBasis<P, C, I>,
    maximumReductionSteps: number =
        ALGEBRA_IDEAL_PROFILE.maximumReductionStepsPerPair
): AlgebraGroebnerBasis<P, C, I> {
    const field = fieldDomain(source.ideal.ring);
    const keep = source.basis.map((basis, index) => {
        const leading = algebraPolynomialLeadingTerm(basis)!;
        return !source.basis.some((other, otherIndex) => {
            if (index === otherIndex) return false;
            const otherLeading = algebraPolynomialLeadingTerm(other)!;
            if (!monomialDivides(otherLeading.monomial, leading.monomial)) {
                return false;
            }
            const same = otherLeading.monomial.exponents.every(
                (value, position) => value === leading.monomial.exponents[position]
            );
            return !same || otherIndex < index;
        });
    });
    const minimalBasis = source.basis.filter((_, index) => keep[index]);
    const minimalRows = source.transformations.filter((_, index) => keep[index]);
    const reducedBasis: AlgebraPolynomial<P, C, I>[] = [];
    const reducedRows: AlgebraPolynomial<P, C, I>[][] = [];
    let reductionSteps = source.reductionSteps;

    minimalBasis.forEach((basis, index) => {
        const otherBasis = minimalBasis.filter((_, other) => other !== index);
        const otherRows = minimalRows.filter((_, other) => other !== index);
        const reduced = reduceWithRows(
            basis,
            minimalRows[index],
            otherBasis,
            otherRows,
            maximumReductionSteps
        );
        reductionSteps += reduced.division.steps;
        if (reduced.polynomial.terms.length === 0) return;
        const normalized = monicPolynomialAndRow(
            reduced.polynomial,
            reduced.row,
            field
        );
        reducedBasis.push(normalized.polynomial);
        reducedRows.push(normalized.row);
    });

    const order = reducedBasis.map((_, index) => index).sort((left, right) =>
        -compareAlgebraMonomials(
            source.ideal.ring.monomialOrder,
            algebraPolynomialLeadingTerm(reducedBasis[left])!.monomial,
            algebraPolynomialLeadingTerm(reducedBasis[right])!.monomial
        )
    );
    return Object.freeze({
        kind: 'algebra-groebner-basis',
        ideal: source.ideal,
        basis: Object.freeze(order.map(index => reducedBasis[index])),
        transformations: Object.freeze(order.map(index =>
            Object.freeze(reducedRows[index])
        )),
        pairsProcessed: source.pairsProcessed,
        reductionSteps,
        reduced: true
    });
}

export function algebraIdealCombination<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ideal: AlgebraPolynomialIdeal<P, C, I>,
    coefficients: readonly AlgebraPolynomial<P, C, I>[]
): AlgebraPolynomial<P, C, I> {
    if (!Array.isArray(coefficients) || coefficients.length !== ideal.generators.length) {
        return fail(
            'INVALID_TRANSFORMATION',
            'combination.coefficients',
            `Expected ${ideal.generators.length} ideal coefficients`
        );
    }
    return coefficients.reduce(
        (sum, coefficient, index) => algebraPolynomialAdd(
            sum,
            algebraPolynomialMultiply(coefficient, ideal.generators[index])
        ),
        algebraPolynomialZero(ideal.ring)
    );
}

export function algebraIdealMembership<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    polynomial: AlgebraPolynomial<P, C, I>,
    basis: AlgebraGroebnerBasis<P, C, I>,
    maximumReductionSteps: number =
        ALGEBRA_IDEAL_PROFILE.maximumReductionStepsPerPair
): AlgebraIdealMembership<P, C, I> {
    const normalized = validateAlgebraPolynomial(
        basis.ideal.ring,
        polynomial,
        'membership.polynomial'
    );
    const division = algebraPolynomialDivide(
        normalized,
        basis.basis,
        maximumReductionSteps
    );
    let coefficients = zeroVector(
        basis.ideal.ring,
        basis.ideal.generators.length
    );
    division.quotients.forEach((quotient, index) => {
        coefficients = vectorAdd(
            coefficients,
            vectorScale(quotient, basis.transformations[index])
        );
    });
    return Object.freeze({
        kind: 'algebra-ideal-membership',
        polynomial: normalized,
        basis,
        member: division.remainder.terms.length === 0,
        coefficients: Object.freeze(coefficients),
        remainder: division.remainder,
        basisQuotients: division.quotients,
        reductionSteps: division.steps
    });
}

export const serializeAlgebraPolynomialIdeal = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(ideal: AlgebraPolynomialIdeal<P, C, I>): string => `${JSON.stringify({
    serializationRevision: ALGEBRA_IDEAL_PROFILE.serializationRevision,
    kind: ideal.kind,
    ring: {
        id: ideal.ring.identity.id,
        revision: ideal.ring.identity.revision
    },
    generators: ideal.generators.map(algebraPolynomialText)
})}\n`;

export const serializeAlgebraGroebnerBasis = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(basis: AlgebraGroebnerBasis<P, C, I>): string => `${JSON.stringify({
    serializationRevision: ALGEBRA_IDEAL_PROFILE.serializationRevision,
    kind: basis.kind,
    ring: {
        id: basis.ideal.ring.identity.id,
        revision: basis.ideal.ring.identity.revision
    },
    generators: basis.ideal.generators.map(algebraPolynomialText),
    basis: basis.basis.map(algebraPolynomialText),
    transformations: basis.transformations.map(row =>
        row.map(algebraPolynomialText)
    ),
    pairsProcessed: basis.pairsProcessed,
    reductionSteps: basis.reductionSteps,
    reduced: basis.reduced
})}\n`;

export function validateAlgebraGroebnerBasis<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ring: AlgebraPolynomialRing<P, C, I>,
    value: unknown,
    path = 'groebnerBasis'
): AlgebraGroebnerBasis<P, C, I> {
    if (
        !record(value) ||
        value.kind !== 'algebra-groebner-basis' ||
        !record(value.ideal) ||
        !Array.isArray(value.basis) ||
        !Array.isArray(value.transformations) ||
        !Number.isSafeInteger(value.pairsProcessed) ||
        (value.pairsProcessed as number) < 0 ||
        !Number.isSafeInteger(value.reductionSteps) ||
        (value.reductionSteps as number) < 0 ||
        typeof value.reduced !== 'boolean'
    ) {
        return fail(
            'INVALID_GROEBNER_BASIS',
            path,
            'Expected one structured Groebner-basis result'
        );
    }
    const idealSchema = algebraPolynomialIdealSchema(ring);
    const ideal = idealSchema.normalize(value.ideal, `${path}.ideal`);
    const polynomialSchema = algebraPolynomialSchema(ring);
    const basis = value.basis.map((polynomial, index) =>
        polynomialSchema.normalize(polynomial, `${path}.basis[${index}]`)
    );
    if (value.transformations.length !== basis.length) {
        return fail(
            'INVALID_TRANSFORMATION',
            `${path}.transformations`,
            'Transformation row count differs from basis size'
        );
    }
    const transformations = value.transformations.map((row, rowIndex) => {
        if (!Array.isArray(row) || row.length !== ideal.generators.length) {
            return fail(
                'INVALID_TRANSFORMATION',
                `${path}.transformations[${rowIndex}]`,
                'Transformation row width differs from generator count'
            );
        }
        return Object.freeze(row.map((polynomial, columnIndex) =>
            polynomialSchema.normalize(
                polynomial,
                `${path}.transformations[${rowIndex}][${columnIndex}]`
            )
        ));
    });
    return Object.freeze({
        kind: 'algebra-groebner-basis',
        ideal,
        basis: Object.freeze(basis),
        transformations: Object.freeze(transformations),
        pairsProcessed: value.pairsProcessed as number,
        reductionSteps: value.reductionSteps as number,
        reduced: value.reduced
    });
}

export function algebraGroebnerBasisSchema<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ring: AlgebraPolynomialRing<P, C, I>
): AlgebraRuntimeSchema<AlgebraGroebnerBasis<P, C, I>> {
    return defineAlgebraRuntimeSchema({
        id: `algebra.groebner-basis/${ring.identity.id}`,
        revision: ring.identity.revision,
        normalize(value: unknown, path: string) {
            return validateAlgebraGroebnerBasis(ring, value, path);
        }
    });
}

export function validateAlgebraIdealMembership<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ring: AlgebraPolynomialRing<P, C, I>,
    value: unknown,
    path = 'idealMembership'
): AlgebraIdealMembership<P, C, I> {
    if (
        !record(value) ||
        value.kind !== 'algebra-ideal-membership' ||
        typeof value.member !== 'boolean' ||
        !Array.isArray(value.coefficients) ||
        !Array.isArray(value.basisQuotients) ||
        !Number.isSafeInteger(value.reductionSteps) ||
        (value.reductionSteps as number) < 0
    ) {
        return fail(
            'INVALID_IDEAL',
            path,
            'Expected one structured ideal-membership result'
        );
    }
    const polynomialSchema = algebraPolynomialSchema(ring);
    const polynomial = polynomialSchema.normalize(
        value.polynomial,
        `${path}.polynomial`
    );
    const basis = validateAlgebraGroebnerBasis(
        ring,
        value.basis,
        `${path}.basis`
    );
    if (value.coefficients.length !== basis.ideal.generators.length) {
        return fail(
            'INVALID_TRANSFORMATION',
            `${path}.coefficients`,
            'Membership coefficient count differs from generator count'
        );
    }
    if (value.basisQuotients.length !== basis.basis.length) {
        return fail(
            'INVALID_TRANSFORMATION',
            `${path}.basisQuotients`,
            'Basis quotient count differs from basis size'
        );
    }
    const coefficients = Object.freeze(value.coefficients.map(
        (coefficient, index) => polynomialSchema.normalize(
            coefficient,
            `${path}.coefficients[${index}]`
        )
    ));
    const basisQuotients = Object.freeze(value.basisQuotients.map(
        (quotient, index) => polynomialSchema.normalize(
            quotient,
            `${path}.basisQuotients[${index}]`
        )
    ));
    const remainder = polynomialSchema.normalize(
        value.remainder,
        `${path}.remainder`
    );
    return Object.freeze({
        kind: 'algebra-ideal-membership',
        polynomial,
        basis,
        member: value.member,
        coefficients,
        remainder,
        basisQuotients,
        reductionSteps: value.reductionSteps as number
    });
}

export function algebraIdealMembershipSchema<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ring: AlgebraPolynomialRing<P, C, I>
): AlgebraRuntimeSchema<AlgebraIdealMembership<P, C, I>> {
    return defineAlgebraRuntimeSchema({
        id: `algebra.ideal-membership/${ring.identity.id}`,
        revision: ring.identity.revision,
        normalize(value: unknown, path: string) {
            return validateAlgebraIdealMembership(ring, value, path);
        }
    });
}
