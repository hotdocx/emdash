/** Computational unimodular families and finite basic-open cover data. */

import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    AlgebraComputationContextInput,
    AlgebraRuntimeSchema,
    defineAlgebraRuntimeSchema
} from './algebra_engine';
import {
    AlgebraGroebnerBasis,
    AlgebraGroebnerOptions,
    AlgebraIdealMembership,
    AlgebraPolynomialIdeal,
    algebraGroebnerBasis,
    algebraGroebnerBasisSchema,
    algebraIdealCombination,
    algebraIdealMembership,
    algebraIdealMembershipSchema,
    algebraPolynomialIdeal,
    algebraPolynomialIdealSchema,
    algebraReducedGroebnerBasis
} from './algebra_ideal';
import {
    AlgebraPolynomial,
    AlgebraPolynomialRing,
    algebraPolynomialEquals,
    algebraPolynomialOne,
    algebraPolynomialSchema,
    algebraPolynomialText
} from './algebra_polynomial';

export const ALGEBRA_ZARISKI_PROFILE = Object.freeze({
    revision: 'emdash-algebra-zariski-v1' as const,
    serializationRevision: 'emdash-algebra-zariski-json-v1' as const,
    formalAdapter: false as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraZariskiErrorCode =
    | 'INVALID_UNIMODULAR_RESULT'
    | 'NOT_UNIMODULAR'
    | 'INVALID_COVER_PRESENTATION';

export class AlgebraZariskiError extends Error {
    constructor(
        public readonly code: AlgebraZariskiErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraZariskiError';
    }
}

const fail = (
    code: AlgebraZariskiErrorCode,
    path: string,
    message: string,
    underlying?: unknown
): never => {
    throw new AlgebraZariskiError(
        code,
        path,
        message,
        underlying instanceof Error ? underlying : undefined
    );
};

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

export interface AlgebraUnimodularCombination<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-unimodular-combination';
    readonly ideal: AlgebraPolynomialIdeal<P, C, I>;
    readonly basis: AlgebraGroebnerBasis<P, C, I>;
    readonly membership: AlgebraIdealMembership<P, C, I>;
    readonly unimodular: boolean;
    readonly coefficients: readonly AlgebraPolynomial<P, C, I>[];
    readonly combination: AlgebraPolynomial<P, C, I>;
    readonly remainder: AlgebraPolynomial<P, C, I>;
}

export interface AlgebraZariskiCoverPresentation<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-zariski-cover-presentation';
    readonly ring: AlgebraPolynomialRing<P, C, I>;
    readonly generators: readonly AlgebraPolynomial<P, C, I>[];
    readonly coefficients: readonly AlgebraPolynomial<P, C, I>[];
    readonly combination: AlgebraPolynomial<P, C, I>;
    readonly source: AlgebraUnimodularCombination<P, C, I>;
}

export interface AlgebraUnimodularOptions extends AlgebraGroebnerOptions {
    readonly reduceBasis?: boolean;
    readonly membershipReductionSteps?: number;
    readonly context?: AlgebraComputationContextInput;
}

export function algebraUnimodularCombination<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ideal: AlgebraPolynomialIdeal<P, C, I>,
    options: AlgebraUnimodularOptions = {}
): AlgebraUnimodularCombination<P, C, I> {
    const rawBasis = algebraGroebnerBasis(ideal, options);
    const basis = options.reduceBasis === false
        ? rawBasis
        : algebraReducedGroebnerBasis(rawBasis);
    const one = algebraPolynomialOne(ideal.ring);
    const membership = algebraIdealMembership(
        one,
        basis,
        options.membershipReductionSteps
    );
    const combination = algebraIdealCombination(
        ideal,
        membership.coefficients
    );
    return Object.freeze({
        kind: 'algebra-unimodular-combination',
        ideal,
        basis,
        membership,
        unimodular: membership.member,
        coefficients: membership.coefficients,
        combination,
        remainder: membership.remainder
    });
}

export const algebraUnimodularFamily = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ring: AlgebraPolynomialRing<P, C, I>,
    generators: readonly AlgebraPolynomial<P, C, I>[],
    options: AlgebraUnimodularOptions = {}
): AlgebraUnimodularCombination<P, C, I> => algebraUnimodularCombination(
    algebraPolynomialIdeal(ring, generators),
    options
);

export function algebraZariskiCoverPresentation<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    source: AlgebraUnimodularCombination<P, C, I>
): AlgebraZariskiCoverPresentation<P, C, I> {
    if (!source.unimodular) {
        return fail(
            'NOT_UNIMODULAR',
            'zariskiCover.source',
            'A finite basic-open cover requires a unimodular generator family'
        );
    }
    const one = algebraPolynomialOne(source.ideal.ring);
    if (!algebraPolynomialEquals(source.combination, one)) {
        return fail(
            'INVALID_UNIMODULAR_RESULT',
            'zariskiCover.source.combination',
            'Unimodular coefficients do not combine to one'
        );
    }
    return Object.freeze({
        kind: 'algebra-zariski-cover-presentation',
        ring: source.ideal.ring,
        generators: source.ideal.generators,
        coefficients: source.coefficients,
        combination: source.combination,
        source
    });
}

export function validateAlgebraUnimodularCombination<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ring: AlgebraPolynomialRing<P, C, I>,
    value: unknown,
    path = 'unimodular'
): AlgebraUnimodularCombination<P, C, I> {
    if (
        !record(value) ||
        value.kind !== 'algebra-unimodular-combination' ||
        typeof value.unimodular !== 'boolean' ||
        !Array.isArray(value.coefficients)
    ) {
        return fail(
            'INVALID_UNIMODULAR_RESULT',
            path,
            'Expected one structured unimodular-combination result'
        );
    }
    const ideal = algebraPolynomialIdealSchema(ring).normalize(
        value.ideal,
        `${path}.ideal`
    );
    const basis = algebraGroebnerBasisSchema(ring).normalize(
        value.basis,
        `${path}.basis`
    );
    const membership = algebraIdealMembershipSchema(ring).normalize(
        value.membership,
        `${path}.membership`
    );
    const polynomialSchema = algebraPolynomialSchema(ring);
    const coefficients = Object.freeze(value.coefficients.map(
        (coefficient, index) => polynomialSchema.normalize(
            coefficient,
            `${path}.coefficients[${index}]`
        )
    ));
    if (coefficients.length !== ideal.generators.length) {
        return fail(
            'INVALID_UNIMODULAR_RESULT',
            `${path}.coefficients`,
            'Unimodular coefficient count differs from generator count'
        );
    }
    const combination = polynomialSchema.normalize(
        value.combination,
        `${path}.combination`
    );
    const remainder = polynomialSchema.normalize(
        value.remainder,
        `${path}.remainder`
    );
    const reconstructed = algebraIdealCombination(ideal, coefficients);
    if (!algebraPolynomialEquals(reconstructed, combination)) {
        return fail(
            'INVALID_UNIMODULAR_RESULT',
            `${path}.combination`,
            'Combination differs from the retained coefficients and generators'
        );
    }
    if (
        value.unimodular !== membership.member ||
        !algebraPolynomialEquals(remainder, membership.remainder)
    ) {
        return fail(
            'INVALID_UNIMODULAR_RESULT',
            path,
            'Unimodular projection disagrees with retained membership data'
        );
    }
    return Object.freeze({
        kind: 'algebra-unimodular-combination',
        ideal,
        basis,
        membership,
        unimodular: value.unimodular,
        coefficients,
        combination,
        remainder
    });
}

export function algebraUnimodularCombinationSchema<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ring: AlgebraPolynomialRing<P, C, I>
): AlgebraRuntimeSchema<AlgebraUnimodularCombination<P, C, I>> {
    return defineAlgebraRuntimeSchema({
        id: `algebra.unimodular-combination/${ring.identity.id}`,
        revision: ring.identity.revision,
        normalize(value: unknown, path: string) {
            return validateAlgebraUnimodularCombination(ring, value, path);
        }
    });
}

export function validateAlgebraZariskiCoverPresentation<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ring: AlgebraPolynomialRing<P, C, I>,
    value: unknown,
    path = 'zariskiCover'
): AlgebraZariskiCoverPresentation<P, C, I> {
    if (
        !record(value) ||
        value.kind !== 'algebra-zariski-cover-presentation' ||
        !Array.isArray(value.generators) ||
        !Array.isArray(value.coefficients)
    ) {
        return fail(
            'INVALID_COVER_PRESENTATION',
            path,
            'Expected one computational Zariski-cover presentation'
        );
    }
    const source = validateAlgebraUnimodularCombination(
        ring,
        value.source,
        `${path}.source`
    );
    const reconstructed = algebraZariskiCoverPresentation(source);
    const polynomialSchema = algebraPolynomialSchema(ring);
    if (
        value.generators.length !== reconstructed.generators.length ||
        value.coefficients.length !== reconstructed.coefficients.length
    ) {
        return fail(
            'INVALID_COVER_PRESENTATION',
            path,
            'Zariski-cover projection lengths disagree with the source'
        );
    }
    const generatorsAgree = value.generators.every((generator, index) =>
        algebraPolynomialEquals(
            polynomialSchema.normalize(
                generator,
                `${path}.generators[${index}]`
            ),
            reconstructed.generators[index]
        )
    );
    const coefficientsAgree = value.coefficients.every((coefficient, index) =>
        algebraPolynomialEquals(
            polynomialSchema.normalize(
                coefficient,
                `${path}.coefficients[${index}]`
            ),
            reconstructed.coefficients[index]
        )
    );
    const combination = polynomialSchema.normalize(
        value.combination,
        `${path}.combination`
    );
    if (
        !generatorsAgree ||
        !coefficientsAgree ||
        !algebraPolynomialEquals(combination, reconstructed.combination)
    ) {
        return fail(
            'INVALID_COVER_PRESENTATION',
            path,
            'Zariski-cover projections disagree with the retained source'
        );
    }
    return reconstructed;
}

export function algebraZariskiCoverPresentationSchema<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ring: AlgebraPolynomialRing<P, C, I>
): AlgebraRuntimeSchema<AlgebraZariskiCoverPresentation<P, C, I>> {
    return defineAlgebraRuntimeSchema({
        id: `algebra.zariski-cover-presentation/${ring.identity.id}`,
        revision: ring.identity.revision,
        normalize(value: unknown, path: string) {
            return validateAlgebraZariskiCoverPresentation(ring, value, path);
        }
    });
}

export const serializeAlgebraUnimodularCombination = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraUnimodularCombination<P, C, I>): string => `${JSON.stringify({
    serializationRevision: ALGEBRA_ZARISKI_PROFILE.serializationRevision,
    kind: value.kind,
    ring: {
        id: value.ideal.ring.identity.id,
        revision: value.ideal.ring.identity.revision
    },
    generators: value.ideal.generators.map(algebraPolynomialText),
    unimodular: value.unimodular,
    coefficients: value.coefficients.map(algebraPolynomialText),
    combination: algebraPolynomialText(value.combination),
    remainder: algebraPolynomialText(value.remainder)
})}\n`;

export const serializeAlgebraZariskiCoverPresentation = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraZariskiCoverPresentation<P, C, I>): string =>
    `${JSON.stringify({
        serializationRevision: ALGEBRA_ZARISKI_PROFILE.serializationRevision,
        kind: value.kind,
        ring: {
            id: value.ring.identity.id,
            revision: value.ring.identity.revision
        },
        generators: value.generators.map(algebraPolynomialText),
        coefficients: value.coefficients.map(algebraPolynomialText),
        combination: algebraPolynomialText(value.combination)
    })}\n`;
