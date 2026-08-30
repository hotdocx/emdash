/** Canonical exact integer and rational values for the focused CAS. */

import {
    AlgebraElement,
    AlgebraParent,
    AlgebraParentError,
    assertAlgebraParent,
    defineAlgebraParent
} from './algebra_parent';
import {
    AlgebraRuntimeSchema,
    defineAlgebraRuntimeSchema
} from './algebra_engine';

export const ALGEBRA_EXACT_PROFILE = Object.freeze({
    revision: 'emdash-algebra-exact-v1' as const,
    serializationRevision: 'emdash-algebra-exact-json-v1' as const,
    integerRepresentation: 'bigint' as const,
    rationalRepresentation: 'reduced-numerator-positive-denominator' as const,
    acceptsJavascriptNumber: false as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraExactErrorCode =
    | 'INVALID_INTEGER'
    | 'INVALID_RATIONAL'
    | 'FOREIGN_PARENT'
    | 'ZERO_DENOMINATOR'
    | 'DIVISION_BY_ZERO'
    | 'NEGATIVE_EXPONENT';

export class AlgebraExactError extends Error {
    constructor(
        public readonly code: AlgebraExactErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraExactError';
    }
}

const fail = (
    code: AlgebraExactErrorCode,
    path: string,
    message: string,
    underlying?: unknown
): never => {
    throw new AlgebraExactError(
        code,
        path,
        message,
        underlying instanceof Error ? underlying : undefined
    );
};

export type AlgebraIntegerRing = AlgebraParent<'integer-ring'>;
export type AlgebraRationalField = AlgebraParent<'rational-field'>;

export const INTEGER_RING: AlgebraIntegerRing = defineAlgebraParent(
    'integer-ring',
    'algebra.integer-ring',
    'v1'
);

export const RATIONAL_FIELD: AlgebraRationalField = defineAlgebraParent(
    'rational-field',
    'algebra.rational-field',
    'v1'
);

export interface AlgebraInteger extends AlgebraElement<AlgebraIntegerRing> {
    readonly kind: 'algebra-integer';
    readonly value: bigint;
}

export interface AlgebraRational extends AlgebraElement<AlgebraRationalField> {
    readonly kind: 'algebra-rational';
    readonly numerator: bigint;
    readonly denominator: bigint;
}

export type AlgebraIntegerInput = bigint | string | AlgebraInteger;

export type AlgebraRationalInput =
    | bigint
    | string
    | AlgebraInteger
    | AlgebraRational
    | {
        readonly numerator: AlgebraIntegerInput;
        readonly denominator: AlgebraIntegerInput;
    };

const INTEGER_TEXT = /^(?:0|-[1-9][0-9]*|[1-9][0-9]*)$/u;
const RATIONAL_TEXT = /^(0|-[1-9][0-9]*|[1-9][0-9]*)(?:\/([1-9][0-9]*))?$/u;

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

const parseIntegerText = (value: string, path: string): bigint => {
    if (!INTEGER_TEXT.test(value)) {
        return fail(
            'INVALID_INTEGER',
            path,
            'Integer text must use canonical base-10 spelling'
        );
    }
    try {
        return BigInt(value);
    } catch (error: unknown) {
        return fail(
            'INVALID_INTEGER',
            path,
            'Integer text cannot be represented as bigint',
            error
        );
    }
};

const integerValue = (input: AlgebraIntegerInput, path: string): bigint => {
    if (typeof input === 'bigint') return input;
    if (typeof input === 'string') return parseIntegerText(input, path);
    if (!record(input) || input.kind !== 'algebra-integer') {
        return fail(
            'INVALID_INTEGER',
            path,
            'Expected bigint, canonical integer text, or AlgebraInteger'
        );
    }
    try {
        assertAlgebraParent(
            input.parent as AlgebraParent,
            INTEGER_RING,
            `${path}.parent`
        );
    } catch (error: unknown) {
        if (error instanceof AlgebraParentError) {
            return fail(
                'FOREIGN_PARENT',
                `${path}.parent`,
                'Integer value has a foreign parent',
                error
            );
        }
        throw error;
    }
    if (typeof input.value !== 'bigint') {
        return fail(
            'INVALID_INTEGER',
            `${path}.value`,
            'AlgebraInteger payload must be bigint'
        );
    }
    return input.value;
};

export const algebraInteger = (
    input: AlgebraIntegerInput,
    path = 'integer'
): AlgebraInteger => Object.freeze({
    kind: 'algebra-integer',
    parent: INTEGER_RING,
    value: integerValue(input, path)
});

const absBigInt = (value: bigint): bigint => value < 0n ? -value : value;

export const algebraIntegerGcd = (
    leftInput: AlgebraIntegerInput,
    rightInput: AlgebraIntegerInput
): AlgebraInteger => {
    let left = absBigInt(integerValue(leftInput, 'gcd.left'));
    let right = absBigInt(integerValue(rightInput, 'gcd.right'));
    while (right !== 0n) {
        const remainder = left % right;
        left = right;
        right = remainder;
    }
    return algebraInteger(left);
};

export interface AlgebraIntegerDivision {
    readonly quotient: AlgebraInteger;
    readonly remainder: AlgebraInteger;
}

export const algebraIntegerDivRem = (
    dividendInput: AlgebraIntegerInput,
    divisorInput: AlgebraIntegerInput
): AlgebraIntegerDivision => {
    const dividend = integerValue(dividendInput, 'divRem.dividend');
    const divisor = integerValue(divisorInput, 'divRem.divisor');
    if (divisor === 0n) {
        return fail(
            'DIVISION_BY_ZERO',
            'divRem.divisor',
            'Integer Euclidean division requires a nonzero divisor'
        );
    }
    let quotient = dividend / divisor;
    let remainder = dividend % divisor;
    if (remainder < 0n) {
        if (divisor > 0n) {
            quotient -= 1n;
            remainder += divisor;
        } else {
            quotient += 1n;
            remainder -= divisor;
        }
    }
    return Object.freeze({
        quotient: algebraInteger(quotient),
        remainder: algebraInteger(remainder)
    });
};

export const algebraIntegerAdd = (
    left: AlgebraIntegerInput,
    right: AlgebraIntegerInput
): AlgebraInteger => algebraInteger(
    integerValue(left, 'add.left') + integerValue(right, 'add.right')
);

export const algebraIntegerNegate = (
    value: AlgebraIntegerInput
): AlgebraInteger => algebraInteger(-integerValue(value, 'negate.value'));

export const algebraIntegerSubtract = (
    left: AlgebraIntegerInput,
    right: AlgebraIntegerInput
): AlgebraInteger => algebraInteger(
    integerValue(left, 'subtract.left') -
        integerValue(right, 'subtract.right')
);

export const algebraIntegerMultiply = (
    left: AlgebraIntegerInput,
    right: AlgebraIntegerInput
): AlgebraInteger => algebraInteger(
    integerValue(left, 'multiply.left') * integerValue(right, 'multiply.right')
);

const nonnegativeExponent = (value: bigint, path: string): bigint => {
    if (value < 0n) {
        return fail(
            'NEGATIVE_EXPONENT',
            path,
            'Exact power requires a nonnegative bigint exponent'
        );
    }
    return value;
};

const powerBigInt = (baseInput: bigint, exponentInput: bigint): bigint => {
    let base = baseInput;
    let exponent = exponentInput;
    let result = 1n;
    while (exponent > 0n) {
        if ((exponent & 1n) === 1n) result *= base;
        exponent >>= 1n;
        if (exponent > 0n) base *= base;
    }
    return result;
};

export const algebraIntegerPower = (
    base: AlgebraIntegerInput,
    exponent: bigint
): AlgebraInteger => {
    if (typeof exponent !== 'bigint') {
        return fail(
            'INVALID_INTEGER',
            'power.exponent',
            'Exact exponent must be bigint'
        );
    }
    return algebraInteger(powerBigInt(
        integerValue(base, 'power.base'),
        nonnegativeExponent(exponent, 'power.exponent')
    ));
};

export const algebraIntegerEquals = (
    left: AlgebraIntegerInput,
    right: AlgebraIntegerInput
): boolean => integerValue(left, 'equals.left') ===
    integerValue(right, 'equals.right');

export const algebraIntegerCompare = (
    left: AlgebraIntegerInput,
    right: AlgebraIntegerInput
): -1 | 0 | 1 => {
    const leftValue = integerValue(left, 'compare.left');
    const rightValue = integerValue(right, 'compare.right');
    return leftValue < rightValue ? -1 : leftValue > rightValue ? 1 : 0;
};

const reducedRational = (
    numeratorInput: bigint,
    denominatorInput: bigint,
    path: string
): AlgebraRational => {
    if (denominatorInput === 0n) {
        return fail(
            'ZERO_DENOMINATOR',
            `${path}.denominator`,
            'Rational denominator must be nonzero'
        );
    }
    if (numeratorInput === 0n) {
        return Object.freeze({
            kind: 'algebra-rational',
            parent: RATIONAL_FIELD,
            numerator: 0n,
            denominator: 1n
        });
    }
    const sign = denominatorInput < 0n ? -1n : 1n;
    const numerator = numeratorInput * sign;
    const denominator = denominatorInput * sign;
    const divisor = algebraIntegerGcd(numerator, denominator).value;
    return Object.freeze({
        kind: 'algebra-rational',
        parent: RATIONAL_FIELD,
        numerator: numerator / divisor,
        denominator: denominator / divisor
    });
};

const rationalParts = (
    input: AlgebraRationalInput,
    path: string
): readonly [bigint, bigint] => {
    if (typeof input === 'bigint') return [input, 1n];
    if (typeof input === 'string') {
        const match = RATIONAL_TEXT.exec(input);
        if (!match) {
            return fail(
                'INVALID_RATIONAL',
                path,
                'Rational text must use canonical n or n/d spelling'
            );
        }
        return [BigInt(match[1]), match[2] === undefined ? 1n : BigInt(match[2])];
    }
    if (!record(input)) {
        return fail(
            'INVALID_RATIONAL',
            path,
            'Expected exact rational input'
        );
    }
    if ('kind' in input && input.kind === 'algebra-integer') {
        return [integerValue(input as unknown as AlgebraInteger, path), 1n];
    }
    if ('kind' in input && input.kind === 'algebra-rational') {
        const rational = input as unknown as AlgebraRational;
        try {
            assertAlgebraParent(
                rational.parent as AlgebraParent,
                RATIONAL_FIELD,
                `${path}.parent`
            );
        } catch (error: unknown) {
            if (error instanceof AlgebraParentError) {
                return fail(
                    'FOREIGN_PARENT',
                    `${path}.parent`,
                    'Rational value has a foreign parent',
                    error
                );
            }
            throw error;
        }
        if (
            typeof rational.numerator !== 'bigint' ||
            typeof rational.denominator !== 'bigint'
        ) {
            return fail(
                'INVALID_RATIONAL',
                path,
                'AlgebraRational payloads must be bigint'
            );
        }
        return [rational.numerator, rational.denominator];
    }
    if ('numerator' in input && 'denominator' in input) {
        return [
            integerValue(
                input.numerator as AlgebraIntegerInput,
                `${path}.numerator`
            ),
            integerValue(
                input.denominator as AlgebraIntegerInput,
                `${path}.denominator`
            )
        ];
    }
    return fail(
        'INVALID_RATIONAL',
        path,
        'Rational record has an unsupported shape'
    );
};

export const algebraRational = (
    input: AlgebraRationalInput,
    path = 'rational'
): AlgebraRational => {
    const [numerator, denominator] = rationalParts(input, path);
    return reducedRational(numerator, denominator, path);
};

export const algebraRationalFromIntegers = (
    numerator: AlgebraIntegerInput,
    denominator: AlgebraIntegerInput
): AlgebraRational => reducedRational(
    integerValue(numerator, 'rational.numerator'),
    integerValue(denominator, 'rational.denominator'),
    'rational'
);

export const algebraIntegerToRational = (
    value: AlgebraIntegerInput
): AlgebraRational => algebraRational(integerValue(value, 'coerce.integer'));

export const algebraRationalAdd = (
    leftInput: AlgebraRationalInput,
    rightInput: AlgebraRationalInput
): AlgebraRational => {
    const left = algebraRational(leftInput, 'add.left');
    const right = algebraRational(rightInput, 'add.right');
    return reducedRational(
        left.numerator * right.denominator +
            right.numerator * left.denominator,
        left.denominator * right.denominator,
        'add.result'
    );
};

export const algebraRationalNegate = (
    value: AlgebraRationalInput
): AlgebraRational => {
    const normalized = algebraRational(value, 'negate.value');
    return reducedRational(
        -normalized.numerator,
        normalized.denominator,
        'negate.result'
    );
};

export const algebraRationalSubtract = (
    left: AlgebraRationalInput,
    right: AlgebraRationalInput
): AlgebraRational => algebraRationalAdd(left, algebraRationalNegate(right));

export const algebraRationalMultiply = (
    leftInput: AlgebraRationalInput,
    rightInput: AlgebraRationalInput
): AlgebraRational => {
    const left = algebraRational(leftInput, 'multiply.left');
    const right = algebraRational(rightInput, 'multiply.right');
    return reducedRational(
        left.numerator * right.numerator,
        left.denominator * right.denominator,
        'multiply.result'
    );
};

export const algebraRationalInverse = (
    value: AlgebraRationalInput
): AlgebraRational => {
    const normalized = algebraRational(value, 'inverse.value');
    if (normalized.numerator === 0n) {
        return fail(
            'DIVISION_BY_ZERO',
            'inverse.value',
            'Zero has no multiplicative inverse'
        );
    }
    return reducedRational(
        normalized.denominator,
        normalized.numerator,
        'inverse.result'
    );
};

export const algebraRationalDivide = (
    dividend: AlgebraRationalInput,
    divisor: AlgebraRationalInput
): AlgebraRational => algebraRationalMultiply(
    dividend,
    algebraRationalInverse(divisor)
);

export const algebraRationalPower = (
    baseInput: AlgebraRationalInput,
    exponent: bigint
): AlgebraRational => {
    if (typeof exponent !== 'bigint') {
        return fail(
            'INVALID_INTEGER',
            'power.exponent',
            'Exact exponent must be bigint'
        );
    }
    const normalizedExponent = nonnegativeExponent(
        exponent,
        'power.exponent'
    );
    const base = algebraRational(baseInput, 'power.base');
    return reducedRational(
        powerBigInt(base.numerator, normalizedExponent),
        powerBigInt(base.denominator, normalizedExponent),
        'power.result'
    );
};

export const algebraRationalEquals = (
    leftInput: AlgebraRationalInput,
    rightInput: AlgebraRationalInput
): boolean => {
    const left = algebraRational(leftInput, 'equals.left');
    const right = algebraRational(rightInput, 'equals.right');
    return left.numerator === right.numerator &&
        left.denominator === right.denominator;
};

export const algebraRationalCompare = (
    leftInput: AlgebraRationalInput,
    rightInput: AlgebraRationalInput
): -1 | 0 | 1 => {
    const left = algebraRational(leftInput, 'compare.left');
    const right = algebraRational(rightInput, 'compare.right');
    const difference = left.numerator * right.denominator -
        right.numerator * left.denominator;
    return difference < 0n ? -1 : difference > 0n ? 1 : 0;
};

export const algebraIntegerText = (value: AlgebraIntegerInput): string =>
    integerValue(value, 'integerText.value').toString(10);

export const algebraRationalText = (value: AlgebraRationalInput): string => {
    const normalized = algebraRational(value, 'rationalText.value');
    return normalized.denominator === 1n
        ? normalized.numerator.toString(10)
        : `${normalized.numerator.toString(10)}/` +
            normalized.denominator.toString(10);
};

export const serializeAlgebraInteger = (
    value: AlgebraIntegerInput
): string => `${JSON.stringify({
    serializationRevision: ALGEBRA_EXACT_PROFILE.serializationRevision,
    kind: 'algebra-integer',
    parent: {
        id: INTEGER_RING.identity.id,
        revision: INTEGER_RING.identity.revision
    },
    value: algebraIntegerText(value)
})}\n`;

export const serializeAlgebraRational = (
    value: AlgebraRationalInput
): string => {
    const normalized = algebraRational(value, 'serialize.value');
    return `${JSON.stringify({
        serializationRevision: ALGEBRA_EXACT_PROFILE.serializationRevision,
        kind: 'algebra-rational',
        parent: {
            id: RATIONAL_FIELD.identity.id,
            revision: RATIONAL_FIELD.identity.revision
        },
        numerator: normalized.numerator.toString(10),
        denominator: normalized.denominator.toString(10)
    })}\n`;
};

export const ALGEBRA_INTEGER_SCHEMA: AlgebraRuntimeSchema<AlgebraInteger> =
    defineAlgebraRuntimeSchema({
        id: 'algebra.exact.integer',
        revision: 'v1',
        normalize(value: unknown, path: string): AlgebraInteger {
            if (
                typeof value !== 'bigint' &&
                typeof value !== 'string' &&
                !record(value)
            ) {
                return fail(
                    'INVALID_INTEGER',
                    path,
                    'Integer schema rejects non-exact JavaScript values'
                );
            }
            return algebraInteger(value as AlgebraIntegerInput, path);
        }
    });

export const ALGEBRA_RATIONAL_SCHEMA: AlgebraRuntimeSchema<AlgebraRational> =
    defineAlgebraRuntimeSchema({
        id: 'algebra.exact.rational',
        revision: 'v1',
        normalize(value: unknown, path: string): AlgebraRational {
            if (
                typeof value !== 'bigint' &&
                typeof value !== 'string' &&
                !record(value)
            ) {
                return fail(
                    'INVALID_RATIONAL',
                    path,
                    'Rational schema rejects non-exact JavaScript values'
                );
            }
            return algebraRational(value as AlgebraRationalInput, path);
        }
    });

export interface AlgebraCommutativeRingDomain<
    Parent extends AlgebraParent,
    Element extends AlgebraElement<Parent>,
    Input
> {
    readonly kind: 'commutative-ring-domain';
    readonly parent: Parent;
    readonly schema: AlgebraRuntimeSchema<Element>;
    readonly zero: Element;
    readonly one: Element;
    normalize(value: Input | Element): Element;
    add(left: Input | Element, right: Input | Element): Element;
    negate(value: Input | Element): Element;
    subtract(left: Input | Element, right: Input | Element): Element;
    multiply(left: Input | Element, right: Input | Element): Element;
    power(base: Input | Element, exponent: bigint): Element;
    equals(left: Input | Element, right: Input | Element): boolean;
    compare(left: Input | Element, right: Input | Element): -1 | 0 | 1;
    isZero(value: Input | Element): boolean;
    isOne(value: Input | Element): boolean;
    text(value: Input | Element): string;
    serialize(value: Input | Element): string;
}

export interface AlgebraFieldDomain<
    Parent extends AlgebraParent,
    Element extends AlgebraElement<Parent>,
    Input
> extends AlgebraCommutativeRingDomain<Parent, Element, Input> {
    readonly field: true;
    inverse(value: Input | Element): Element;
    divide(dividend: Input | Element, divisor: Input | Element): Element;
}

export const INTEGER_DOMAIN: AlgebraCommutativeRingDomain<
    AlgebraIntegerRing,
    AlgebraInteger,
    AlgebraIntegerInput
> = Object.freeze({
    kind: 'commutative-ring-domain',
    parent: INTEGER_RING,
    schema: ALGEBRA_INTEGER_SCHEMA,
    zero: algebraInteger(0n),
    one: algebraInteger(1n),
    normalize: algebraInteger,
    add: algebraIntegerAdd,
    negate: algebraIntegerNegate,
    subtract: algebraIntegerSubtract,
    multiply: algebraIntegerMultiply,
    power: algebraIntegerPower,
    equals: algebraIntegerEquals,
    compare: algebraIntegerCompare,
    isZero: value => algebraIntegerEquals(value, 0n),
    isOne: value => algebraIntegerEquals(value, 1n),
    text: algebraIntegerText,
    serialize: serializeAlgebraInteger
});

export const RATIONAL_DOMAIN: AlgebraFieldDomain<
    AlgebraRationalField,
    AlgebraRational,
    AlgebraRationalInput
> = Object.freeze({
    kind: 'commutative-ring-domain',
    field: true,
    parent: RATIONAL_FIELD,
    schema: ALGEBRA_RATIONAL_SCHEMA,
    zero: algebraRational(0n),
    one: algebraRational(1n),
    normalize: algebraRational,
    add: algebraRationalAdd,
    negate: algebraRationalNegate,
    subtract: algebraRationalSubtract,
    multiply: algebraRationalMultiply,
    power: algebraRationalPower,
    equals: algebraRationalEquals,
    compare: algebraRationalCompare,
    isZero: value => algebraRationalEquals(value, 0n),
    isOne: value => algebraRationalEquals(value, 1n),
    text: algebraRationalText,
    serialize: serializeAlgebraRational,
    inverse: algebraRationalInverse,
    divide: algebraRationalDivide
});
