/** Inert mathematical source and retained computation for the first goal workspace. */

import {
    RATIONAL_DOMAIN, algebraPolynomial, algebraPolynomialRing, algebraPolynomialText,
    algebraPolynomialIdeal, algebraGroebnerBasis, algebraIdealMembership,
    algebraIdealWitnessSource, checkAlgebraIdealWitness, normalizeAlgebraIdealWitnessInput,
    serializeAlgebraPolynomial, type AlgebraIdealWitnessInput,
    type AlgebraMonomialOrder, type AlgebraRationalPolynomial,
    type AlgebraRationalPolynomialRing
} from './package_algebra';

export const ALGEBRA_GOAL_SOURCE_PROFILE = Object.freeze({
    revision: 'emdash-algebra-goal-source-v1',
    computationRevision: 'emdash-algebra-goal-computation-v1',
    coefficientField: 'Q', maximumVariables: 4, maximumGenerators: 8,
    maximumInputTerms: 256, maximumResultTerms: 4096,
    maximumCoefficientCharacters: 2048, maximumExponent: 4096,
    engine: 'native-typescript-buchberger-reference',
    performsIo: false, invokesCore: false, automaticCertification: false
} as const);

export class AlgebraGoalError extends Error {
    constructor(public readonly code: string, message: string) {
        super(message); this.name = 'AlgebraGoalError';
    }
}

export interface AlgebraGoalTermSource {
    readonly coefficient: string;
    readonly exponents: readonly string[];
}
export interface AlgebraGoalPolynomialSource {
    readonly name: string;
    readonly terms: readonly AlgebraGoalTermSource[];
}
export interface AlgebraGoalSource {
    readonly revision: typeof ALGEBRA_GOAL_SOURCE_PROFILE.revision;
    readonly title: string;
    readonly ring: {
        readonly field: 'Q';
        readonly variables: readonly string[];
        readonly order: AlgebraMonomialOrder;
    };
    readonly generators: readonly AlgebraGoalPolynomialSource[];
    readonly query: AlgebraGoalPolynomialSource;
}

const fail = (message: string): never => { throw new AlgebraGoalError('INVALID_SOURCE', message); };
export function algebraGoalRecord(value: unknown, keys: readonly string[], path: string): Record<string, unknown> {
    if (!value || typeof value !== 'object' || Array.isArray(value)) return fail(`${path} must be an object`);
    if (Object.keys(value).some(key => !keys.includes(key))) return fail(`${path} has an unknown field`);
    return value as Record<string, unknown>;
}
const text = (value: unknown, path: string, maximum = 1024): string => {
    if (typeof value !== 'string' || !value.trim() || value.length > maximum) return fail(`Invalid ${path}`);
    return value;
};
const name = (value: unknown, path: string): string => {
    const result = text(value, path, 64);
    if (!/^[A-Za-z][A-Za-z0-9_]*$/u.test(result)) return fail(`${path} must be a simple mathematical name`);
    return result;
};

export function algebraGoalPolynomialTerms(polynomial: AlgebraRationalPolynomial): readonly AlgebraGoalTermSource[] {
    // The polynomial owner supplies exact coefficient/exponent spelling.
    const serialized = JSON.parse(serializeAlgebraPolynomial(polynomial)) as { terms: AlgebraGoalTermSource[] };
    return Object.freeze(serialized.terms.map(term => Object.freeze({
        coefficient: term.coefficient, exponents: Object.freeze([...term.exponents])
    })));
}

export function algebraGoalPolynomialFromTerms(
    ring: AlgebraRationalPolynomialRing, input: unknown,
    maximumTerms: number = ALGEBRA_GOAL_SOURCE_PROFILE.maximumResultTerms
): AlgebraRationalPolynomial {
    if (!Array.isArray(input) || input.length > maximumTerms) return fail('Polynomial term limit exceeded');
    const terms = input.map((item, index) => {
        const term = algebraGoalRecord(item, ['coefficient', 'exponents'], `terms[${index}]`);
        const coefficient = text(term.coefficient, 'coefficient', ALGEBRA_GOAL_SOURCE_PROFILE.maximumCoefficientCharacters);
        if (!Array.isArray(term.exponents) || term.exponents.length !== ring.variables.length) {
            return fail('One exact exponent is required per ordered variable');
        }
        const exponents = term.exponents.map(value => {
            if (typeof value !== 'string' || !/^(0|[1-9][0-9]{0,3})$/u.test(value) ||
                BigInt(value) > BigInt(ALGEBRA_GOAL_SOURCE_PROFILE.maximumExponent)) return fail('Invalid bounded exponent');
            return value;
        });
        return { coefficient, exponents };
    });
    return algebraPolynomial(ring, terms);
}

export function normalizeAlgebraGoalSource(value: unknown): AlgebraGoalSource {
    const source = algebraGoalRecord(value, ['revision', 'title', 'ring', 'generators', 'query'], 'source');
    if (source.revision !== ALGEBRA_GOAL_SOURCE_PROFILE.revision) return fail('Unsupported source revision');
    const ringSource = algebraGoalRecord(source.ring, ['field', 'variables', 'order'], 'ring');
    if (ringSource.field !== 'Q') return fail('This workspace supports exact rational coefficients (Q)');
    if (!Array.isArray(ringSource.variables) || ringSource.variables.length < 1 ||
        ringSource.variables.length > ALGEBRA_GOAL_SOURCE_PROFILE.maximumVariables) return fail('Expected 1–4 ordered variables');
    const variables = ringSource.variables.map((value, i) => name(value, `variables[${i}]`));
    if (!['lex', 'grlex', 'grevlex'].includes(String(ringSource.order))) return fail('Unsupported monomial order');
    const order = ringSource.order as AlgebraMonomialOrder;
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, variables, order);
    if (!Array.isArray(source.generators) || !source.generators.length ||
        source.generators.length > ALGEBRA_GOAL_SOURCE_PROFILE.maximumGenerators) return fail('Expected 1–8 ideal generators');
    const normalizePolynomial = (value: unknown, label: string): AlgebraGoalPolynomialSource => {
        const polynomial = algebraGoalRecord(value, ['name', 'terms'], label);
        return Object.freeze({ name: name(polynomial.name, `${label}.name`), terms: algebraGoalPolynomialTerms(
            algebraGoalPolynomialFromTerms(ring, polynomial.terms, ALGEBRA_GOAL_SOURCE_PROFILE.maximumInputTerms)
        ) });
    };
    const generators = source.generators.map((p, i) => normalizePolynomial(p, `generators[${i}]`));
    const query = normalizePolynomial(source.query, 'query');
    const names = [...generators, query].map(p => p.name);
    if (new Set(names).size !== names.length) return fail('Generator and query names must be distinct');
    return Object.freeze({
        revision: ALGEBRA_GOAL_SOURCE_PROFILE.revision,
        title: text(source.title, 'title'),
        ring: Object.freeze({ field: 'Q', variables: Object.freeze(variables), order }),
        generators: Object.freeze(generators), query
    });
}

export const serializeAlgebraGoalSource = (source: AlgebraGoalSource): string =>
    JSON.stringify(normalizeAlgebraGoalSource(source), null, 2) + '\n';

export function algebraGoalInput(source: AlgebraGoalSource): AlgebraIdealWitnessInput {
    const normalized = normalizeAlgebraGoalSource(source);
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, normalized.ring.variables, normalized.ring.order);
    return Object.freeze({
        ideal: algebraPolynomialIdeal(ring, normalized.generators.map(p => algebraGoalPolynomialFromTerms(ring, p.terms))),
        polynomial: algebraGoalPolynomialFromTerms(ring, normalized.query.terms)
    });
}

/** TypeScript builders can emit the same inert source accepted by the file/CLI/MCP paths. */
export function createAlgebraGoalSource(input: AlgebraIdealWitnessInput, options: {
    readonly title: string; readonly generatorNames?: readonly string[]; readonly queryName?: string;
}): AlgebraGoalSource {
    const normalized = normalizeAlgebraIdealWitnessInput(input);
    if (options.generatorNames && options.generatorNames.length !== normalized.ideal.generators.length) {
        return fail('Generator name count differs from the ideal');
    }
    return normalizeAlgebraGoalSource({
        revision: ALGEBRA_GOAL_SOURCE_PROFILE.revision, title: options.title,
        ring: { field: 'Q', variables: normalized.ideal.ring.variables, order: normalized.ideal.ring.monomialOrder },
        generators: normalized.ideal.generators.map((p, i) => ({
            name: options.generatorNames?.[i] ?? `f${i + 1}`, terms: algebraGoalPolynomialTerms(p)
        })),
        query: { name: options.queryName ?? 'g', terms: algebraGoalPolynomialTerms(normalized.polynomial) }
    });
}

export function createAlgebraGoalExampleSource(): AlgebraGoalSource {
    return normalizeAlgebraGoalSource({
        revision: ALGEBRA_GOAL_SOURCE_PROFILE.revision,
        title: 'Compute a polynomial relation, view its curves, and reuse it in a complex',
        ring: { field: 'Q', variables: ['x', 'y'], order: 'lex' },
        generators: [
            { name: 'f1', terms: [{ coefficient: '-1', exponents: ['2', '0'] }, { coefficient: '1', exponents: ['0', '1'] }] },
            { name: 'f2', terms: [{ coefficient: '1', exponents: ['1', '1'] }, { coefficient: '-1', exponents: ['0', '0'] }] }
        ],
        query: { name: 'g', terms: [{ coefficient: '1', exponents: ['3', '0'] }, { coefficient: '-1', exponents: ['0', '0'] }] }
    });
}

export interface AlgebraGoalComputation {
    readonly revision: typeof ALGEBRA_GOAL_SOURCE_PROFILE.computationRevision;
    readonly engine: typeof ALGEBRA_GOAL_SOURCE_PROFILE.engine;
    readonly mathematicalSource: string;
    readonly member: boolean;
    readonly coefficients: readonly (readonly AlgebraGoalTermSource[])[];
    readonly remainder: readonly AlgebraGoalTermSource[];
    readonly basis: readonly (readonly AlgebraGoalTermSource[])[];
}

export function computeAlgebraGoal(source: AlgebraGoalSource): AlgebraGoalComputation {
    const input = algebraGoalInput(source);
    const basis = algebraGroebnerBasis(input.ideal, {
        maximumBasisSize: 32, maximumPairs: 256,
        maximumReductionStepsPerPair: 10_000, maximumTotalReductionSteps: 20_000
    });
    const result = algebraIdealMembership(input.polynomial, basis, 20_000);
    if (result.member) checkAlgebraIdealWitness(input, {
        source: algebraIdealWitnessSource(input), coefficients: result.coefficients
    });
    return Object.freeze({
        revision: ALGEBRA_GOAL_SOURCE_PROFILE.computationRevision,
        engine: ALGEBRA_GOAL_SOURCE_PROFILE.engine,
        mathematicalSource: algebraIdealWitnessSource(input), member: result.member,
        coefficients: Object.freeze(result.coefficients.map(algebraGoalPolynomialTerms)),
        remainder: algebraGoalPolynomialTerms(result.remainder),
        basis: Object.freeze(result.basis.basis.map(algebraGoalPolynomialTerms))
    });
}

/** A persisted positive result is checked as exact mathematical data, never as proof authority. */
export function checkAlgebraGoalRelation(source: AlgebraGoalSource, value: unknown) {
    const result = algebraGoalRecord(value,
        ['revision', 'engine', 'mathematicalSource', 'member', 'coefficients', 'remainder', 'basis'], 'computation');
    if (result.revision !== ALGEBRA_GOAL_SOURCE_PROFILE.computationRevision ||
        result.engine !== ALGEBRA_GOAL_SOURCE_PROFILE.engine || result.member !== true) {
        throw new AlgebraGoalError('NO_POSITIVE_RELATION', 'Internal reuse requires a retained positive native relation');
    }
    const input = algebraGoalInput(source), ring = input.ideal.ring;
    if (result.mathematicalSource !== algebraIdealWitnessSource(input)) {
        throw new AlgebraGoalError('STALE_RESULT', 'The retained relation belongs to a different mathematical input');
    }
    if (!Array.isArray(result.coefficients) || result.coefficients.length !== input.ideal.generators.length) {
        return fail('One retained coefficient is required per generator');
    }
    const coefficients = result.coefficients.map(p => algebraGoalPolynomialFromTerms(ring, p));
    const remainder = algebraGoalPolynomialFromTerms(ring, result.remainder);
    if (remainder.terms.length) return fail('A positive relation must have zero remainder');
    return checkAlgebraIdealWitness(input, { source: algebraIdealWitnessSource(input), coefficients });
}

export function describeAlgebraGoal(source: AlgebraGoalSource) {
    const normalized = normalizeAlgebraGoalSource(source), input = algebraGoalInput(normalized);
    return Object.freeze({
        title: normalized.title, ring: `Q[${normalized.ring.variables.join(',')}]`,
        generators: input.ideal.generators.map((p, i) => ({ name: normalized.generators[i].name, polynomial: algebraPolynomialText(p) })),
        query: { name: normalized.query.name, polynomial: algebraPolynomialText(input.polynomial) }
    });
}
