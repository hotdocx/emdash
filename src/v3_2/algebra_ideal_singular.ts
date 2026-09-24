/** Bounded Q-polynomial witness exchange; formal proof adoption is separate. */

import { AlgebraComputationContextInput } from './algebra_engine';
import {
    AlgebraOracleError, AlgebraOracleTransport
} from './algebra_oracle';
import { algebraPolynomial } from './algebra_polynomial';
import {
    AlgebraIdealWitnessInput, AlgebraRationalPolynomial,
    algebraIdealWitnessSource, checkAlgebraIdealWitness,
    normalizeAlgebraIdealWitnessInput
} from './algebra_ideal_witness';

export const ALGEBRA_IDEAL_SINGULAR_PROFILE = Object.freeze({
    revision: 'emdash-singular-ideal-witness-v1',
    timeoutMilliseconds: 30_000,
    maximumOutputBytes: 1_000_000,
    maximumTerms: 10_000,
    maximumExponent: 4096n,
    maximumGenerators: 64,
    maximumVariables: 16,
    negativeAuthority: 'external-observation',
    positiveAuthority: 'exact-polynomial-arithmetic',
    nodeBuiltinDependency: false,
    addsCoreProof: false
} as const);

const malformed = (message: string): never => {
    throw new AlgebraOracleError('MALFORMED_OUTPUT', message);
};

const boundedInput = (input: AlgebraIdealWitnessInput): AlgebraIdealWitnessInput => {
    const value = normalizeAlgebraIdealWitnessInput(input);
    const { maximumVariables, maximumGenerators, maximumTerms, maximumExponent } =
        ALGEBRA_IDEAL_SINGULAR_PROFILE;
    const polynomials = [value.polynomial, ...value.ideal.generators];
    if (value.ideal.ring.variables.length < 1 ||
        value.ideal.ring.variables.length > maximumVariables ||
        value.ideal.generators.length > maximumGenerators ||
        polynomials.reduce((sum, p) => sum + p.terms.length, 0) > maximumTerms ||
        polynomials.some(p => p.terms.some(t =>
            t.monomial.exponents.some(e => e > maximumExponent)))) {
        throw new Error('Input exceeds the bounded Singular witness profile');
    }
    return value;
};

/** Rename variables by position, so user names cannot collide with Singular. */
const polynomialText = (polynomial: AlgebraRationalPolynomial): string =>
    polynomial.terms.map(term => [
        `(${term.coefficient.numerator}/${term.coefficient.denominator})`,
        ...term.monomial.exponents.map((exponent, index) => `v${index + 1}^${exponent}`)
    ].join('*')).join('+') || '0';

/** lift(I,(g)) returns original-generator coefficients in global polynomial orders. */
export function singularIdealWitnessScript(input: AlgebraIdealWitnessInput): string {
    const { ideal, polynomial } = boundedInput(input);
    const variables = ideal.ring.variables.map((_, index) => `v${index + 1}`);
    const order = { lex: 'lp', grlex: 'Dp', grevlex: 'dp' }[ideal.ring.monomialOrder];
    return [
        `ring emdash_r=0,(${variables.join(',')}),${order};`,
        `ideal emdash_i=${ideal.generators.map(polynomialText).join(',') || '0'};`,
        `poly emdash_g=${polynomialText(polynomial)};`,
        'print("EMDASH_WITNESS_V1");',
        'print("VERSION:"+string(system("version")));',
        'if(reduce(emdash_g,std(emdash_i))!=0){print("MEMBER:0");}',
        'else {',
        'print("MEMBER:1");',
        'matrix emdash_c=lift(emdash_i,ideal(emdash_g));',
        'int emdash_j; poly emdash_p;',
        `for(emdash_j=1;emdash_j<=${ideal.generators.length};emdash_j++){`,
        'print("COEFFICIENT:"+string(emdash_j-1));',
        'emdash_p=emdash_c[emdash_j,1];',
        'while(emdash_p!=0){',
        'print("TERM:"+string(leadcoef(emdash_p))+":"+string(leadexp(emdash_p)));',
        'emdash_p=emdash_p-lead(emdash_p);',
        '}',
        'print("END_COEFFICIENT");',
        '}',
        '}',
        'print("END_WITNESS");',
        'quit;'
    ].join('\n') + '\n';
}

/** Parse coefficient/exponent data, never executable text or displayed formulas. */
export function parseSingularIdealWitness(input: AlgebraIdealWitnessInput, stdout: string) {
    const normalized = boundedInput(input);
    if (new TextEncoder().encode(stdout).length >
        ALGEBRA_IDEAL_SINGULAR_PROFILE.maximumOutputBytes) {
        return malformed('Singular witness output exceeds its byte limit');
    }
    const lines = stdout.trim().split(/\r?\n/u);
    let cursor = 0;
    const expect = (line: string): void => {
        if (lines[cursor++] !== line) malformed(`Expected ${line} in Singular output`);
    };
    expect('EMDASH_WITNESS_V1');
    const version = /^VERSION:([0-9]+)$/u.exec(lines[cursor++] ?? '')?.[1];
    if (!version) return malformed('Missing Singular version');
    const membership = lines[cursor++];
    if (membership !== 'MEMBER:0' && membership !== 'MEMBER:1') {
        return malformed('Missing or invalid membership result');
    }
    const coefficients: AlgebraRationalPolynomial[] = [];
    let termCount = 0;
    if (membership === 'MEMBER:1') {
        for (let index = 0; index < normalized.ideal.generators.length; index++) {
            expect(`COEFFICIENT:${index}`);
            const terms: { coefficient: string; exponents: string[] }[] = [];
            while (lines[cursor] !== 'END_COEFFICIENT') {
                const match = /^TERM:(-?[0-9]+(?:\/[1-9][0-9]*)?):([0-9, ]+)$/u
                    .exec(lines[cursor++] ?? '');
                if (!match || ++termCount > ALGEBRA_IDEAL_SINGULAR_PROFILE.maximumTerms) {
                    return malformed('Malformed or excessive Singular coefficient terms');
                }
                const exponents = match[2].split(',').map(value => value.trim());
                if (exponents.length !== normalized.ideal.ring.variables.length ||
                    exponents.some(value => !/^(0|[1-9][0-9]*)$/u.test(value) ||
                        BigInt(value) > ALGEBRA_IDEAL_SINGULAR_PROFILE.maximumExponent)) {
                    return malformed('Wrong arity or out-of-range Singular exponents');
                }
                terms.push({ coefficient: match[1], exponents });
            }
            expect('END_COEFFICIENT');
            coefficients.push(algebraPolynomial(normalized.ideal.ring, terms));
        }
    }
    expect('END_WITNESS');
    if (cursor !== lines.length) return malformed('Unexpected trailing Singular output');
    const source = algebraIdealWitnessSource(normalized);
    return membership === 'MEMBER:1'
        ? Object.freeze({
            kind: 'witness' as const, version, source,
            witness: checkAlgebraIdealWitness(normalized, { source, coefficients })
        })
        : Object.freeze({
            kind: 'nonmembership-observation' as const, version, source,
            authority: 'external-observation' as const
        });
}

export async function computeSingularIdealWitness(
    input: AlgebraIdealWitnessInput,
    transport: AlgebraOracleTransport,
    options: {
        readonly executable?: string;
        readonly context?: AlgebraComputationContextInput;
    } = {}
) {
    const normalized = boundedInput(input);
    const checkCancellation = (): void => {
        if (options.context?.cancellation?.requested()) {
            throw new AlgebraOracleError('CANCELLED',
                options.context.cancellation.reason?.() ?? 'Singular witness cancelled');
        }
    };
    checkCancellation();
    const request = Object.freeze({
        executable: options.executable ?? 'Singular',
        args: Object.freeze(['-q', '--no-rc']),
        stdin: singularIdealWitnessScript(normalized),
        timeoutMilliseconds: ALGEBRA_IDEAL_SINGULAR_PROFILE.timeoutMilliseconds,
        maximumOutputBytes: ALGEBRA_IDEAL_SINGULAR_PROFILE.maximumOutputBytes
    });
    const result = await transport.execute(request);
    checkCancellation();
    if (result.exitCode !== 0 || result.stderr.trim() !== '') {
        throw new AlgebraOracleError('PROCESS_FAILED',
            result.stderr || `Singular exited with ${result.exitCode}`);
    }
    return Object.freeze({
        ...parseSingularIdealWitness(normalized, result.stdout),
        request,
        backend: Object.freeze({ executable: request.executable,
            adapterRevision: ALGEBRA_IDEAL_SINGULAR_PROFILE.revision })
    });
}
