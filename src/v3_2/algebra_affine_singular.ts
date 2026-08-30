/** Real/injected Singular differential comparisons for affine computations. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import {
    AlgebraPolynomialIdeal,
    algebraGroebnerBasis,
    algebraIdealMembership
} from './algebra_ideal';
import {
    AlgebraPolynomial,
    AlgebraPolynomialRing,
    algebraPolynomialSubtract,
    algebraPolynomialText
} from './algebra_polynomial';
import {
    AlgebraPolynomialQuotientRing,
    AlgebraQuotientElement,
    algebraQuotientEquals
} from './algebra_quotient';
import { algebraIdealSaturate } from './algebra_ideal_geometry';
import {
    AlgebraOracleError,
    AlgebraOracleProcessRequest,
    AlgebraOracleTransport
} from './algebra_oracle';

export const ALGEBRA_AFFINE_SINGULAR_PROFILE = Object.freeze({
    revision: 'emdash-affine-singular-differential-v1' as const,
    authority: 'non-authoritative-differential-comparison' as const,
    executable: 'Singular' as const,
    nodeBuiltinDependency: false as const,
    performsIo: true as const
});

const order = (ring: AlgebraPolynomialRing<AlgebraParent, AlgebraElement, unknown>):
    'lp' | 'Dp' | 'dp' => ring.monomialOrder === 'lex'
        ? 'lp'
        : ring.monomialOrder === 'grlex' ? 'Dp' : 'dp';

const variables = (ring: AlgebraPolynomialRing<AlgebraParent, AlgebraElement, unknown>):
    string => ring.variables.length === 0 ? 'emdash_dummy' : ring.variables.join(',');

const generators = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    ideal: AlgebraPolynomialIdeal<P, C, I>
): string => ideal.generators.length === 0
    ? '0'
    : ideal.generators.map(algebraPolynomialText).join(',');

export function singularIdealMembershipScript<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(ideal: AlgebraPolynomialIdeal<P, C, I>, polynomial: AlgebraPolynomial<P, C, I>):
    string {
    return [
        `ring emdash_r = 0,(${variables(ideal.ring as never)}),${order(ideal.ring as never)};`,
        `ideal emdash_i = ${generators(ideal)};`,
        'ideal emdash_g = std(emdash_i);',
        `poly emdash_p = ${algebraPolynomialText(polynomial)};`,
        'poly emdash_n = reduce(emdash_p,emdash_g);',
        'if (emdash_n == 0) { print("EMDASH_IDEAL_MEMBER:1"); }',
        'else { print("EMDASH_IDEAL_MEMBER:0"); }',
        'quit;'
    ].join('\n') + '\n';
}

export function singularSaturationMembershipScript<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ideal: AlgebraPolynomialIdeal<P, C, I>,
    element: AlgebraPolynomial<P, C, I>,
    candidate: AlgebraPolynomial<P, C, I>
): string {
    return [
    `ring emdash_r = 0,(${variables(ideal.ring as never)}),${order(ideal.ring as never)};`,
    `ideal emdash_i = ${generators(ideal)};`,
    `poly emdash_f = ${algebraPolynomialText(element)};`,
    `poly emdash_p = ${algebraPolynomialText(candidate)};`,
    `ring emdash_e = 0,(emdash_t,${variables(ideal.ring as never)}),lp;`,
    'ideal emdash_j = imap(emdash_r,emdash_i),1-emdash_t*imap(emdash_r,emdash_f);',
    'ideal emdash_g = std(emdash_j);',
    'poly emdash_q = imap(emdash_r,emdash_p);',
    'poly emdash_n = reduce(emdash_q,emdash_g);',
    'if (emdash_n == 0) { print("EMDASH_IDEAL_MEMBER:1"); }',
    'else { print("EMDASH_IDEAL_MEMBER:0"); }',
    'quit;'
    ].join('\n') + '\n';
}

export interface AlgebraAffineSingularComparison {
    readonly kind: 'algebra-affine-singular-comparison';
    readonly subject: 'ideal-membership' | 'quotient-equality' | 'saturation-membership';
    readonly native: boolean;
    readonly singular: boolean;
    readonly agrees: boolean;
    readonly request: AlgebraOracleProcessRequest;
}

const execute = async (
    subject: AlgebraAffineSingularComparison['subject'],
    native: boolean,
    script: string,
    transport: AlgebraOracleTransport
): Promise<AlgebraAffineSingularComparison> => {
    const request = Object.freeze({
        executable: ALGEBRA_AFFINE_SINGULAR_PROFILE.executable,
        args: Object.freeze(['-q']),
        stdin: script,
        timeoutMilliseconds: 30_000,
        maximumOutputBytes: 1_000_000
    });
    const result = await transport.execute(request);
    if (result.exitCode !== 0) {
        throw new AlgebraOracleError(
            'PROCESS_FAILED',
            result.stderr || `Singular exited with ${result.exitCode}`
        );
    }
    const match = /EMDASH_IDEAL_MEMBER:([01])/u.exec(result.stdout);
    if (!match) {
        throw new AlgebraOracleError(
            'MALFORMED_OUTPUT',
            'Singular output omitted the ideal-membership marker'
        );
    }
    const singular = match[1] === '1';
    return Object.freeze({
        kind: 'algebra-affine-singular-comparison',
        subject,
        native,
        singular,
        agrees: native === singular,
        request
    });
};

export async function compareIdealMembershipWithSingular<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ideal: AlgebraPolynomialIdeal<P, C, I>,
    polynomial: AlgebraPolynomial<P, C, I>,
    transport: AlgebraOracleTransport
): Promise<AlgebraAffineSingularComparison> {
    const native = algebraIdealMembership(
        polynomial,
        algebraGroebnerBasis(ideal)
    ).member;
    return execute(
        'ideal-membership',
        native,
        singularIdealMembershipScript(ideal, polynomial),
        transport
    );
}

export async function compareQuotientEqualityWithSingular<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    quotient: AlgebraPolynomialQuotientRing<P, C, I>,
    left: AlgebraQuotientElement<P, C, I>,
    right: AlgebraQuotientElement<P, C, I>,
    transport: AlgebraOracleTransport
): Promise<AlgebraAffineSingularComparison> {
    const difference = algebraPolynomialSubtract(
        left.representative,
        right.representative
    );
    return execute(
        'quotient-equality',
        algebraQuotientEquals(left, right),
        singularIdealMembershipScript(quotient.ideal, difference),
        transport
    );
}

export async function compareSaturationMembershipWithSingular<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ideal: AlgebraPolynomialIdeal<P, C, I>,
    element: AlgebraPolynomial<P, C, I>,
    candidate: AlgebraPolynomial<P, C, I>,
    transport: AlgebraOracleTransport
): Promise<AlgebraAffineSingularComparison> {
    const saturation = algebraIdealSaturate(ideal, element);
    const native = algebraIdealMembership(
        candidate,
        algebraGroebnerBasis(saturation.ideal)
    ).member;
    return execute(
        'saturation-membership',
        native,
        singularSaturationMembershipScript(ideal, element, candidate),
        transport
    );
}
