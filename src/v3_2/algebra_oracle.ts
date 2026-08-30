/** Opt-in external differential oracle contracts and a Singular adapter. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import {
    AlgebraAlgorithmIdentity,
    AlgebraEngine,
    AlgebraOperation,
    AlgebraRuntimeSchema,
    algebraAlgorithmIdentity,
    algebraEngineIdentity,
    algebraEngineSupported,
    algebraEngineUnsupported,
    computeAlgebraOperation,
    defineAlgebraEngine,
    defineAlgebraOperation,
    defineAlgebraRuntimeSchema
} from './algebra_engine';
import {
    AlgebraPolynomialIdeal,
    algebraPolynomialIdealSchema
} from './algebra_ideal';
import {
    AlgebraPolynomial,
    AlgebraPolynomialRing,
    algebraPolynomialSchema,
    algebraPolynomialText
} from './algebra_polynomial';
import { algebraIdealRadicalMembership } from './algebra_ideal_geometry';
import {
    AlgebraReferenceImplementation,
    createAlgebraTypeScriptReferenceEngine,
    defineAlgebraReferenceImplementation
} from './algebra_reference_engine';

export const ALGEBRA_ORACLE_PROFILE = Object.freeze({
    revision: 'emdash-algebra-differential-oracle-v1' as const,
    authority: 'non-authoritative-differential-comparison' as const,
    provider: 'Singular' as const,
    defaultExecutable: 'Singular' as const,
    nodeBuiltinDependency: false as const,
    performsIo: true as const
});

export interface AlgebraRadicalMembershipDecisionInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly ideal: AlgebraPolynomialIdeal<P, C, I>;
    readonly element: AlgebraPolynomial<P, C, I>;
}

export interface AlgebraRadicalMembershipDecision {
    readonly kind: 'algebra-radical-membership-decision';
    readonly member: boolean;
    readonly provider: 'native-typescript' | 'singular-oracle';
}

export interface AlgebraRadicalMembershipOperationBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly inputSchema: AlgebraRuntimeSchema<
        AlgebraRadicalMembershipDecisionInput<P, C, I>
    >;
    readonly outputSchema: AlgebraRuntimeSchema<AlgebraRadicalMembershipDecision>;
    readonly operation: AlgebraOperation<
        AlgebraRadicalMembershipDecisionInput<P, C, I>,
        AlgebraRadicalMembershipDecision
    >;
    readonly nativeImplementation: AlgebraReferenceImplementation;
}

export function algebraRadicalMembershipOperation<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(ring: AlgebraPolynomialRing<P, C, I>):
    AlgebraRadicalMembershipOperationBundle<P, C, I> {
    const idealSchema = algebraPolynomialIdealSchema(ring);
    const polynomialSchema = algebraPolynomialSchema(ring);
    const inputSchema = defineAlgebraRuntimeSchema<
        AlgebraRadicalMembershipDecisionInput<P, C, I>
    >({
        id: `algebra.oracle.radical-membership-input/${ring.identity.id}`,
        revision: ring.identity.revision,
        normalize(value: unknown, path: string) {
            if (typeof value !== 'object' || value === null) {
                throw new Error(`radical-membership input expected at ${path}`);
            }
            const input = value as Record<string, unknown>;
            return Object.freeze({
                ideal: idealSchema.normalize(input.ideal, `${path}.ideal`),
                element: polynomialSchema.normalize(input.element, `${path}.element`)
            });
        }
    });
    const outputSchema = defineAlgebraRuntimeSchema<AlgebraRadicalMembershipDecision>({
        id: `algebra.oracle.radical-membership-decision/${ring.identity.id}`,
        revision: ring.identity.revision,
        normalize(value: unknown, path: string) {
            if (typeof value !== 'object' || value === null ||
                (value as { kind?: unknown }).kind !== 'algebra-radical-membership-decision' ||
                typeof (value as { member?: unknown }).member !== 'boolean' ||
                !['native-typescript', 'singular-oracle'].includes(
                    (value as { provider?: string }).provider ?? ''
                )) throw new Error(`radical-membership decision expected at ${path}`);
            const decision = value as AlgebraRadicalMembershipDecision;
            return Object.freeze({ ...decision });
        }
    });
    const operation = defineAlgebraOperation({
        id: `algebra.radical-membership-decision/${ring.identity.id}`,
        revision: ring.identity.revision,
        input: inputSchema,
        output: outputSchema
    });
    const nativeImplementation = defineAlgebraReferenceImplementation({
        operation,
        algorithm: algebraAlgorithmIdentity('algebra.typescript-reference/radical-membership', 'v1'),
        execute: input => Object.freeze({
            kind: 'algebra-radical-membership-decision' as const,
            member: algebraIdealRadicalMembership(input.ideal, input.element).member,
            provider: 'native-typescript' as const
        })
    });
    return Object.freeze({ inputSchema, outputSchema, operation, nativeImplementation });
}

export interface AlgebraOracleProcessRequest {
    readonly executable: string;
    readonly args: readonly string[];
    readonly stdin: string;
    readonly timeoutMilliseconds: number;
    readonly maximumOutputBytes: number;
}

export interface AlgebraOracleProcessResult {
    readonly exitCode: number;
    readonly stdout: string;
    readonly stderr: string;
}

export interface AlgebraOracleTransport {
    execute(request: AlgebraOracleProcessRequest): Promise<AlgebraOracleProcessResult>;
}

const singularOrder = (ring: AlgebraPolynomialRing<AlgebraParent, AlgebraElement, unknown>):
    'lp' | 'Dp' | 'dp' => ring.monomialOrder === 'lex'
        ? 'lp'
        : ring.monomialOrder === 'grlex' ? 'Dp' : 'dp';

export function singularRadicalMembershipScript<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: AlgebraRadicalMembershipDecisionInput<P, C, I>): string {
    const ring = input.ideal.ring;
    const variables = ring.variables.length === 0 ? 'emdash_dummy' : ring.variables.join(',');
    const generators = input.ideal.generators.length === 0
        ? '0'
        : input.ideal.generators.map(algebraPolynomialText).join(',');
    const element = algebraPolynomialText(input.element);
    return [
        `ring emdash_r = 0,(${variables}),${singularOrder(ring as never)};`,
        `ideal emdash_i = ${generators};`,
        `poly emdash_f = ${element};`,
        '// Recreate with an explicit Rabinowitsch variable.',
        `ring emdash_e = 0,(emdash_t,${variables}),lp;`,
        `ideal emdash_j = imap(emdash_r,emdash_i),1-emdash_t*imap(emdash_r,emdash_f);`,
        'ideal emdash_b = std(emdash_j);',
        'poly emdash_n = reduce(1,emdash_b);',
        'if (emdash_n == 0) { print("EMDASH_RADICAL_MEMBER:1"); }',
        'else { print("EMDASH_RADICAL_MEMBER:0"); }',
        'quit;'
    ].join('\n') + '\n';
}

export class AlgebraOracleError extends Error {
    constructor(
        public readonly code: 'PROCESS_FAILED' | 'MALFORMED_OUTPUT' | 'CANCELLED',
        message: string
    ) {
        super(message);
        this.name = 'AlgebraOracleError';
    }
}

export function createSingularRadicalMembershipEngine<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    bundle: AlgebraRadicalMembershipOperationBundle<P, C, I>,
    transport: AlgebraOracleTransport,
    executable = ALGEBRA_ORACLE_PROFILE.defaultExecutable
): AlgebraEngine {
    const engineIdentity = algebraEngineIdentity('algebra.oracle.singular', 'v1');
    const algorithm: AlgebraAlgorithmIdentity = algebraAlgorithmIdentity(
        'algebra.oracle.singular/radical-membership',
        'v1'
    );
    return defineAlgebraEngine({
        id: engineIdentity.id,
        revision: engineIdentity.revision,
        support: operation => {
            const sameContract = operation.identity.id === bundle.operation.identity.id &&
                operation.identity.revision === bundle.operation.identity.revision &&
                operation.input.identity.id === bundle.operation.input.identity.id &&
                operation.output.identity.id === bundle.operation.output.identity.id;
            return sameContract
                ? algebraEngineSupported({
                    operation: operation.identity,
                    engine: engineIdentity,
                    algorithms: [algorithm]
                })
                : algebraEngineUnsupported({
                    operation: operation.identity,
                    engine: engineIdentity,
                    diagnostics: [{
                        code: 'ORACLE_OPERATION_UNSUPPORTED',
                        severity: 'info',
                        message: 'Singular oracle supports only radical membership'
                    }]
                });
        },
        async compute(operation, input, _algorithm, context) {
            if (context.cancellation?.requested()) {
                throw new AlgebraOracleError('CANCELLED',
                    context.cancellation.reason?.() ?? 'Oracle cancelled');
            }
            const result = await transport.execute({
                executable,
                args: ['-q'],
                stdin: singularRadicalMembershipScript(input as never),
                timeoutMilliseconds: 30_000,
                maximumOutputBytes: 1_000_000
            });
            if (context.cancellation?.requested()) {
                throw new AlgebraOracleError('CANCELLED',
                    context.cancellation.reason?.() ?? 'Oracle cancelled');
            }
            if (result.exitCode !== 0) {
                throw new AlgebraOracleError('PROCESS_FAILED', result.stderr ||
                    `Singular exited with ${result.exitCode}`);
            }
            const match = /EMDASH_RADICAL_MEMBER:([01])/u.exec(result.stdout);
            if (!match) throw new AlgebraOracleError('MALFORMED_OUTPUT',
                'Singular output omitted the radical-membership marker');
            return {
                operation: operation.identity,
                engine: engineIdentity,
                algorithm,
                quality: 'exact',
                value: {
                    kind: 'algebra-radical-membership-decision',
                    member: match[1] === '1',
                    provider: 'singular-oracle'
                },
                diagnostics: [{
                    code: 'EXTERNAL_ORACLE',
                    severity: 'info',
                    message: 'Non-authoritative Singular differential result'
                }]
            };
        }
    });
}

export interface AlgebraOracleComparison {
    readonly kind: 'algebra-oracle-comparison';
    readonly native: AlgebraRadicalMembershipDecision;
    readonly oracle: AlgebraRadicalMembershipDecision;
    readonly agrees: boolean;
}

export async function compareRadicalMembershipWithSingular<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    bundle: AlgebraRadicalMembershipOperationBundle<P, C, I>,
    input: AlgebraRadicalMembershipDecisionInput<P, C, I>,
    transport: AlgebraOracleTransport
): Promise<AlgebraOracleComparison> {
    const nativeEngine = createAlgebraTypeScriptReferenceEngine({
        implementations: [bundle.nativeImplementation]
    });
    const oracleEngine = createSingularRadicalMembershipEngine(bundle, transport);
    const [native, oracle] = await Promise.all([
        computeAlgebraOperation({ engine: nativeEngine, operation: bundle.operation, input }),
        computeAlgebraOperation({ engine: oracleEngine, operation: bundle.operation, input })
    ]);
    return Object.freeze({
        kind: 'algebra-oracle-comparison',
        native: native.value,
        oracle: oracle.value,
        agrees: native.value.member === oracle.value.member
    });
}
