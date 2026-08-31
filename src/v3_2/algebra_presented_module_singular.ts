/** Non-authoritative Singular comparison for presented-module zero decisions. */

import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
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
    AlgebraPolynomialRing,
    algebraPolynomialText
} from './algebra_polynomial';
import {
    AlgebraPresentedAlgebraModule,
    AlgebraPresentedAlgebraModuleVector,
    algebraPresentedAlgebraModuleNormalize,
    algebraPresentedAlgebraModuleVectorLift,
    algebraPresentedAlgebraModuleVectorSchema
} from './algebra_presented_module';
import {
    AlgebraOracleError,
    AlgebraOracleTransport
} from './algebra_oracle';
import {
    AlgebraReferenceImplementation,
    createAlgebraTypeScriptReferenceEngine,
    defineAlgebraReferenceImplementation
} from './algebra_reference_engine';

export const ALGEBRA_PRESENTED_MODULE_SINGULAR_PROFILE = Object.freeze({
    revision: 'emdash-presented-module-singular-v1' as const,
    authority: 'non-authoritative-differential-comparison' as const,
    operation: 'presented-module-vector-zero-decision' as const,
    executable: 'Singular' as const,
    nodeBuiltinDependency: false as const,
    performsIo: true as const
});

export interface AlgebraPresentedModuleZeroDecision {
    readonly kind: 'algebra-presented-module-zero-decision';
    readonly zero: boolean;
    readonly provider: 'native-typescript' | 'singular-oracle';
}

export interface AlgebraPresentedModuleZeroOperationBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly module: AlgebraPresentedAlgebraModule<P, C, I>;
    readonly inputSchema: AlgebraRuntimeSchema<
        AlgebraPresentedAlgebraModuleVector<P, C, I>
    >;
    readonly outputSchema: AlgebraRuntimeSchema<AlgebraPresentedModuleZeroDecision>;
    readonly operation: AlgebraOperation<
        AlgebraPresentedAlgebraModuleVector<P, C, I>,
        AlgebraPresentedModuleZeroDecision
    >;
    readonly nativeImplementation: AlgebraReferenceImplementation;
}

export function algebraPresentedModuleZeroOperation<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(module: AlgebraPresentedAlgebraModule<P, C, I>):
    AlgebraPresentedModuleZeroOperationBundle<P, C, I> {
    const inputSchema = algebraPresentedAlgebraModuleVectorSchema(
        module.freeModule
    );
    const outputSchema = defineAlgebraRuntimeSchema<
        AlgebraPresentedModuleZeroDecision
    >({
        id: `algebra.oracle.presented-module-zero/${module.identity.id}`,
        revision: ALGEBRA_PRESENTED_MODULE_SINGULAR_PROFILE.revision,
        normalize(value: unknown, path: string) {
            if (
                typeof value !== 'object' ||
                value === null ||
                (value as { kind?: unknown }).kind !==
                    'algebra-presented-module-zero-decision' ||
                typeof (value as { zero?: unknown }).zero !== 'boolean' ||
                !['native-typescript', 'singular-oracle'].includes(
                    (value as { provider?: string }).provider ?? ''
                )
            ) throw new Error(`presented-module zero decision expected at ${path}`);
            return Object.freeze({ ...(value as AlgebraPresentedModuleZeroDecision) });
        }
    });
    const operation = defineAlgebraOperation({
        id: `algebra.presented-module-zero-decision/${module.identity.id}`,
        revision: ALGEBRA_PRESENTED_MODULE_SINGULAR_PROFILE.revision,
        input: inputSchema,
        output: outputSchema
    });
    const nativeImplementation = defineAlgebraReferenceImplementation({
        operation,
        algorithm: algebraAlgorithmIdentity(
            'algebra.typescript-reference/presented-module-zero',
            'v1'
        ),
        execute: vector => Object.freeze({
            kind: 'algebra-presented-module-zero-decision' as const,
            zero: algebraPresentedAlgebraModuleNormalize(module, vector)
                .membership.member,
            provider: 'native-typescript' as const
        })
    });
    return Object.freeze({
        module,
        inputSchema,
        outputSchema,
        operation,
        nativeImplementation
    });
}

const singularOrder = (
    ring: AlgebraPolynomialRing<AlgebraParent, AlgebraElement, unknown>
): 'lp' | 'Dp' | 'dp' => ring.monomialOrder === 'lex'
    ? 'lp'
    : ring.monomialOrder === 'grlex' ? 'Dp' : 'dp';

const vectorText = (texts: readonly string[]): string => `[${texts.join(',')}]`;

export function singularPresentedModuleZeroScript<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    module: AlgebraPresentedAlgebraModule<P, C, I>,
    vector: AlgebraPresentedAlgebraModuleVector<P, C, I>
): string {
    const ring = module.freeModule.algebra.quotient.polynomialRing;
    const variables = ring.variables.length === 0
        ? 'emdash_dummy'
        : ring.variables.join(',');
    if (module.freeModule.rank === 0) {
        return [
            `ring emdash_r = 0,(${variables}),${singularOrder(ring as never)};`,
            'print("EMDASH_MODULE_ZERO:1");',
            'quit;'
        ].join('\n') + '\n';
    }
    const zeroVector = `[${Array.from(
        { length: module.freeModule.rank },
        () => '0'
    ).join(',')}]`;
    const relationVectors = module.combinedRelations.generators.map(relation =>
        vectorText(relation.components.map(algebraPolynomialText))
    );
    const lifted = algebraPresentedAlgebraModuleVectorLift(vector);
    return [
        `ring emdash_r = 0,(${variables}),${singularOrder(ring as never)};`,
        `module emdash_m = ${relationVectors.join(',') || zeroVector};`,
        'module emdash_g = std(emdash_m);',
        `vector emdash_v = ${vectorText(
            lifted.components.map(algebraPolynomialText)
        )};`,
        'vector emdash_n = reduce(emdash_v,emdash_g);',
        'if (emdash_n == 0) { print("EMDASH_MODULE_ZERO:1"); }',
        'else { print("EMDASH_MODULE_ZERO:0"); }',
        'quit;'
    ].join('\n') + '\n';
}

export function createSingularPresentedModuleZeroEngine<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    bundle: AlgebraPresentedModuleZeroOperationBundle<P, C, I>,
    transport: AlgebraOracleTransport,
    executable = ALGEBRA_PRESENTED_MODULE_SINGULAR_PROFILE.executable
): AlgebraEngine {
    const engineIdentity = algebraEngineIdentity(
        'algebra.oracle.singular.presented-module',
        'v1'
    );
    const algorithm: AlgebraAlgorithmIdentity = algebraAlgorithmIdentity(
        'algebra.oracle.singular/presented-module-zero',
        'v1'
    );
    return defineAlgebraEngine({
        id: engineIdentity.id,
        revision: engineIdentity.revision,
        support: operation => {
            const sameContract =
                operation.identity.id === bundle.operation.identity.id &&
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
                        message: 'Singular module oracle supports one zero decision'
                    }]
                });
        },
        async compute(operation, input, _algorithm, context) {
            if (context.cancellation?.requested()) {
                throw new AlgebraOracleError(
                    'CANCELLED',
                    context.cancellation.reason?.() ?? 'Oracle cancelled'
                );
            }
            const result = await transport.execute({
                executable,
                args: ['-q'],
                stdin: singularPresentedModuleZeroScript(bundle.module, input as never),
                timeoutMilliseconds: 30_000,
                maximumOutputBytes: 1_000_000
            });
            if (result.exitCode !== 0) {
                throw new AlgebraOracleError(
                    'PROCESS_FAILED',
                    result.stderr || `Singular exited with ${result.exitCode}`
                );
            }
            const match = /EMDASH_MODULE_ZERO:([01])/u.exec(result.stdout);
            if (!match) {
                throw new AlgebraOracleError(
                    'MALFORMED_OUTPUT',
                    'Singular output omitted the module-zero marker'
                );
            }
            return {
                operation: operation.identity,
                engine: engineIdentity,
                algorithm,
                quality: 'exact',
                value: {
                    kind: 'algebra-presented-module-zero-decision',
                    zero: match[1] === '1',
                    provider: 'singular-oracle'
                },
                diagnostics: [{
                    code: 'EXTERNAL_ORACLE',
                    severity: 'info',
                    message: 'Non-authoritative Singular module result'
                }]
            };
        }
    });
}

export interface AlgebraPresentedModuleOracleComparison {
    readonly kind: 'algebra-presented-module-oracle-comparison';
    readonly native: AlgebraPresentedModuleZeroDecision;
    readonly oracle: AlgebraPresentedModuleZeroDecision;
    readonly agrees: boolean;
}

export async function comparePresentedModuleZeroWithSingular<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    bundle: AlgebraPresentedModuleZeroOperationBundle<P, C, I>,
    vector: AlgebraPresentedAlgebraModuleVector<P, C, I>,
    transport: AlgebraOracleTransport
): Promise<AlgebraPresentedModuleOracleComparison> {
    const nativeEngine = createAlgebraTypeScriptReferenceEngine({
        implementations: [bundle.nativeImplementation]
    });
    const oracleEngine = createSingularPresentedModuleZeroEngine(
        bundle,
        transport
    );
    const [native, oracle] = await Promise.all([
        computeAlgebraOperation({
            engine: nativeEngine,
            operation: bundle.operation,
            input: vector
        }),
        computeAlgebraOperation({
            engine: oracleEngine,
            operation: bundle.operation,
            input: vector
        })
    ]);
    return Object.freeze({
        kind: 'algebra-presented-module-oracle-comparison',
        native: native.value,
        oracle: oracle.value,
        agrees: native.value.zero === oracle.value.zero
    });
}
