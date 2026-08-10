/**
 * Fresh proof-document checking over the exact outer-LF environment.
 *
 * Proof terms may contain lambda motives whose result types require generic
 * beta conversion, and checked declaration closures may expose transparent
 * delta bodies. This checker reuses the bounded combined LF conversion path
 * without opening annotated-lambda inference or accepting a runtime callback.
 */

import {
    CoreLfChecker,
    CoreLfElaborationSession,
    CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT
} from './lf_checker';
import {
    CoreLfDeclarationEnvironment
} from './lf_declarations';

export const CORE_PROOF_CHECKER_PROFILE = Object.freeze({
    revision: 'emdash-core-proof-checker-v1' as const,
    checker: 'CoreProofChecker' as const,
    environment: 'exact-core-lf-declaration-environment' as const,
    conversion:
        'bounded-zonk-beta-delta-reviewed-runtime' as const,
    comparisonStepLimit:
        CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT,
    permitsAnnotatedLambdaInference: false as const,
    acceptsCatalogRuntime: false as const,
    serializesComparisonTrace: false as const,
    productionLambdapiDependency: false as const,
    nodeBuiltinDependency: false as const
});

/**
 * Product proof checker: combined conversion with the bidirectional lambda
 * boundary kept closed. The constructor deliberately exposes no catalog
 * runtime parameter.
 */
export class CoreProofChecker extends CoreLfChecker {
    constructor(
        environment: CoreLfDeclarationEnvironment,
        comparisonStepLimit =
            CORE_PROOF_CHECKER_PROFILE.comparisonStepLimit
    ) {
        super(new CoreLfElaborationSession(
            environment,
            comparisonStepLimit
        ));
    }

    protected permitsAnnotatedLambdaInference(): boolean {
        return false;
    }

    protected conversionDiagnosticName(): string {
        return 'Core proof conversion';
    }
}

export const createCoreProofChecker = (
    environment: CoreLfDeclarationEnvironment,
    comparisonStepLimit = CORE_PROOF_CHECKER_PROFILE.comparisonStepLimit
): CoreProofChecker => new CoreProofChecker(
    environment,
    comparisonStepLimit
);
