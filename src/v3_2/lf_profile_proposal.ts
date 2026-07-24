/**
 * Machine-readable H-DTTLF-01 proposal for the outer λΠ LF profile.
 *
 * This is a pre-review description of the already isolated candidate path.
 * It does not promote that path into the browser product, change the frozen
 * MVP manifest, or authorize any metatheoretic claim.
 */

import {
    CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT
} from './lf_checker';
import {
    CORE_MVP_MANIFEST
} from './manifest';
import {
    CORE_MVP_RUNTIME_PROGRAM
} from './runtime';

export type CoreLfProfileTransition =
    | 'zonk'
    | 'beta'
    | 'delta'
    | 'reviewed-runtime';

export interface CoreLfProfileProposalInput {
    readonly revision: 'LF-PROFILE-1';
    readonly status: 'proposal-awaiting-h-dttlf-01';
    readonly reviewGate: 'H-DTTLF-01';
    readonly intendedUse: 'active-continuation-checker-api';
    readonly conversion: {
        readonly transitionOrder: readonly CoreLfProfileTransition[];
        readonly defaultStepLimit: 256;
        readonly budgetUnit: 'successful-transition';
        readonly budgetScope:
            'global-across-both-sides-and-all-congruence-paths';
        readonly equalityClosure:
            'weak-head-reduction-plus-structural-congruence';
        readonly plicityMismatch: 'stuck';
        readonly eta: 'disabled';
        readonly arbitraryUserRules: 'excluded';
    };
    readonly declarations: {
        readonly storage: 'persistent-immutable-environment';
        readonly defaultTransparency: 'opaque';
        readonly transparentAssumption: 'rejected';
        readonly bodyCheckingEnvironment: 'strictly-preceding';
        readonly bodyDependencyOrder: 'strictly-earlier-ordinals';
        readonly selfReference: 'rejected';
        readonly forwardReference: 'rejected';
        readonly globalRegistry: 'absent';
    };
    readonly checker: {
        readonly annotatedLambdaInference: true;
        readonly unannotatedLambdaInference: false;
        readonly rigidConstraintRevisit: 'combined-conversion';
        readonly contextualMillerPatterns: 'retained';
        readonly foreignDeclarationEnvironment: 'rejected';
    };
    readonly surface: {
        readonly representation: 'one-shot-scoped-builder';
        readonly binderIdentity: 'opaque-builder-local-token';
        readonly trustedLowering: 'de-bruijn-core';
        readonly callbackStorage: 'none';
        readonly let: 'annotated-lambda-beta-sugar';
        readonly parser: 'not-required';
    };
    readonly reviewedRuntimeComponent: {
        readonly manifestRevision: 'emdash-v3.2-mvp-1';
        readonly manifestContentHash:
            'sha256:28834e9c0361b98e9f14f66f02aac8f59900a98b9c8c1ce1c62ae0e5396f8ff0';
        readonly ruleIds: readonly string[];
        readonly authority:
            'exact-reviewed-runtime-subprogram-only';
    };
    readonly integrationBoundary: {
        readonly developmentBarrel: 'src/v3_2/index.ts';
        readonly browserEntryPoint: 'excluded';
        readonly frozenMvpMutation: false;
        readonly deployedManifest: 'unchanged';
        readonly directedCandidateUse:
            'authorized-only-after-h-dttlf-01';
    };
    readonly claims: {
        readonly boundedStopping: 'implemented';
        readonly unrestrictedNormalization: 'withheld';
        readonly termination: 'withheld';
        readonly confluence: 'withheld';
        readonly typescriptSubjectReduction: 'withheld';
        readonly performanceSla: 'withheld';
    };
}

export type CoreLfProfileProposalErrorCode =
    | 'INVALID_PROFILE_BOUNDARY'
    | 'INVALID_CONVERSION_PROFILE'
    | 'INVALID_DECLARATION_POLICY'
    | 'INVALID_CHECKER_SURFACE'
    | 'MVP_RUNTIME_DRIFT'
    | 'UNAUTHORIZED_CLAIM'
    | 'PROFILE_DRIFT';

export class CoreLfProfileProposalError extends Error {
    constructor(
        public readonly code: CoreLfProfileProposalErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreLfProfileProposalError';
    }
}

const rawProfile: CoreLfProfileProposalInput = {
    revision: 'LF-PROFILE-1',
    status: 'proposal-awaiting-h-dttlf-01',
    reviewGate: 'H-DTTLF-01',
    intendedUse: 'active-continuation-checker-api',
    conversion: {
        transitionOrder: [
            'zonk',
            'beta',
            'delta',
            'reviewed-runtime'
        ],
        defaultStepLimit: 256,
        budgetUnit: 'successful-transition',
        budgetScope:
            'global-across-both-sides-and-all-congruence-paths',
        equalityClosure:
            'weak-head-reduction-plus-structural-congruence',
        plicityMismatch: 'stuck',
        eta: 'disabled',
        arbitraryUserRules: 'excluded'
    },
    declarations: {
        storage: 'persistent-immutable-environment',
        defaultTransparency: 'opaque',
        transparentAssumption: 'rejected',
        bodyCheckingEnvironment: 'strictly-preceding',
        bodyDependencyOrder: 'strictly-earlier-ordinals',
        selfReference: 'rejected',
        forwardReference: 'rejected',
        globalRegistry: 'absent'
    },
    checker: {
        annotatedLambdaInference: true,
        unannotatedLambdaInference: false,
        rigidConstraintRevisit: 'combined-conversion',
        contextualMillerPatterns: 'retained',
        foreignDeclarationEnvironment: 'rejected'
    },
    surface: {
        representation: 'one-shot-scoped-builder',
        binderIdentity: 'opaque-builder-local-token',
        trustedLowering: 'de-bruijn-core',
        callbackStorage: 'none',
        let: 'annotated-lambda-beta-sugar',
        parser: 'not-required'
    },
    reviewedRuntimeComponent: {
        manifestRevision: 'emdash-v3.2-mvp-1',
        manifestContentHash:
            'sha256:28834e9c0361b98e9f14f66f02aac8f59900a98b9c8c1ce1c62ae0e5396f8ff0',
        ruleIds: [
            'projection.functor-hom.evaluate',
            'projection.transfor-component.evaluate',
            'projection.transfor-hom.evaluate'
        ],
        authority: 'exact-reviewed-runtime-subprogram-only'
    },
    integrationBoundary: {
        developmentBarrel: 'src/v3_2/index.ts',
        browserEntryPoint: 'excluded',
        frozenMvpMutation: false,
        deployedManifest: 'unchanged',
        directedCandidateUse: 'authorized-only-after-h-dttlf-01'
    },
    claims: {
        boundedStopping: 'implemented',
        unrestrictedNormalization: 'withheld',
        termination: 'withheld',
        confluence: 'withheld',
        typescriptSubjectReduction: 'withheld',
        performanceSla: 'withheld'
    }
};

const deepFreeze = <T>(value: T): T => {
    if (
        value !== null &&
        typeof value === 'object' &&
        !Object.isFrozen(value)
    ) {
        Object.values(value as Record<string, unknown>).forEach(item =>
            deepFreeze(item)
        );
        Object.freeze(value);
    }
    return value;
};

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

const fail = (
    code: CoreLfProfileProposalErrorCode,
    message: string
): never => {
    throw new CoreLfProfileProposalError(code, message);
};

export const CORE_LF_CONTINUATION_PROFILE_PROPOSAL =
    deepFreeze(rawProfile);

/**
 * Validate the exact H-DTTLF-01 review input against live frozen components.
 */
export function validateCoreLfProfileProposal(
    profile: CoreLfProfileProposalInput =
        CORE_LF_CONTINUATION_PROFILE_PROPOSAL
): void {
    if (
        profile.revision !== 'LF-PROFILE-1' ||
        profile.status !== 'proposal-awaiting-h-dttlf-01' ||
        profile.reviewGate !== 'H-DTTLF-01' ||
        profile.intendedUse !== 'active-continuation-checker-api' ||
        profile.integrationBoundary.browserEntryPoint !== 'excluded' ||
        profile.integrationBoundary.frozenMvpMutation !== false ||
        profile.integrationBoundary.deployedManifest !== 'unchanged'
    ) {
        fail(
            'INVALID_PROFILE_BOUNDARY',
            'The outer LF must remain a continuation-only proposal awaiting ' +
            'H-DTTLF-01'
        );
    }

    if (
        !sameData(profile.conversion.transitionOrder, [
            'zonk',
            'beta',
            'delta',
            'reviewed-runtime'
        ]) ||
        profile.conversion.defaultStepLimit !==
            CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT ||
        profile.conversion.budgetUnit !== 'successful-transition' ||
        profile.conversion.budgetScope !==
            'global-across-both-sides-and-all-congruence-paths' ||
        profile.conversion.equalityClosure !==
            'weak-head-reduction-plus-structural-congruence' ||
        profile.conversion.plicityMismatch !== 'stuck' ||
        profile.conversion.eta !== 'disabled' ||
        profile.conversion.arbitraryUserRules !== 'excluded'
    ) {
        fail(
            'INVALID_CONVERSION_PROFILE',
            'The outer LF conversion order, global budget, or exclusions ' +
            'have drifted'
        );
    }

    if (
        profile.declarations.storage !==
            'persistent-immutable-environment' ||
        profile.declarations.defaultTransparency !== 'opaque' ||
        profile.declarations.transparentAssumption !== 'rejected' ||
        profile.declarations.bodyCheckingEnvironment !==
            'strictly-preceding' ||
        profile.declarations.bodyDependencyOrder !==
            'strictly-earlier-ordinals' ||
        profile.declarations.selfReference !== 'rejected' ||
        profile.declarations.forwardReference !== 'rejected' ||
        profile.declarations.globalRegistry !== 'absent'
    ) {
        fail(
            'INVALID_DECLARATION_POLICY',
            'The outer LF checked-declaration or transparency policy drifted'
        );
    }

    if (
        profile.checker.annotatedLambdaInference !== true ||
        profile.checker.unannotatedLambdaInference !== false ||
        profile.checker.rigidConstraintRevisit !==
            'combined-conversion' ||
        profile.checker.contextualMillerPatterns !== 'retained' ||
        profile.checker.foreignDeclarationEnvironment !== 'rejected' ||
        profile.surface.representation !==
            'one-shot-scoped-builder' ||
        profile.surface.binderIdentity !==
            'opaque-builder-local-token' ||
        profile.surface.trustedLowering !== 'de-bruijn-core' ||
        profile.surface.callbackStorage !== 'none' ||
        profile.surface.let !== 'annotated-lambda-beta-sugar'
    ) {
        fail(
            'INVALID_CHECKER_SURFACE',
            'The outer LF checker or scoped-surface boundary drifted'
        );
    }

    const liveRuntime = {
        manifestRevision: CORE_MVP_MANIFEST.revision,
        manifestContentHash: CORE_MVP_MANIFEST.contentHash,
        ruleIds: CORE_MVP_RUNTIME_PROGRAM.rules.map(rule => rule.id),
        authority: 'exact-reviewed-runtime-subprogram-only'
    };
    if (!sameData(profile.reviewedRuntimeComponent, liveRuntime)) {
        fail(
            'MVP_RUNTIME_DRIFT',
            'The outer LF must embed only the exact reviewed MVP runtime ' +
            'subprogram'
        );
    }

    if (
        profile.claims.boundedStopping !== 'implemented' ||
        profile.claims.unrestrictedNormalization !== 'withheld' ||
        profile.claims.termination !== 'withheld' ||
        profile.claims.confluence !== 'withheld' ||
        profile.claims.typescriptSubjectReduction !== 'withheld' ||
        profile.claims.performanceSla !== 'withheld'
    ) {
        fail(
            'UNAUTHORIZED_CLAIM',
            'H-DTTLF-01 grants no normalization, termination, confluence, ' +
            'subject-reduction, or performance claim'
        );
    }

    if (!sameData(profile, rawProfile)) {
        fail(
            'PROFILE_DRIFT',
            'The outer LF profile differs from its exact H-DTTLF-01 input'
        );
    }
}

validateCoreLfProfileProposal();
