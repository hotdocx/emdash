/**
 * Immutable source-level patches for checked Core proof plans.
 *
 * A patch changes inert source data only. Semantic authority remains the
 * ordinary fresh proof-plan replay performed by the caller.
 */

import {
    CoreProofPlan,
    coreProofPlanApply,
    coreProofPlanHave,
    coreProofPlanIntro,
    validateCoreProofPlan
} from './proof_plan';

export const CORE_PROOF_PLAN_PATCH_PROFILE = Object.freeze({
    revision: 'emdash-proof-plan-patch-v1' as const,
    kinds: Object.freeze(['replace-hole'] as const),
    targetIdentity: 'stable-goal-id' as const,
    mutatesInput: false as const,
    performsSemanticChecks: false as const,
    addsProofPlanTags: false as const,
    nodeBuiltinDependency: false as const,
    productionLambdapiDependency: false as const
});

export interface CoreProofPlanReplaceHolePatch {
    readonly revision: typeof CORE_PROOF_PLAN_PATCH_PROFILE.revision;
    readonly kind: 'replace-hole';
    readonly goalId: string;
    readonly replacement: CoreProofPlan;
}

export type CoreProofPlanPatch = CoreProofPlanReplaceHolePatch;

export type CoreProofPlanPatchErrorCode =
    | 'INVALID_PATCH'
    | 'TARGET_NOT_FOUND';

export class CoreProofPlanPatchError extends Error {
    constructor(
        public readonly code: CoreProofPlanPatchErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(`${message} (${path})`);
        this.name = 'CoreProofPlanPatchError';
    }
}

const SAFE_GOAL_ID = /^[A-Za-z][A-Za-z0-9._-]*$/u;

const fail = (
    code: CoreProofPlanPatchErrorCode,
    path: string,
    message: string,
    underlying?: Error
): never => {
    throw new CoreProofPlanPatchError(code, path, message, underlying);
};

/** Create one inert exact hole-replacement patch. */
export function createCoreProofPlanHoleReplacement(
    goalId: string,
    replacement: CoreProofPlan
): CoreProofPlanReplaceHolePatch {
    if (typeof goalId !== 'string' || !SAFE_GOAL_ID.test(goalId)) {
        return fail(
            'INVALID_PATCH',
            'goalId',
            'Proof-plan patch target must be a stable source goal ID'
        );
    }
    try {
        validateCoreProofPlan(replacement);
    } catch (error: unknown) {
        return fail(
            'INVALID_PATCH',
            'replacement',
            'Proof-plan patch replacement is not a valid inert plan',
            error instanceof Error ? error : undefined
        );
    }
    return Object.freeze({
        revision: CORE_PROOF_PLAN_PATCH_PROFILE.revision,
        kind: 'replace-hole',
        goalId,
        replacement
    });
}

interface ReplacementResult {
    readonly plan: CoreProofPlan;
    readonly replaced: boolean;
}

const replaceHole = (
    plan: CoreProofPlan,
    goalId: string,
    replacement: CoreProofPlan
): ReplacementResult => {
    switch (plan.tag) {
        case 'exact':
            return { plan, replaced: false };
        case 'hole':
            return plan.goalId === goalId
                ? { plan: replacement, replaced: true }
                : { plan, replaced: false };
        case 'intro': {
            const body = replaceHole(plan.body, goalId, replacement);
            return body.replaced
                ? {
                    plan: coreProofPlanIntro(body.plan, {
                        id: plan.id,
                        provenance: plan.provenance,
                        name: plan.name
                    }),
                    replaced: true
                }
                : { plan, replaced: false };
        }
        case 'apply': {
            let replaced = false;
            const premises = plan.premises.map(premise => {
                if (replaced) return premise;
                const result = replaceHole(premise, goalId, replacement);
                replaced = result.replaced;
                return result.plan;
            });
            return replaced
                ? {
                    plan: coreProofPlanApply(plan.callee, premises, {
                        id: plan.id,
                        provenance: plan.provenance
                    }),
                    replaced: true
                }
                : { plan, replaced: false };
        }
        case 'have': {
            const proof = replaceHole(plan.proof, goalId, replacement);
            if (proof.replaced) {
                return {
                    plan: coreProofPlanHave(
                        plan.binding,
                        proof.plan,
                        plan.body,
                        {
                            id: plan.id,
                            provenance: plan.provenance
                        }
                    ),
                    replaced: true
                };
            }
            const body = replaceHole(plan.body, goalId, replacement);
            return body.replaced
                ? {
                    plan: coreProofPlanHave(
                        plan.binding,
                        plan.proof,
                        body.plan,
                        {
                            id: plan.id,
                            provenance: plan.provenance
                        }
                    ),
                    replaced: true
                }
                : { plan, replaced: false };
        }
        default: {
            const exhaustive: never = plan;
            return exhaustive;
        }
    }
};

const validatePatch = (
    patch: CoreProofPlanPatch
): CoreProofPlanReplaceHolePatch => {
    if (
        patch === null ||
        typeof patch !== 'object' ||
        patch.revision !== CORE_PROOF_PLAN_PATCH_PROFILE.revision ||
        patch.kind !== 'replace-hole' ||
        typeof patch.goalId !== 'string' ||
        !SAFE_GOAL_ID.test(patch.goalId)
    ) {
        return fail(
            'INVALID_PATCH',
            'patch',
            'Unsupported or malformed proof-plan patch'
        );
    }
    try {
        validateCoreProofPlan(patch.replacement);
    } catch (error: unknown) {
        return fail(
            'INVALID_PATCH',
            'patch.replacement',
            'Proof-plan patch replacement is not valid',
            error instanceof Error ? error : undefined
        );
    }
    return patch;
};

/**
 * Apply one immutable source patch and validate the resulting complete plan.
 */
export function applyCoreProofPlanPatch(
    plan: CoreProofPlan,
    inputPatch: CoreProofPlanPatch
): CoreProofPlan {
    try {
        validateCoreProofPlan(plan);
    } catch (error: unknown) {
        return fail(
            'INVALID_PATCH',
            'plan',
            'Cannot patch an invalid source proof plan',
            error instanceof Error ? error : undefined
        );
    }
    const patch = validatePatch(inputPatch);
    const result = replaceHole(
        plan,
        patch.goalId,
        patch.replacement
    );
    if (!result.replaced) {
        return fail(
            'TARGET_NOT_FOUND',
            'patch.goalId',
            `Proof plan has no open source hole '${patch.goalId}'`
        );
    }

    try {
        validateCoreProofPlan(result.plan);
    } catch (error: unknown) {
        return fail(
            'INVALID_PATCH',
            'result',
            'Proof-plan patch produced an invalid complete plan',
            error instanceof Error ? error : undefined
        );
    }
    return result.plan;
}
