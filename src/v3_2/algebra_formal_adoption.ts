/** Explicit checked or trusted adoption of exact formal computations. */

import {
    AlgebraFormalComputationDatum,
    AlgebraFormalComputationRequest,
    AlgebraFormalDelegationError,
    normalizeAlgebraFormalComputationInterpretation,
    serializeAlgebraFormalComputationInterpretation,
    serializeAlgebraFormalComputationOutput,
    serializeAlgebraFormalComputationRequest
} from './algebra_formal_delegation';
import {
    ALGEBRA_ENGINE_PROFILE
} from './algebra_engine';
import {
    ALGEBRA_FORMAL_DELEGATION_EXECUTION_PROFILE,
    AlgebraFormalComputationResult,
    serializeAlgebraFormalComputationResult
} from './algebra_formal_delegation_execution';
import {
    serializeCoreExpression
} from './core_serialization';
import {
    CoreLfDeclaration,
    CoreLfDeclarationEnvironment
} from './lf_declarations';
import {
    CoreProofRefiner
} from './proof';
import {
    createCoreProofChecker
} from './proof_checker';
import {
    CoreProofPlan,
    CoreProofPlanExecution,
    coreProofPlanExact,
    executeCoreProofPlan
} from './proof_plan';
import {
    CoreProofPlanPatch,
    applyCoreProofPlanPatch,
    createCoreProofPlanHoleReplacement
} from './proof_plan_patch';
import {
    KernelExpression,
    Provenance,
    binderMode,
    kernelFree,
    kernelUniverse,
    provenance
} from './kernel';
import {
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';

export const ALGEBRA_FORMAL_ADOPTION_PROFILE = Object.freeze({
    revision: 'emdash-algebra-formal-adoption-v1' as const,
    dataRevision: 'emdash-algebra-formal-checked-data-v1' as const,
    checkedRevision: 'emdash-algebra-formal-checked-adoption-v1' as const,
    trustedRevision: 'emdash-algebra-formal-trusted-adoption-v1' as const,
    trustedDecisionKind: 'trust-exact-algebra-computation' as const,
    trustedDeclaration: 'checked-type-body-free-opaque' as const,
    completionAuthority: Object.freeze({
        checked: 'checked-proof-plan' as const,
        trusted: 'checked-relative-to-explicit-assumption' as const
    }),
    mutatesInputEnvironment: false as const,
    mutatesInputPlan: false as const,
    addsCoreOwner: false as const,
    addsProofPlanTag: false as const,
    performsComputation: false as const,
    performsIo: false as const,
    productionLambdapiDependency: false as const
});

const fail = (
    code: AlgebraFormalDelegationError['code'],
    path: string,
    message: string,
    underlying?: unknown
): never => {
    throw new AlgebraFormalDelegationError(
        code,
        path,
        message,
        underlying instanceof Error ? underlying : undefined
    );
};

const SAFE_NAME = /^[A-Za-z][A-Za-z0-9._/-]*$/u;

const portableText = (value: unknown, path: string): string => {
    if (
        typeof value === 'string' &&
        value.trim().length > 0 &&
        value.length <= 4096 &&
        !/[\u0000-\u0008\u000b\u000c\u000e-\u001f\u007f]/u.test(value)
    ) return value;
    return fail(
        'INVALID_APPROVAL',
        path,
        'Trusted-adoption evidence must be nonempty bounded portable text'
    );
};

const assertCurrent = <R, I, O>(
    result: AlgebraFormalComputationResult<R, I, O>
): void => {
    if (
        result.profileRevision !==
            ALGEBRA_FORMAL_DELEGATION_EXECUTION_PROFILE.resultRevision ||
        result.computed.profileRevision !== ALGEBRA_ENGINE_PROFILE.resultRevision
    ) {
        fail(
            'STALE_RESULT',
            'adoption.result.profileRevision',
            'Formal computation result has a foreign revision'
        );
    }
    const sameIdentity = (
        left: { readonly id: string; readonly revision: string },
        right: { readonly id: string; readonly revision: string }
    ): boolean => left.id === right.id && left.revision === right.revision;
    if (
        !sameIdentity(result.computed.operation, result.request.operation.identity) ||
        !sameIdentity(result.computed.engine, result.request.engine.identity) ||
        (
            result.request.algorithm !== undefined &&
            !sameIdentity(result.computed.algorithm, result.request.algorithm)
        )
    ) {
        fail(
            'STALE_RESULT',
            'adoption.result.computed',
            'Computed operation, engine, or algorithm differs from the request'
        );
    }
    const requestData = serializeAlgebraFormalComputationRequest(result.request);
    if (requestData !== result.requestData) {
        fail(
            'STALE_RESULT',
            'adoption.result.requestData',
            'Formal computation request has changed since execution'
        );
    }
    const outputData = serializeAlgebraFormalComputationOutput(
        result.request.adapter,
        result.computed.value
    );
    if (outputData !== result.outputData) {
        fail(
            'STALE_RESULT',
            'adoption.result.outputData',
            'Computed output has changed since interpretation'
        );
    }
    const interpretationData =
        serializeAlgebraFormalComputationInterpretation(result.interpretation);
    if (interpretationData !== result.interpretationData) {
        fail(
            'STALE_RESULT',
            'adoption.result.interpretationData',
            'Formal interpretation has changed since execution'
        );
    }
    let firstInterpretation: string;
    let secondInterpretation: string;
    try {
        firstInterpretation = serializeAlgebraFormalComputationInterpretation(
            normalizeAlgebraFormalComputationInterpretation(
                result.request.goal,
                result.request.adapter.interpret({
                    goal: result.request.goal,
                    realization: result.request.realization,
                    operationInput: result.request.operationInput,
                    computed: result.computed
                })
            )
        );
        secondInterpretation = serializeAlgebraFormalComputationInterpretation(
            normalizeAlgebraFormalComputationInterpretation(
                result.request.goal,
                result.request.adapter.interpret({
                    goal: result.request.goal,
                    realization: result.request.realization,
                    operationInput: result.request.operationInput,
                    computed: result.computed
                })
            )
        );
    } catch (error: unknown) {
        return fail(
            'STALE_RESULT',
            'adoption.result.interpretation',
            'Adapter can no longer reproduce the formal interpretation',
            error
        );
    }
    if (
        firstInterpretation !== secondInterpretation ||
        firstInterpretation !== result.interpretationData
    ) {
        fail(
            'STALE_RESULT',
            'adoption.result.interpretation',
            'Adapter interpretation no longer matches the executed result'
        );
    }
    if (result.computed.quality !== 'exact') {
        fail(
            'UNSUPPORTED_RESULT_QUALITY',
            'adoption.result.computed.quality',
            'Only exact computations may reach adoption v1'
        );
    }
};

const claimResult = <R, I, O>(
    result: AlgebraFormalComputationResult<R, I, O>
): Extract<typeof result.interpretation, { readonly kind: 'claim' }> => {
    assertCurrent(result);
    if (result.interpretation.kind !== 'claim') {
        return fail(
            'NO_ADOPTABLE_CLAIM',
            'adoption.result.interpretation',
            'Observation-only computation has no formal claim to adopt'
        );
    }
    return result.interpretation;
};

export interface AlgebraFormalCheckedDatum {
    readonly id: string;
    readonly type: KernelExpression;
    readonly term: KernelExpression;
}

export interface AlgebraFormalCheckedData {
    readonly profileRevision:
        typeof ALGEBRA_FORMAL_ADOPTION_PROFILE.dataRevision;
    readonly data: readonly AlgebraFormalCheckedDatum[];
}

const checkDatum = (
    environment: CoreLfDeclarationEnvironment,
    datum: AlgebraFormalComputationDatum,
    index: number
): AlgebraFormalCheckedDatum => {
    const checker = createCoreProofChecker(environment);
    checker.validateEnvironment();
    const nodeProvenance = provenance(
        'derived',
        `formal computation datum ${datum.id}`
    );
    try {
        const type = checker.check(
            checker.rootContext,
            datum.type,
            kernelUniverse(nodeProvenance)
        ).term;
        const term = checker.check(
            checker.rootContext,
            datum.term,
            type
        ).term;
        return Object.freeze({ id: datum.id, type, term });
    } catch (error: unknown) {
        return fail(
            'ADOPTION_FAILED',
            `adoption.data[${index}]`,
            `Formal computation datum '${datum.id}' did not typecheck`,
            error
        );
    }
};

export function checkAlgebraFormalComputationData<R, I, O>(
    result: AlgebraFormalComputationResult<R, I, O>
): AlgebraFormalCheckedData {
    assertCurrent(result);
    const environment = result.request.goal.document.environment;
    return Object.freeze({
        profileRevision: ALGEBRA_FORMAL_ADOPTION_PROFILE.dataRevision,
        data: Object.freeze(result.interpretation.data.map((datum, index) =>
            checkDatum(environment, datum, index)
        ))
    });
}

interface CheckedReplay {
    readonly execution: CoreProofPlanExecution;
    readonly checkedTerm: KernelExpression;
}

const replayComplete = (
    environment: CoreLfDeclarationEnvironment,
    target: KernelExpression,
    plan: CoreProofPlan,
    nodeProvenance: Provenance,
    path: string
): CheckedReplay => {
    try {
        const checker = createCoreProofChecker(environment);
        checker.validateEnvironment();
        const checkedTarget = checker.check(
            checker.rootContext,
            target,
            kernelUniverse(nodeProvenance)
        ).term;
        const root = checker.lfSession.freshMeta(
            checker.rootContext,
            checkedTarget,
            nodeProvenance
        );
        const execution = executeCoreProofPlan(
            new CoreProofRefiner(checker, root),
            root.identity,
            plan
        );
        if (execution.state.status !== 'complete') {
            return fail(
                'CHECKED_PLAN_FAILED',
                path,
                'Adopted proof plan left an open goal'
            );
        }
        const checkedTerm = checker.check(
            checker.rootContext,
            execution.term,
            checkedTarget
        ).term;
        return Object.freeze({ execution, checkedTerm });
    } catch (error: unknown) {
        if (error instanceof AlgebraFormalDelegationError) throw error;
        return fail(
            'CHECKED_PLAN_FAILED',
            path,
            'Adopted proof plan did not check in its selected environment',
            error
        );
    }
};

interface AlgebraFormalAdoptionBase<R, I, O> {
    readonly result: AlgebraFormalComputationResult<R, I, O>;
    readonly patch: CoreProofPlanPatch;
    readonly plan: CoreProofPlan;
    readonly environment: CoreLfDeclarationEnvironment;
    readonly execution: CoreProofPlanExecution;
    readonly checkedTerm: KernelExpression;
}

export interface AlgebraFormalCheckedAdoption<R, I, O>
    extends AlgebraFormalAdoptionBase<R, I, O> {
    readonly profileRevision:
        typeof ALGEBRA_FORMAL_ADOPTION_PROFILE.checkedRevision;
    readonly kind: 'checked-plan';
    readonly authority:
        typeof ALGEBRA_FORMAL_ADOPTION_PROFILE.completionAuthority.checked;
}

export function adoptAlgebraFormalCheckedPlan<R, I, O>(input: {
    readonly result: AlgebraFormalComputationResult<R, I, O>;
    readonly replacement: CoreProofPlan;
}): AlgebraFormalCheckedAdoption<R, I, O> {
    claimResult(input.result);
    checkAlgebraFormalComputationData(input.result);
    const patch = createCoreProofPlanHoleReplacement(
        input.result.request.goal.goalId,
        input.replacement
    );
    const plan = applyCoreProofPlanPatch(
        input.result.request.goal.document.plan,
        patch
    );
    const checked = replayComplete(
        input.result.request.goal.document.environment,
        input.result.request.goal.target,
        plan,
        provenance('derived', 'checked formal computation adoption'),
        'checkedAdoption.plan'
    );
    return Object.freeze({
        profileRevision: ALGEBRA_FORMAL_ADOPTION_PROFILE.checkedRevision,
        kind: 'checked-plan',
        authority: ALGEBRA_FORMAL_ADOPTION_PROFILE.completionAuthority.checked,
        result: input.result,
        patch,
        plan,
        environment: input.result.request.goal.document.environment,
        execution: checked.execution,
        checkedTerm: checked.checkedTerm
    });
}

export interface AlgebraFormalTrustedAdoptionDecision {
    readonly kind:
        typeof ALGEBRA_FORMAL_ADOPTION_PROFILE.trustedDecisionKind;
    readonly evidence: string;
}

export interface AlgebraFormalTrustedAdoptionArtifact {
    readonly revision:
        typeof ALGEBRA_FORMAL_ADOPTION_PROFILE.trustedRevision;
    readonly kind: 'trusted-assumption';
    readonly authority:
        typeof ALGEBRA_FORMAL_ADOPTION_PROFILE.completionAuthority.trusted;
    readonly evidence: string;
    readonly moduleId: string;
    readonly declarationId: string;
    readonly goalId: string;
    readonly assumptionName: string;
    readonly assumptionTypeCore: string;
    readonly requestData: string;
    readonly resultData: string;
    readonly checkedTermCore: string;
}

export interface AlgebraFormalTrustedAdoption<R, I, O>
    extends AlgebraFormalAdoptionBase<R, I, O> {
    readonly profileRevision:
        typeof ALGEBRA_FORMAL_ADOPTION_PROFILE.trustedRevision;
    readonly kind: 'trusted-assumption';
    readonly authority:
        typeof ALGEBRA_FORMAL_ADOPTION_PROFILE.completionAuthority.trusted;
    readonly assumption: CoreLfDeclaration;
    readonly reference: KernelExpression;
    readonly artifact: AlgebraFormalTrustedAdoptionArtifact;
}

export function adoptAlgebraFormalTrustedComputation<R, I, O>(input: {
    readonly result: AlgebraFormalComputationResult<R, I, O>;
    readonly assumptionName: string;
    readonly decision: AlgebraFormalTrustedAdoptionDecision;
}): AlgebraFormalTrustedAdoption<R, I, O> {
    const claim = claimResult(input.result);
    if (input.result.computed.assumptions.length > 0) {
        return fail(
            'UNACKNOWLEDGED_ASSUMPTIONS',
            'trustedAdoption.result.computed.assumptions',
            'Trusted adoption v1 requires an exact assumption-free computation'
        );
    }
    if (
        input.decision?.kind !==
            ALGEBRA_FORMAL_ADOPTION_PROFILE.trustedDecisionKind
    ) {
        return fail(
            'INVALID_APPROVAL',
            'trustedAdoption.decision.kind',
            'Trusted computation requires one explicit adoption decision'
        );
    }
    const evidence = portableText(
        input.decision.evidence,
        'trustedAdoption.decision.evidence'
    );
    if (
        typeof input.assumptionName !== 'string' ||
        !SAFE_NAME.test(input.assumptionName)
    ) {
        return fail(
            'INVALID_APPROVAL',
            'trustedAdoption.assumptionName',
            'Trusted assumption name must be stable and portable'
        );
    }
    checkAlgebraFormalComputationData(input.result);
    const nodeProvenance = provenance(
        'derived',
        `trusted exact algebra computation: ${evidence}`
    );
    let environment: CoreLfDeclarationEnvironment;
    try {
        environment = input.result.request.goal.document.environment.extend({
            name: input.assumptionName,
            type: claim.claimType,
            mode: binderMode('explicit', 'functorial'),
            provenance: nodeProvenance
        });
    } catch (error: unknown) {
        return fail(
            'ADOPTION_FAILED',
            'trustedAdoption.assumption',
            'Trusted assumption declaration did not typecheck',
            error
        );
    }
    const assumption = environment.lookup(input.assumptionName);
    if (assumption === undefined) {
        return fail(
            'ADOPTION_FAILED',
            'trustedAdoption.assumption',
            'Extended environment did not retain the trusted assumption'
        );
    }
    const reference = kernelFree(input.assumptionName, nodeProvenance);
    const patch = createCoreProofPlanHoleReplacement(
        input.result.request.goal.goalId,
        coreProofPlanExact(reference, { provenance: nodeProvenance })
    );
    const plan = applyCoreProofPlanPatch(
        input.result.request.goal.document.plan,
        patch
    );
    const checked = replayComplete(
        environment,
        claim.claimType,
        plan,
        nodeProvenance,
        'trustedAdoption.plan'
    );
    const artifact: AlgebraFormalTrustedAdoptionArtifact = Object.freeze({
        revision: ALGEBRA_FORMAL_ADOPTION_PROFILE.trustedRevision,
        kind: 'trusted-assumption',
        authority: ALGEBRA_FORMAL_ADOPTION_PROFILE.completionAuthority.trusted,
        evidence,
        moduleId: input.result.request.goal.moduleId,
        declarationId: input.result.request.goal.declarationId,
        goalId: input.result.request.goal.goalId,
        assumptionName: input.assumptionName,
        assumptionTypeCore: claim.claimTypeCore,
        requestData: input.result.requestData,
        resultData: serializeAlgebraFormalComputationResult(input.result),
        checkedTermCore: serializeCoreExpression(checked.checkedTerm)
    });
    return Object.freeze({
        profileRevision: ALGEBRA_FORMAL_ADOPTION_PROFILE.trustedRevision,
        kind: 'trusted-assumption',
        authority: ALGEBRA_FORMAL_ADOPTION_PROFILE.completionAuthority.trusted,
        result: input.result,
        patch,
        plan,
        environment,
        execution: checked.execution,
        checkedTerm: checked.checkedTerm,
        assumption,
        reference,
        artifact
    });
}

export const serializeAlgebraFormalTrustedAdoptionArtifact = (
    artifact: AlgebraFormalTrustedAdoptionArtifact
): string => serializeCoreLfWorkspaceCanonicalJson(
    artifact,
    'algebraFormalTrustedAdoptionArtifact'
);

/** Exposed only for stale-safe consumers that retain the original request. */
export const assertAlgebraFormalComputationResultCurrent = <R, I, O>(
    result: AlgebraFormalComputationResult<R, I, O>,
    request: AlgebraFormalComputationRequest<R, I, O>
): void => {
    assertCurrent(result);
    if (
        serializeAlgebraFormalComputationRequest(request) !==
            result.requestData
    ) {
        fail(
            'STALE_RESULT',
            'adoption.currentRequest',
            'Supplied current request differs from the executed request'
        );
    }
};
