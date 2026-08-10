/**
 * Deterministic, bounded obvious-proof proposals over accessible LF premises.
 *
 * The provider discovers candidates but grants no proof authority. Every
 * proposal is an inert hole-replacement patch checked by fresh ordinary Core
 * proof replay; acceptance repeats the precondition and result checks.
 */

import {
    CoreCheckerError
} from './checker';
import {
    serializeCoreExpression
} from './core_serialization';
import {
    CoreLfCompiledPremiseIndex,
    CoreLfPremiseIndexEntrySnapshot,
    CoreLfPremiseSearchResult,
    searchCoreLfAccessiblePremises,
    serializeCoreLfPremiseIndexSnapshot
} from './lf_premise_index';
import {
    KernelExpression,
    kernelFree,
    kernelUniverse,
    provenance
} from './kernel';
import {
    CoreProofGoal,
    CoreProofRefinementError,
    CoreProofRefiner
} from './proof';
import {
    createCoreProofChecker
} from './proof_checker';
import {
    CoreProofPlan,
    CoreProofPlanError,
    CoreProofPlanExecution,
    CoreProofPlanGoalSnapshot,
    CoreProofPlanHole,
    CoreProofPlanStateSnapshot,
    coreProofPlanApply,
    coreProofPlanExact,
    coreProofPlanHole,
    executeCoreProofPlan,
    serializeCoreProofPlanState
} from './proof_plan';
import {
    CORE_PROOF_PLAN_PATCH_PROFILE,
    CoreProofPlanPatch,
    applyCoreProofPlanPatch,
    createCoreProofPlanHoleReplacement
} from './proof_plan_patch';

export const CORE_OBVIOUS_PROOF_PROVIDER_PROFILE = Object.freeze({
    revision: 'emdash-obvious-proof-provider-v1' as const,
    candidateRevision: 'emdash-obvious-proof-candidate-v1' as const,
    reportRevision: 'emdash-obvious-proof-report-v1' as const,
    preconditionRevision: 'emdash-obvious-proof-precondition-v1' as const,
    replayRevision: 'emdash-obvious-proof-replay-v1' as const,
    patchRevision: CORE_PROOF_PLAN_PATCH_PROFILE.revision,
    retrieval: 'exact-conclusion-head' as const,
    premiseOrder: 'exact-qualified-id' as const,
    tacticOrder: Object.freeze(['exact', 'apply'] as const),
    applyDepth: 1,
    randomizes: false as const,
    defaultSeed: 'deterministic-v1' as const,
    defaultBudget: Object.freeze({
        premiseLimit: 32,
        tacticAttemptLimit: 64,
        candidateLimit: 16,
        introducedGoalLimit: 8
    }),
    maximumBudget: Object.freeze({
        premiseLimit: 256,
        tacticAttemptLimit: 512,
        candidateLimit: 128,
        introducedGoalLimit: 64
    }),
    recursiveDischarge: false as const,
    searchesLocalHypotheses: false as const,
    invokesInstanceSynthesis: false as const,
    invokesSimplifier: false as const,
    retainsSessionState: false as const,
    performsIo: false as const,
    computesCryptographicHashes: false as const,
    nodeBuiltinDependency: false as const,
    productionLambdapiDependency: false as const
});

export interface CoreObviousProofBudgetOptions {
    readonly premiseLimit?: number;
    readonly tacticAttemptLimit?: number;
    readonly candidateLimit?: number;
    readonly introducedGoalLimit?: number;
}

export interface CoreObviousProofBudget {
    readonly premiseLimit: number;
    readonly tacticAttemptLimit: number;
    readonly candidateLimit: number;
    readonly introducedGoalLimit: number;
}

export type CoreObviousProofOperation = 'exact' | 'apply';

export type CoreObviousProofTracePhase =
    | 'resolve'
    | 'exact-replay'
    | 'apply-explore'
    | 'candidate-replay';

export type CoreObviousProofTraceOutcome =
    | 'accepted'
    | 'rejected'
    | 'skipped'
    | 'bounded';

export interface CoreObviousProofDiagnostic {
    readonly code: string;
    readonly message: string;
}

export interface CoreObviousProofTraceStep {
    readonly ordinal: number;
    readonly premise: CoreLfPremiseIndexEntrySnapshot['symbol'];
    readonly phase: CoreObviousProofTracePhase;
    readonly outcome: CoreObviousProofTraceOutcome;
    readonly tacticAttempt?: number;
    readonly introducedGoalCount?: number;
    readonly candidateIndex?: number;
    readonly diagnostic?: CoreObviousProofDiagnostic;
}

export interface CoreObviousProofPrecondition {
    readonly revision:
        typeof CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.preconditionRevision;
    /** Exact canonical supplied-data index snapshot, not a computed hash. */
    readonly indexSnapshot: string;
    readonly checkedTarget: string;
    readonly baseState: CoreProofPlanStateSnapshot;
    readonly selectedGoal: CoreProofPlanGoalSnapshot;
}

export interface CoreObviousProofCandidateCost {
    readonly premiseOrdinal: number;
    readonly tacticAttempts: number;
    readonly checkerReplays: number;
    readonly introducedGoals: number;
}

export interface CoreObviousProofCandidate {
    readonly revision:
        typeof CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.candidateRevision;
    readonly providerRevision:
        typeof CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.revision;
    readonly allowedProfiles: readonly string[];
    readonly seed: string;
    readonly operation: CoreObviousProofOperation;
    readonly premise: CoreLfPremiseIndexEntrySnapshot;
    readonly precondition: CoreObviousProofPrecondition;
    readonly patch: CoreProofPlanPatch;
    readonly generatedGoalIds: readonly string[];
    readonly cost: CoreObviousProofCandidateCost;
    readonly trace: readonly CoreObviousProofTraceStep[];
    readonly result: CoreProofPlanStateSnapshot;
}

export type CoreObviousProofTermination =
    | 'exhausted-search'
    | 'premise-limit'
    | 'tactic-attempt-limit'
    | 'candidate-limit';

export interface CoreObviousProofProposalCounts {
    readonly premisesExamined: number;
    readonly tacticAttempts: number;
    readonly checkerReplays: number;
    readonly candidates: number;
}

export interface CoreObviousProofProposalReport {
    readonly revision:
        typeof CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.reportRevision;
    readonly providerRevision:
        typeof CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.revision;
    readonly allowedProfiles: readonly string[];
    readonly seed: string;
    readonly budget: CoreObviousProofBudget;
    readonly precondition: CoreObviousProofPrecondition;
    readonly search: CoreLfPremiseSearchResult;
    readonly trace: readonly CoreObviousProofTraceStep[];
    readonly candidates: readonly CoreObviousProofCandidate[];
    readonly counts: CoreObviousProofProposalCounts;
    readonly termination: CoreObviousProofTermination;
}

interface CoreObviousProofSourceInput {
    readonly index: CoreLfCompiledPremiseIndex;
    readonly type: KernelExpression;
    readonly plan: CoreProofPlan;
    readonly goalId: string;
}

export interface CoreObviousProofProposalInput
    extends CoreObviousProofSourceInput {
    readonly allowedProfiles?: readonly string[];
    readonly seed?: string;
    readonly budget?: CoreObviousProofBudgetOptions;
}

export interface CoreObviousProofCandidateReplayInput
    extends CoreObviousProofSourceInput {
    readonly candidate: CoreObviousProofCandidate;
}

export interface CoreObviousProofCandidateReplay {
    readonly revision:
        typeof CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.replayRevision;
    readonly plan: CoreProofPlan;
    readonly execution: CoreProofPlanExecution;
}

export type CoreObviousProofProviderErrorCode =
    | 'INVALID_INPUT'
    | 'INVALID_ALLOWED_PROFILE'
    | 'INVALID_BUDGET'
    | 'INVALID_SEED'
    | 'BASE_REPLAY_FAILED'
    | 'GOAL_NOT_OPEN'
    | 'CANDIDATE_CHECK_FAILED'
    | 'INVALID_CANDIDATE'
    | 'STALE_CANDIDATE';

export class CoreObviousProofProviderError extends Error {
    constructor(
        public readonly code: CoreObviousProofProviderErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(`${message} (${path})`);
        this.name = 'CoreObviousProofProviderError';
    }
}

const SAFE_GOAL_ID = /^[A-Za-z][A-Za-z0-9._-]*$/u;

const fail = (
    code: CoreObviousProofProviderErrorCode,
    path: string,
    message: string,
    underlying?: Error
): never => {
    throw new CoreObviousProofProviderError(
        code,
        path,
        message,
        underlying
    );
};

const cloneData = <T>(value: T): T => {
    if (Array.isArray(value)) return value.map(cloneData) as T;
    if (value !== null && typeof value === 'object') {
        return Object.fromEntries(Object.entries(
            value as Record<string, unknown>
        ).map(([key, entry]) => [key, cloneData(entry)])) as T;
    }
    return value;
};

const deepFreeze = <T>(value: T): T => {
    if (
        value !== null &&
        typeof value === 'object' &&
        !Object.isFrozen(value)
    ) {
        Object.values(value as Record<string, unknown>).forEach(deepFreeze);
        Object.freeze(value);
    }
    return value;
};

const freezeData = <T>(value: T): T => deepFreeze(cloneData(value));

const bounded = (
    value: number | undefined,
    fallback: number,
    maximum: number,
    path: string
): number => {
    const selected = value ?? fallback;
    if (
        Number.isSafeInteger(selected) &&
        selected >= 0 &&
        selected <= maximum
    ) {
        return selected;
    }
    return fail(
        'INVALID_BUDGET',
        path,
        `Budget must be a nonnegative safe integer at most ${maximum}; ` +
            `received ${String(selected)}`
    );
};

const normalizeBudget = (
    options: CoreObviousProofBudgetOptions | undefined
): CoreObviousProofBudget => {
    if (options !== undefined && (
        options === null ||
        typeof options !== 'object'
    )) {
        return fail(
            'INVALID_BUDGET',
            'budget',
            'Obvious-proof budget must be an object'
        );
    }
    const input = options ?? {};
    const defaults = CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.defaultBudget;
    const maxima = CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.maximumBudget;
    return Object.freeze({
        premiseLimit: bounded(
            input.premiseLimit,
            defaults.premiseLimit,
            maxima.premiseLimit,
            'budget.premiseLimit'
        ),
        tacticAttemptLimit: bounded(
            input.tacticAttemptLimit,
            defaults.tacticAttemptLimit,
            maxima.tacticAttemptLimit,
            'budget.tacticAttemptLimit'
        ),
        candidateLimit: bounded(
            input.candidateLimit,
            defaults.candidateLimit,
            maxima.candidateLimit,
            'budget.candidateLimit'
        ),
        introducedGoalLimit: bounded(
            input.introducedGoalLimit,
            defaults.introducedGoalLimit,
            maxima.introducedGoalLimit,
            'budget.introducedGoalLimit'
        )
    });
};

const normalizeAllowedProfiles = (
    input: readonly string[] | undefined
): readonly string[] => {
    const profiles = input === undefined
        ? [CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.revision]
        : input;
    if (!Array.isArray(profiles) || profiles.length === 0) {
        return fail(
            'INVALID_ALLOWED_PROFILE',
            'allowedProfiles',
            'At least one exact automation profile must be allowed'
        );
    }
    const seen = new Set<string>();
    const normalized = profiles.map((profile, index) => {
        if (
            profile !== CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.revision
        ) {
            return fail(
                'INVALID_ALLOWED_PROFILE',
                `allowedProfiles[${index}]`,
                `Unsupported obvious-proof profile '${String(profile)}'`
            );
        }
        if (seen.has(profile)) {
            return fail(
                'INVALID_ALLOWED_PROFILE',
                `allowedProfiles[${index}]`,
                `Duplicate obvious-proof profile '${profile}'`
            );
        }
        seen.add(profile);
        return profile;
    });
    return Object.freeze(normalized);
};

const normalizeSeed = (seed: string | undefined): string => {
    const selected = seed ?? CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.defaultSeed;
    if (
        typeof selected === 'string' &&
        selected.length > 0 &&
        selected.length <= 128 &&
        selected.trim() === selected &&
        !/[\u0000-\u001f\u007f]/u.test(selected)
    ) {
        return selected;
    }
    return fail(
        'INVALID_SEED',
        'seed',
        'Seed label must be 1-128 trimmed printable characters'
    );
};

interface FreshReplay {
    readonly checkedTarget: KernelExpression;
    readonly refiner: CoreProofRefiner;
    readonly execution: CoreProofPlanExecution;
}

const replayPlan = (
    index: CoreLfCompiledPremiseIndex,
    type: KernelExpression,
    plan: CoreProofPlan
): FreshReplay => {
    const checker = createCoreProofChecker(
        index.closureCompilation.environment
    );
    checker.validateEnvironment();
    const targetProvenance = provenance(
        'derived',
        'obvious-proof provider closed target must inhabit TYPE',
        plan.provenance.span
    );
    const checkedTarget = checker.check(
        checker.rootContext,
        type,
        kernelUniverse(targetProvenance)
    ).term;
    const root = checker.lfSession.freshMeta(
        checker.rootContext,
        checkedTarget,
        plan.provenance
    );
    const refiner = new CoreProofRefiner(checker, root);
    const execution = executeCoreProofPlan(
        refiner,
        root.identity,
        plan
    );
    if (execution.state.status === 'complete') {
        checker.check(
            checker.rootContext,
            execution.term,
            checkedTarget
        );
    }
    return Object.freeze({ checkedTarget, refiner, execution });
};

interface SelectedFreshGoal {
    readonly raw: CoreProofGoal;
    readonly snapshot: CoreProofPlanGoalSnapshot;
    readonly hole: CoreProofPlanHole;
}

const findHole = (
    plan: CoreProofPlan,
    goalId: string
): CoreProofPlanHole | undefined => {
    switch (plan.tag) {
        case 'exact':
            return undefined;
        case 'hole':
            return plan.goalId === goalId ? plan : undefined;
        case 'intro':
            return findHole(plan.body, goalId);
        case 'apply':
            for (const premise of plan.premises) {
                const found = findHole(premise, goalId);
                if (found !== undefined) return found;
            }
            return undefined;
        case 'have':
            return findHole(plan.proof, goalId) ??
                findHole(plan.body, goalId);
        default: {
            const exhaustive: never = plan;
            return exhaustive;
        }
    }
};

const selectFreshGoal = (
    replay: FreshReplay,
    plan: CoreProofPlan,
    goalId: string
): SelectedFreshGoal => {
    const index = replay.execution.snapshot.goals.findIndex(
        goal => goal.id === goalId
    );
    const hole = findHole(plan, goalId);
    if (
        index < 0 ||
        hole === undefined ||
        replay.execution.state.goals[index] === undefined
    ) {
        return fail(
            'GOAL_NOT_OPEN',
            'goalId',
            `Source goal '${goalId}' is not open after fresh plan replay`
        );
    }
    return Object.freeze({
        raw: replay.execution.state.goals[index],
        snapshot: replay.execution.snapshot.goals[index],
        hole
    });
};

const preconditionFor = (
    index: CoreLfCompiledPremiseIndex,
    replay: FreshReplay,
    goal: SelectedFreshGoal
): CoreObviousProofPrecondition => Object.freeze({
    revision: CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.preconditionRevision,
    indexSnapshot: serializeCoreLfPremiseIndexSnapshot(index.snapshot),
    checkedTarget: serializeCoreExpression(replay.checkedTarget),
    baseState: replay.execution.snapshot,
    selectedGoal: goal.snapshot
});

const knownCandidateRejection = (error: unknown): error is Error =>
    error instanceof CoreCheckerError ||
    error instanceof CoreProofRefinementError ||
    error instanceof CoreProofPlanError;

const diagnostic = (error: Error): CoreObviousProofDiagnostic => {
    const coded = error as Error & { readonly code?: unknown };
    const suffix = typeof coded.code === 'string'
        ? `.${coded.code}`
        : '';
    return Object.freeze({
        code: `${error.name}${suffix}`,
        message: error.message.replace(/\?m\d+/gu, '?internal')
    });
};

interface PlanIds {
    readonly nodeIds: Set<string>;
    readonly goalIds: Set<string>;
}

const collectPlanIds = (plan: CoreProofPlan): PlanIds => {
    const nodeIds = new Set<string>();
    const goalIds = new Set<string>();
    const visit = (node: CoreProofPlan, path: string): void => {
        nodeIds.add(node.id ?? path);
        switch (node.tag) {
            case 'exact':
                return;
            case 'hole':
                goalIds.add(node.goalId);
                return;
            case 'intro':
                visit(node.body, `${path}.body`);
                return;
            case 'apply':
                node.premises.forEach((premise, index) =>
                    visit(premise, `${path}.premise.${index}`)
                );
                return;
            case 'have':
                visit(node.proof, `${path}.proof`);
                visit(node.body, `${path}.body`);
                return;
            default: {
                const exhaustive: never = node;
                return exhaustive;
            }
        }
    };
    visit(plan, 'root');
    return { nodeIds, goalIds };
};

const reserveId = (
    base: string,
    ids: PlanIds
): string => {
    let candidate = base;
    let suffix = 2;
    while (ids.nodeIds.has(candidate) || ids.goalIds.has(candidate)) {
        candidate = `${base}.${suffix}`;
        suffix++;
    }
    ids.nodeIds.add(candidate);
    ids.goalIds.add(candidate);
    return candidate;
};

const applyReplacement = (
    source: CoreObviousProofSourceInput,
    hole: CoreProofPlanHole,
    term: ReturnType<typeof kernelFree>,
    introducedGoals: readonly CoreProofGoal[]
): {
    readonly patch: CoreProofPlanPatch;
    readonly plan: CoreProofPlan;
    readonly goalIds: readonly string[];
} => {
    const ids = collectPlanIds(source.plan);
    const goalIds: string[] = [];
    const premises = introducedGoals.map((goal, index) => {
        const base = `${source.goalId}.obvious.p${index + 1}`;
        const goalId = reserveId(base, ids);
        goalIds.push(goalId);
        const nodeId = reserveId(`${base}.node`, ids);
        return coreProofPlanHole(goalId, {
            id: nodeId,
            provenance: provenance(
                'derived',
                `obvious-proof unresolved premise ${index + 1}`,
                hole.provenance.span
            ),
            expectation: { contextDepth: goal.contextDepth }
        });
    });
    const replacement = coreProofPlanApply(term, premises, {
        id: hole.id,
        provenance: hole.provenance
    });
    const patch = createCoreProofPlanHoleReplacement(
        source.goalId,
        replacement
    );
    return Object.freeze({
        patch,
        plan: applyCoreProofPlanPatch(source.plan, patch),
        goalIds: Object.freeze(goalIds)
    });
};

const exactReplacement = (
    source: CoreObviousProofSourceInput,
    hole: CoreProofPlanHole,
    term: ReturnType<typeof kernelFree>
): {
    readonly patch: CoreProofPlanPatch;
    readonly plan: CoreProofPlan;
} => {
    const replacement = coreProofPlanExact(term, {
        id: hole.id,
        provenance: hole.provenance
    });
    const patch = createCoreProofPlanHoleReplacement(
        source.goalId,
        replacement
    );
    return Object.freeze({
        patch,
        plan: applyCoreProofPlanPatch(source.plan, patch)
    });
};

const traceStep = (
    ordinal: number,
    premise: CoreLfPremiseIndexEntrySnapshot,
    phase: CoreObviousProofTracePhase,
    outcome: CoreObviousProofTraceOutcome,
    extras: Omit<
        CoreObviousProofTraceStep,
        'ordinal' | 'premise' | 'phase' | 'outcome'
    > = {}
): CoreObviousProofTraceStep => Object.freeze({
    ordinal,
    premise: premise.symbol,
    phase,
    outcome,
    ...extras
});

const validateSourceInput = (
    input: CoreObviousProofSourceInput
): void => {
    if (!(input.index instanceof CoreLfCompiledPremiseIndex)) {
        fail(
            'INVALID_INPUT',
            'index',
            'Obvious-proof provider requires a compiled premise index'
        );
    }
    if (typeof input.goalId !== 'string' || !SAFE_GOAL_ID.test(input.goalId)) {
        fail(
            'INVALID_INPUT',
            'goalId',
            'Obvious-proof provider requires one stable source goal ID'
        );
    }
};

/** Propose checked exact or one-step-apply replacements for one named hole. */
export function proposeCoreObviousProofPlanPatches(
    input: CoreObviousProofProposalInput
): CoreObviousProofProposalReport {
    validateSourceInput(input);
    const allowedProfiles = normalizeAllowedProfiles(input.allowedProfiles);
    const seed = normalizeSeed(input.seed);
    const budget = normalizeBudget(input.budget);

    let baseline: FreshReplay;
    try {
        baseline = replayPlan(input.index, input.type, input.plan);
    } catch (error: unknown) {
        return fail(
            'BASE_REPLAY_FAILED',
            'plan',
            'Obvious-proof source did not replay in the exact index closure',
            error instanceof Error ? error : undefined
        );
    }
    const selected = selectFreshGoal(baseline, input.plan, input.goalId);
    const precondition = preconditionFor(input.index, baseline, selected);
    const search = searchCoreLfAccessiblePremises(
        input.index,
        {
            kind: 'conclusion-head',
            type: selected.raw.type,
            ambientDepth: selected.raw.contextDepth
        },
        { limit: budget.premiseLimit }
    );

    const trace: CoreObviousProofTraceStep[] = [];
    const candidates: CoreObviousProofCandidate[] = [];
    let premisesExamined = 0;
    let tacticAttempts = 0;
    let checkerReplays = 1;
    let termination: CoreObviousProofTermination | undefined;

    for (let index = 0; index < search.matches.length; index++) {
        if (candidates.length >= budget.candidateLimit) {
            termination = 'candidate-limit';
            break;
        }
        const premise = search.matches[index];
        const ordinal = index + 1;
        premisesExamined++;
        const compiled = input.index.resolve(premise.symbol);
        if (compiled === undefined) {
            return fail(
                'CANDIDATE_CHECK_FAILED',
                `search.matches[${index}]`,
                'Premise search result did not resolve in its compiled index'
            );
        }
        if (
            premise.link.kind !== 'free-declaration' ||
            !premise.status.startsWith('installed-')
        ) {
            trace.push(traceStep(
                ordinal,
                premise,
                'resolve',
                'skipped',
                {
                    diagnostic: {
                        code: 'UNSUPPORTED_PREMISE_LINK',
                        message: 'Premise is not an installed ordinary free declaration'
                    }
                }
            ));
            continue;
        }

        const term = kernelFree(
            premise.link.coreName,
            provenance(
                'derived',
                `obvious-proof premise ${premise.symbol.moduleId}.` +
                    premise.symbol.name,
                selected.hole.provenance.span
            )
        );
        const localTrace: CoreObviousProofTraceStep[] = [];

        if (tacticAttempts >= budget.tacticAttemptLimit) {
            termination = 'tactic-attempt-limit';
            break;
        }
        tacticAttempts++;
        checkerReplays++;
        const exact = exactReplacement(input, selected.hole, term);
        try {
            const replay = replayPlan(input.index, input.type, exact.plan);
            const step = traceStep(
                ordinal,
                premise,
                'exact-replay',
                'accepted',
                {
                    tacticAttempt: tacticAttempts,
                    introducedGoalCount: 0,
                    candidateIndex: candidates.length
                }
            );
            trace.push(step);
            localTrace.push(step);
            candidates.push(freezeData({
                revision:
                    CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.candidateRevision,
                providerRevision:
                    CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.revision,
                allowedProfiles,
                seed,
                operation: 'exact',
                premise,
                precondition,
                patch: exact.patch,
                generatedGoalIds: [],
                cost: {
                    premiseOrdinal: ordinal,
                    tacticAttempts: 1,
                    checkerReplays: 1,
                    introducedGoals: 0
                },
                trace: localTrace,
                result: replay.execution.snapshot
            }));
            continue;
        } catch (error: unknown) {
            if (!knownCandidateRejection(error)) {
                return fail(
                    'CANDIDATE_CHECK_FAILED',
                    `search.matches[${index}].exact`,
                    'Exact candidate replay failed unexpectedly',
                    error instanceof Error ? error : undefined
                );
            }
            const step = traceStep(
                ordinal,
                premise,
                'exact-replay',
                'rejected',
                {
                    tacticAttempt: tacticAttempts,
                    diagnostic: diagnostic(error)
                }
            );
            trace.push(step);
            localTrace.push(step);
        }

        if (tacticAttempts >= budget.tacticAttemptLimit) {
            termination = 'tactic-attempt-limit';
            break;
        }
        tacticAttempts++;
        checkerReplays++;
        let exploration: FreshReplay;
        try {
            exploration = replayPlan(input.index, input.type, input.plan);
        } catch (error: unknown) {
            return fail(
                'CANDIDATE_CHECK_FAILED',
                `search.matches[${index}].apply.base`,
                'Fresh apply exploration could not reproduce the base replay',
                error instanceof Error ? error : undefined
            );
        }
        const explorationGoal = selectFreshGoal(
            exploration,
            input.plan,
            input.goalId
        );
        let introduced: readonly CoreProofGoal[];
        try {
            introduced = exploration.refiner.apply(
                explorationGoal.raw.identity,
                term,
                selected.hole.provenance
            ).introducedGoals;
        } catch (error: unknown) {
            if (!knownCandidateRejection(error)) {
                return fail(
                    'CANDIDATE_CHECK_FAILED',
                    `search.matches[${index}].apply`,
                    'Apply exploration failed unexpectedly',
                    error instanceof Error ? error : undefined
                );
            }
            const step = traceStep(
                ordinal,
                premise,
                'apply-explore',
                'rejected',
                {
                    tacticAttempt: tacticAttempts,
                    diagnostic: diagnostic(error)
                }
            );
            trace.push(step);
            localTrace.push(step);
            continue;
        }

        if (introduced.length > budget.introducedGoalLimit) {
            const step = traceStep(
                ordinal,
                premise,
                'apply-explore',
                'bounded',
                {
                    tacticAttempt: tacticAttempts,
                    introducedGoalCount: introduced.length,
                    diagnostic: {
                        code: 'INTRODUCED_GOAL_LIMIT',
                        message: `Application introduced ${introduced.length} ` +
                            `goals, above the bound ` +
                            `${budget.introducedGoalLimit}`
                    }
                }
            );
            trace.push(step);
            localTrace.push(step);
            continue;
        }

        const exploredStep = traceStep(
            ordinal,
            premise,
            'apply-explore',
            'accepted',
            {
                tacticAttempt: tacticAttempts,
                introducedGoalCount: introduced.length
            }
        );
        trace.push(exploredStep);
        localTrace.push(exploredStep);
        const applied = applyReplacement(
            input,
            selected.hole,
            term,
            introduced
        );
        checkerReplays++;
        let verified: FreshReplay;
        try {
            verified = replayPlan(input.index, input.type, applied.plan);
        } catch (error: unknown) {
            return fail(
                'CANDIDATE_CHECK_FAILED',
                `search.matches[${index}].apply.replay`,
                'One-step apply succeeded but its explicit plan did not replay',
                error instanceof Error ? error : undefined
            );
        }
        const replayedStep = traceStep(
            ordinal,
            premise,
            'candidate-replay',
            'accepted',
            {
                introducedGoalCount: introduced.length,
                candidateIndex: candidates.length
            }
        );
        trace.push(replayedStep);
        localTrace.push(replayedStep);
        candidates.push(freezeData({
            revision: CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.candidateRevision,
            providerRevision: CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.revision,
            allowedProfiles,
            seed,
            operation: 'apply',
            premise,
            precondition,
            patch: applied.patch,
            generatedGoalIds: applied.goalIds,
            cost: {
                premiseOrdinal: ordinal,
                tacticAttempts: 2,
                checkerReplays: 3,
                introducedGoals: introduced.length
            },
            trace: localTrace,
            result: verified.execution.snapshot
        }));
    }

    if (termination === undefined) {
        termination = search.truncated
            ? 'premise-limit'
            : 'exhausted-search';
    }
    return freezeData({
        revision: CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.reportRevision,
        providerRevision: CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.revision,
        allowedProfiles,
        seed,
        budget,
        precondition,
        search,
        trace,
        candidates,
        counts: {
            premisesExamined,
            tacticAttempts,
            checkerReplays,
            candidates: candidates.length
        },
        termination
    });
}

const sameJson = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

const assertCandidateShape = (
    input: CoreObviousProofCandidateReplayInput
): void => {
    const candidate = input.candidate;
    if (
        candidate === null ||
        typeof candidate !== 'object' ||
        candidate.revision !==
            CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.candidateRevision ||
        candidate.providerRevision !==
            CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.revision ||
        candidate.premise === null ||
        typeof candidate.premise !== 'object' ||
        candidate.premise.symbol === null ||
        typeof candidate.premise.symbol !== 'object' ||
        typeof candidate.premise.symbol.moduleId !== 'string' ||
        typeof candidate.premise.symbol.name !== 'string' ||
        candidate.precondition === null ||
        typeof candidate.precondition !== 'object' ||
        candidate.precondition.revision !==
            CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.preconditionRevision ||
        typeof candidate.precondition.indexSnapshot !== 'string' ||
        typeof candidate.precondition.checkedTarget !== 'string' ||
        candidate.precondition.baseState?.revision !==
            'emdash-proof-state-v2' ||
        candidate.precondition.selectedGoal === null ||
        typeof candidate.precondition.selectedGoal !== 'object' ||
        !Array.isArray(candidate.allowedProfiles) ||
        candidate.allowedProfiles.length !== 1 ||
        candidate.allowedProfiles[0] !==
            CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.revision ||
        typeof candidate.seed !== 'string' ||
        !Array.isArray(candidate.generatedGoalIds) ||
        candidate.result?.revision !== 'emdash-proof-state-v2' ||
        candidate.patch?.revision !== CORE_PROOF_PLAN_PATCH_PROFILE.revision ||
        candidate.patch.kind !== 'replace-hole' ||
        candidate.patch.goalId !== input.goalId
    ) {
        fail(
            'INVALID_CANDIDATE',
            'candidate',
            'Candidate does not use the current exact provider/patch contract'
        );
    }
    const compiled = input.index.resolve(candidate.premise.symbol);
    const link = candidate.premise.link;
    if (
        compiled === undefined ||
        !sameJson(compiled.entry, candidate.premise) ||
        !candidate.premise.status.startsWith('installed-')
    ) {
        fail(
            'INVALID_CANDIDATE',
            'candidate.premise',
            'Candidate premise is not the same accessible installed declaration'
        );
    }
    const coreName = link.kind === 'free-declaration'
        ? link.coreName
        : fail(
            'INVALID_CANDIDATE',
            'candidate.premise.link',
            'Candidate premise is not an ordinary free declaration'
        );
    const replacement = candidate.patch.replacement;
    if (candidate.operation === 'exact') {
        if (
            replacement.tag !== 'exact' ||
            replacement.solution.tag !== 'reference' ||
            replacement.solution.name !== coreName ||
            candidate.generatedGoalIds.length !== 0
        ) {
            fail(
                'INVALID_CANDIDATE',
                'candidate.patch.replacement',
                'Exact candidate does not reference its recorded premise'
            );
        }
        return;
    }
    if (
        candidate.operation !== 'apply' ||
        replacement.tag !== 'apply' ||
        replacement.callee.tag !== 'reference' ||
        replacement.callee.name !== coreName ||
        replacement.premises.length !== candidate.generatedGoalIds.length ||
        replacement.premises.some((premise, index) =>
            premise.tag !== 'hole' ||
            premise.goalId !== candidate.generatedGoalIds[index]
        )
    ) {
        fail(
            'INVALID_CANDIDATE',
            'candidate.patch.replacement',
            'Apply candidate does not expose exactly its recorded premise holes'
        );
    }
};

/** Recheck one proposal against current source and exact accessible scope. */
export function replayCoreObviousProofCandidate(
    input: CoreObviousProofCandidateReplayInput
): CoreObviousProofCandidateReplay {
    validateSourceInput(input);
    assertCandidateShape(input);
    let baseline: FreshReplay;
    try {
        baseline = replayPlan(input.index, input.type, input.plan);
    } catch (error: unknown) {
        return fail(
            'BASE_REPLAY_FAILED',
            'plan',
            'Current source no longer replays for candidate acceptance',
            error instanceof Error ? error : undefined
        );
    }
    const selected = selectFreshGoal(baseline, input.plan, input.goalId);
    const current = preconditionFor(input.index, baseline, selected);
    if (
        current.indexSnapshot !== input.candidate.precondition.indexSnapshot ||
        current.checkedTarget !== input.candidate.precondition.checkedTarget ||
        serializeCoreProofPlanState(current.baseState) !==
            serializeCoreProofPlanState(
                input.candidate.precondition.baseState
            ) ||
        !sameJson(
            current.selectedGoal,
            input.candidate.precondition.selectedGoal
        )
    ) {
        return fail(
            'STALE_CANDIDATE',
            'candidate.precondition',
            'Candidate precondition differs from the current verified source'
        );
    }

    let plan: CoreProofPlan;
    try {
        plan = applyCoreProofPlanPatch(input.plan, input.candidate.patch);
    } catch (error: unknown) {
        return fail(
            'INVALID_CANDIDATE',
            'candidate.patch',
            'Candidate patch cannot be applied to the current source',
            error instanceof Error ? error : undefined
        );
    }
    let replay: FreshReplay;
    try {
        replay = replayPlan(input.index, input.type, plan);
    } catch (error: unknown) {
        return fail(
            'CANDIDATE_CHECK_FAILED',
            'candidate.patch',
            'Candidate patch did not pass fresh proof replay',
            error instanceof Error ? error : undefined
        );
    }
    if (
        serializeCoreProofPlanState(replay.execution.snapshot) !==
        serializeCoreProofPlanState(input.candidate.result)
    ) {
        return fail(
            'STALE_CANDIDATE',
            'candidate.result',
            'Fresh candidate result differs from its recorded checked result'
        );
    }
    return Object.freeze({
        revision: CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.replayRevision,
        plan,
        execution: replay.execution
    });
}

/** Deterministic, diff-friendly proposal report serialization. */
export const serializeCoreObviousProofProposalReport = (
    report: CoreObviousProofProposalReport
): string => `${JSON.stringify(report, null, 2)}\n`;
