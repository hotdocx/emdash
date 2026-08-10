/** Focused OBVIOUS-PROOF-7 patch and bounded-provider tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CoreLfCompiledDeclarationWorkspace,
    CoreLfModuleSpec,
    CoreLfTransferDeclarationLinkage,
    CoreLfTransferPolicyOverlay,
    compileCoreLfDeclarationWorkspace,
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    createCoreLfDeclarationWorkspace,
    createCoreLfModuleSpec,
    createCoreLfTransferDeclarationLinkage,
    createCoreLfTransferPolicyOverlay,
    coreOwnerSignatureType,
    kernelFree,
    provenance
} from '../src/v3_2';
import {
    createCoreLfAccessiblePremiseIndex
} from '../src/v3_2/lf_premise_index';
import {
    CORE_OBVIOUS_PROOF_PROVIDER_PROFILE,
    CoreObviousProofCandidate,
    CoreObviousProofProviderError,
    proposeCoreObviousProofPlanPatches,
    replayCoreObviousProofCandidate,
    serializeCoreObviousProofProposalReport
} from '../src/v3_2/proof_obvious';
import {
    CoreProofPlan,
    coreProofPlanApply,
    coreProofPlanExact,
    coreProofPlanHole
} from '../src/v3_2/proof_plan';
import {
    CoreProofPlanPatchError,
    applyCoreProofPlanPatch,
    createCoreProofPlanHoleReplacement
} from '../src/v3_2/proof_plan_patch';

const providerModuleId = 'fixture.obvious_a_provider';
const rootModuleId = 'fixture.obvious_b_root';

const grpd = coreLfQualifiedSymbol(providerModuleId, 'Grpd');
const cat = coreLfQualifiedSymbol(providerModuleId, 'Cat');
const obj = coreLfQualifiedSymbol(providerModuleId, 'Obj');
const propositionP = coreLfQualifiedSymbol(providerModuleId, 'P');
const propositionQ = coreLfQualifiedSymbol(providerModuleId, 'Q');
const factP = coreLfQualifiedSymbol(providerModuleId, 'p');
const implication = coreLfQualifiedSymbol(providerModuleId, 'p_to_q');
const factQ = coreLfQualifiedSymbol(providerModuleId, 'q');
const alternateQ = coreLfQualifiedSymbol(providerModuleId, 'q_alt');
const twoPremise = coreLfQualifiedSymbol(providerModuleId, 'two_to_q');
const privateQ = coreLfQualifiedSymbol(providerModuleId, 'private_q');
const localQ = coreLfQualifiedSymbol(rootModuleId, 'local_q');

const pCore = 'obvious_P';
const qCore = 'obvious_Q';
const factPCore = 'obvious_p';
const implicationCore = 'obvious_p_to_q';
const factQCore = 'obvious_q';
const alternateQCore = 'obvious_q_alt';
const twoPremiseCore = 'obvious_two_to_q';
const privateQCore = 'obvious_private_q';
const localQCore = 'obvious_local_q';

const hash = (digit: string): string => `sha256:${digit.repeat(64)}`;

interface Fixture {
    readonly module: CoreLfModuleSpec;
    readonly policy: CoreLfTransferPolicyOverlay;
    readonly linkage: CoreLfTransferDeclarationLinkage;
}

const source = (authorityPath: string, sourceFragment: string) => ({
    authorityPath,
    sourceFragment
});

const modifiers = (
    visibility: 'public' | 'protected' | 'private'
) => ({
    visibility,
    rigidity: 'ordinary' as const,
    sourceOpacity: 'opaque' as const
});

const providerFixture = (): Fixture => {
    const authorityPath = 'tests/fixtures/obvious_provider.lp';
    const declarations = [
        {
            order: 0,
            symbol: grpd,
            type: { tag: 'type' as const },
            body: coreLfTransferAbsentBody(),
            modifiers: modifiers('public'),
            provenance: source(authorityPath, 'symbol Grpd : TYPE;')
        },
        {
            order: 1,
            symbol: cat,
            type: { tag: 'type' as const },
            body: coreLfTransferAbsentBody(),
            modifiers: modifiers('public'),
            provenance: source(authorityPath, 'symbol Cat : TYPE;')
        },
        {
            order: 2,
            symbol: obj,
            type: {
                tag: 'pi' as const,
                binder: {
                    hint: 'A',
                    mode: {
                        plicity: 'explicit' as const,
                        variation: 'functorial' as const
                    },
                    type: { tag: 'global' as const, symbol: cat }
                },
                body: { tag: 'global' as const, symbol: grpd }
            },
            body: coreLfTransferAbsentBody(),
            modifiers: modifiers('public'),
            provenance: source(
                authorityPath,
                'symbol Obj : Π A:Cat, Grpd;'
            )
        },
        {
            order: 3,
            symbol: propositionP,
            type: { tag: 'type' as const },
            body: coreLfTransferAbsentBody(),
            modifiers: modifiers('public'),
            provenance: source(authorityPath, 'symbol P : TYPE;')
        },
        {
            order: 4,
            symbol: propositionQ,
            type: { tag: 'type' as const },
            body: coreLfTransferAbsentBody(),
            modifiers: modifiers('public'),
            provenance: source(authorityPath, 'symbol Q : TYPE;')
        },
        {
            order: 5,
            symbol: factP,
            type: { tag: 'global' as const, symbol: propositionP },
            body: coreLfTransferAbsentBody(),
            modifiers: modifiers('public'),
            provenance: source(authorityPath, 'symbol p : P;')
        },
        {
            order: 6,
            symbol: implication,
            type: {
                tag: 'pi' as const,
                binder: {
                    hint: 'h',
                    mode: {
                        plicity: 'explicit' as const,
                        variation: 'functorial' as const
                    },
                    type: { tag: 'global' as const, symbol: propositionP }
                },
                body: { tag: 'global' as const, symbol: propositionQ }
            },
            body: coreLfTransferAbsentBody(),
            modifiers: modifiers('public'),
            provenance: source(
                authorityPath,
                'symbol p_to_q : Π h:P, Q;'
            )
        },
        {
            order: 7,
            symbol: factQ,
            type: { tag: 'global' as const, symbol: propositionQ },
            body: coreLfTransferAbsentBody(),
            modifiers: modifiers('public'),
            provenance: source(authorityPath, 'symbol q : Q;')
        },
        {
            order: 8,
            symbol: alternateQ,
            type: { tag: 'global' as const, symbol: propositionQ },
            body: coreLfTransferAbsentBody(),
            modifiers: modifiers('public'),
            provenance: source(authorityPath, 'symbol q_alt : Q;')
        },
        {
            order: 9,
            symbol: twoPremise,
            type: {
                tag: 'pi' as const,
                binder: {
                    hint: 'left',
                    mode: {
                        plicity: 'explicit' as const,
                        variation: 'functorial' as const
                    },
                    type: { tag: 'global' as const, symbol: propositionP }
                },
                body: {
                    tag: 'pi' as const,
                    binder: {
                        hint: 'right',
                        mode: {
                            plicity: 'explicit' as const,
                            variation: 'functorial' as const
                        },
                        type: {
                            tag: 'global' as const,
                            symbol: propositionP
                        }
                    },
                    body: { tag: 'global' as const, symbol: propositionQ }
                }
            },
            body: coreLfTransferAbsentBody(),
            modifiers: modifiers('public'),
            provenance: source(
                authorityPath,
                'symbol two_to_q : Π left:P, Π right:P, Q;'
            )
        },
        {
            order: 10,
            symbol: privateQ,
            type: { tag: 'global' as const, symbol: propositionQ },
            body: coreLfTransferAbsentBody(),
            modifiers: modifiers('private'),
            provenance: source(
                authorityPath,
                'private symbol private_q : Q;'
            )
        }
    ];
    const module = createCoreLfModuleSpec({
        revision: 'obvious-provider-1',
        moduleId: providerModuleId,
        fragmentId: 'declarations',
        authorityPath,
        sourceSha256: hash('a'),
        dependencies: [],
        externalSymbols: [],
        declarations,
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    return {
        module,
        policy: createCoreLfTransferPolicyOverlay(module, {
            revision: 'obvious-provider-policy-1',
            moduleRevision: module.revision,
            entries: declarations.map((declaration, index) => ({
                order: index,
                target: {
                    kind: 'declaration' as const,
                    symbol: declaration.symbol
                },
                policy: index <= 2
                    ? 'conformance-only' as const
                    : 'opaque-signature' as const,
                evidence: 'OBVIOUS-PROOF-7 standalone provider fixture'
            }))
        }),
        linkage: createCoreLfTransferDeclarationLinkage(module, {
            revision: 'obvious-provider-linkage-1',
            moduleRevision: module.revision,
            entries: declarations.map((declaration, index) => {
                if (index === 0) {
                    return {
                        order: index,
                        symbol: declaration.symbol,
                        kind: 'core-owner' as const,
                        owner: 'groupoid-universe' as const
                    };
                }
                if (index === 1) {
                    return {
                        order: index,
                        symbol: declaration.symbol,
                        kind: 'core-owner' as const,
                        owner: 'category-universe' as const
                    };
                }
                if (index === 2) {
                    return {
                        order: index,
                        symbol: declaration.symbol,
                        kind: 'core-owner' as const,
                        owner: 'object-classifier' as const
                    };
                }
                const coreNames = [
                    pCore,
                    qCore,
                    factPCore,
                    implicationCore,
                    factQCore,
                    alternateQCore,
                    twoPremiseCore,
                    privateQCore
                ];
                return {
                    order: index,
                    symbol: declaration.symbol,
                    kind: 'free-declaration' as const,
                    coreName: coreNames[index - 3],
                    backendName: declaration.symbol.name
                };
            })
        })
    };
};

const rootFixture = (): Fixture => {
    const authorityPath = 'tests/fixtures/obvious_root.lp';
    const module = createCoreLfModuleSpec({
        revision: 'obvious-root-1',
        moduleId: rootModuleId,
        fragmentId: 'declarations',
        authorityPath,
        sourceSha256: hash('b'),
        dependencies: [providerModuleId],
        externalSymbols: [{
            symbol: propositionQ,
            availability: 'dependency-module'
        }],
        declarations: [{
            order: 0,
            symbol: localQ,
            type: { tag: 'global', symbol: propositionQ },
            body: coreLfTransferAbsentBody(),
            modifiers: modifiers('private'),
            provenance: source(
                authorityPath,
                'private symbol local_q : Q;'
            )
        }],
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    return {
        module,
        policy: createCoreLfTransferPolicyOverlay(module, {
            revision: 'obvious-root-policy-1',
            moduleRevision: module.revision,
            entries: [{
                order: 0,
                target: { kind: 'declaration', symbol: localQ },
                policy: 'opaque-signature',
                evidence: 'OBVIOUS-PROOF-7 root-local premise fixture'
            }]
        }),
        linkage: createCoreLfTransferDeclarationLinkage(module, {
            revision: 'obvious-root-linkage-1',
            moduleRevision: module.revision,
            entries: [
                {
                    order: 0,
                    symbol: propositionQ,
                    kind: 'free-declaration',
                    coreName: qCore,
                    backendName: propositionQ.name
                },
                {
                    order: 1,
                    symbol: localQ,
                    kind: 'free-declaration',
                    coreName: localQCore,
                    backendName: localQ.name
                }
            ]
        })
    };
};

const compileFixture = (): CoreLfCompiledDeclarationWorkspace =>
    compileCoreLfDeclarationWorkspace(createCoreLfDeclarationWorkspace({
        revision: 'obvious-workspace-1',
        modules: [rootFixture(), providerFixture()]
    }));

const planProvenance = provenance(
    'surface',
    'OBVIOUS-PROOF-7 selected source hole'
);

const rootPlan = (): CoreProofPlan => coreProofPlanHole('goal', {
    id: 'goal.node',
    provenance: planProvenance
});

const qType = () => kernelFree(qCore, planProvenance);
const pType = () => kernelFree(pCore, planProvenance);

const report = () => {
    const index = createCoreLfAccessiblePremiseIndex(
        compileFixture(),
        rootModuleId
    );
    return {
        index,
        plan: rootPlan(),
        report: proposeCoreObviousProofPlanPatches({
            index,
            type: qType(),
            plan: rootPlan(),
            goalId: 'goal',
            seed: 'fixture-seed'
        })
    };
};

const display = (candidate: CoreObviousProofCandidate): string =>
    `${candidate.premise.symbol.moduleId}.${candidate.premise.symbol.name}`;

const candidateByName = (
    candidates: readonly CoreObviousProofCandidate[],
    name: string
): CoreObviousProofCandidate => {
    const candidate = candidates.find(entry => entry.premise.symbol.name === name);
    assert.notEqual(candidate, undefined, `missing candidate ${name}`);
    return candidate;
};

const captureProviderError = (
    action: () => unknown,
    code: CoreObviousProofProviderError['code']
): CoreObviousProofProviderError => {
    let captured: CoreObviousProofProviderError | undefined;
    assert.throws(action, error => {
        if (error instanceof CoreObviousProofProviderError) captured = error;
        return error instanceof CoreObviousProofProviderError &&
            error.code === code;
    });
    assert.notEqual(captured, undefined);
    return captured;
};

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(assertDeepFrozen);
};

describe('OBVIOUS-PROOF-7 immutable proof-plan patches', () => {
    it('replaces exactly one nested stable hole without mutating source', () => {
        const sourcePlan = coreProofPlanApply(
            kernelFree(implicationCore, planProvenance),
            [
                coreProofPlanHole('left', {
                    provenance: planProvenance
                }),
                coreProofPlanHole('right', {
                    provenance: planProvenance
                })
            ],
            { id: 'apply.node', provenance: planProvenance }
        );
        const replacement = coreProofPlanExact(
            kernelFree(factPCore, planProvenance)
        );
        const patch = createCoreProofPlanHoleReplacement(
            'left',
            replacement
        );
        const result = applyCoreProofPlanPatch(sourcePlan, patch);
        assert.equal(sourcePlan.premises[0].tag, 'hole');
        assert.equal(result.tag, 'apply');
        assert.equal(result.tag === 'apply' && result.premises[0].tag, 'exact');
        assert.equal(result.tag === 'apply' && result.premises[1].tag, 'hole');

        assert.throws(
            () => applyCoreProofPlanPatch(
                sourcePlan,
                createCoreProofPlanHoleReplacement(
                    'missing',
                    replacement
                )
            ),
            error => error instanceof CoreProofPlanPatchError &&
                error.code === 'TARGET_NOT_FOUND'
        );
        assert.throws(
            () => applyCoreProofPlanPatch(
                sourcePlan,
                createCoreProofPlanHoleReplacement(
                    'left',
                    coreProofPlanHole('right', {
                        provenance: planProvenance
                    })
                )
            ),
            error => error instanceof CoreProofPlanPatchError &&
                error.code === 'INVALID_PATCH'
        );
    });
});

describe('OBVIOUS-PROOF-7 bounded exact/apply provider', () => {
    it('returns deterministic checked exact and one-step apply candidates', () => {
        const fixture = report();
        const proposals = fixture.report;
        assert.equal(
            CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.applyDepth,
            1
        );
        assert.deepEqual(
            proposals.candidates.map(candidate => [
                display(candidate),
                candidate.operation
            ]),
            [
                [`${providerModuleId}.p_to_q`, 'apply'],
                [`${providerModuleId}.q`, 'exact'],
                [`${providerModuleId}.q_alt`, 'exact'],
                [`${providerModuleId}.two_to_q`, 'apply'],
                [`${rootModuleId}.local_q`, 'exact']
            ]
        );
        assert.equal(
            proposals.candidates.some(candidate =>
                candidate.premise.symbol.name === privateQ.name
            ),
            false
        );
        const implicationCandidate = candidateByName(
            proposals.candidates,
            implication.name
        );
        assert.deepEqual(
            implicationCandidate.generatedGoalIds,
            ['goal.obvious.p1']
        );
        assert.equal(implicationCandidate.result.status, 'incomplete');
        assert.deepEqual(
            implicationCandidate.result.goals.map(goal => [
                goal.id,
                goal.target
            ]),
            [['goal.obvious.p1', pCore]]
        );
        assert.equal(
            implicationCandidate.trace[0].phase,
            'exact-replay'
        );
        assert.equal(implicationCandidate.trace[0].outcome, 'rejected');
        assert.equal(
            implicationCandidate.trace.at(-1)?.phase,
            'candidate-replay'
        );

        const exact = candidateByName(proposals.candidates, factQ.name);
        assert.equal(exact.result.status, 'complete');
        assert.equal(exact.generatedGoalIds.length, 0);
        assert.equal(proposals.termination, 'exhausted-search');
        assert.equal(proposals.search.truncated, false);
        assert.equal(proposals.counts.candidates, 5);
        assertDeepFrozen(proposals);
    });

    it('replays current candidates and rejects stale or forged evidence', () => {
        const fixture = report();
        const exact = candidateByName(fixture.report.candidates, factQ.name);
        const applied = candidateByName(
            fixture.report.candidates,
            implication.name
        );
        const exactReplay = replayCoreObviousProofCandidate({
            index: fixture.index,
            type: qType(),
            plan: fixture.plan,
            goalId: 'goal',
            candidate: exact
        });
        assert.equal(exactReplay.execution.state.status, 'complete');
        const applyReplay = replayCoreObviousProofCandidate({
            index: fixture.index,
            type: qType(),
            plan: fixture.plan,
            goalId: 'goal',
            candidate: applied
        });
        assert.equal(applyReplay.execution.state.status, 'incomplete');

        captureProviderError(
            () => replayCoreObviousProofCandidate({
                index: fixture.index,
                type: pType(),
                plan: fixture.plan,
                goalId: 'goal',
                candidate: exact
            }),
            'STALE_CANDIDATE'
        );
        captureProviderError(
            () => replayCoreObviousProofCandidate({
                index: fixture.index,
                type: qType(),
                plan: fixture.plan,
                goalId: 'goal',
                candidate: {
                    ...exact,
                    result: applied.result
                }
            }),
            'STALE_CANDIDATE'
        );
        const forgedPatch = createCoreProofPlanHoleReplacement(
            'goal',
            coreProofPlanExact(kernelFree(privateQCore, planProvenance), {
                id: 'goal.node',
                provenance: planProvenance
            })
        );
        captureProviderError(
            () => replayCoreObviousProofCandidate({
                index: fixture.index,
                type: qType(),
                plan: fixture.plan,
                goalId: 'goal',
                candidate: { ...exact, patch: forgedPatch }
            }),
            'INVALID_CANDIDATE'
        );
    });

    it('enforces independent finite budgets without recursive discharge', () => {
        const index = createCoreLfAccessiblePremiseIndex(
            compileFixture(),
            rootModuleId
        );
        const limited = proposeCoreObviousProofPlanPatches({
            index,
            type: qType(),
            plan: rootPlan(),
            goalId: 'goal',
            budget: { premiseLimit: 1 }
        });
        assert.equal(limited.search.truncated, true);
        assert.equal(limited.termination, 'premise-limit');
        assert.equal(limited.candidates.length, 1);
        assert.equal(limited.candidates[0].operation, 'apply');
        assert.equal(limited.candidates[0].result.status, 'incomplete');

        const oneAttempt = proposeCoreObviousProofPlanPatches({
            index,
            type: qType(),
            plan: rootPlan(),
            goalId: 'goal',
            budget: { tacticAttemptLimit: 1 }
        });
        assert.equal(oneAttempt.termination, 'tactic-attempt-limit');
        assert.equal(oneAttempt.candidates.length, 0);
        assert.equal(oneAttempt.counts.tacticAttempts, 1);

        const noIntroducedGoals = proposeCoreObviousProofPlanPatches({
            index,
            type: qType(),
            plan: rootPlan(),
            goalId: 'goal',
            budget: { introducedGoalLimit: 0 }
        });
        assert.equal(
            noIntroducedGoals.trace.some(step =>
                step.outcome === 'bounded' &&
                step.diagnostic?.code === 'INTRODUCED_GOAL_LIMIT'
            ),
            true
        );
        assert.equal(
            noIntroducedGoals.candidates.every(candidate =>
                candidate.operation === 'exact'
            ),
            true
        );

        const noCandidates = proposeCoreObviousProofPlanPatches({
            index,
            type: qType(),
            plan: rootPlan(),
            goalId: 'goal',
            budget: { candidateLimit: 0 }
        });
        assert.equal(noCandidates.termination, 'candidate-limit');
        assert.equal(noCandidates.counts.premisesExamined, 0);
    });

    it('traces unsupported owner links instead of inventing terms', () => {
        const index = createCoreLfAccessiblePremiseIndex(
            compileFixture(),
            rootModuleId
        );
        const ownerType = coreOwnerSignatureType(
            'object-classifier',
            planProvenance
        );
        const proposals = proposeCoreObviousProofPlanPatches({
            index,
            type: ownerType,
            plan: rootPlan(),
            goalId: 'goal'
        });
        assert.equal(proposals.candidates.length, 0);
        assert.deepEqual(
            proposals.trace.map(step => [
                step.premise.name,
                step.phase,
                step.outcome,
                step.diagnostic?.code
            ]),
            [[
                obj.name,
                'resolve',
                'skipped',
                'UNSUPPORTED_PREMISE_LINK'
            ]]
        );
    });

    it('is byte-stable and rejects invalid profile, seed, and budgets', () => {
        const first = report().report;
        const second = report().report;
        assert.equal(
            serializeCoreObviousProofProposalReport(first),
            serializeCoreObviousProofProposalReport(second)
        );
        const index = createCoreLfAccessiblePremiseIndex(
            compileFixture(),
            rootModuleId
        );
        captureProviderError(
            () => proposeCoreObviousProofPlanPatches({
                index,
                type: qType(),
                plan: rootPlan(),
                goalId: 'goal',
                allowedProfiles: [
                    CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.revision,
                    CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.revision
                ]
            }),
            'INVALID_ALLOWED_PROFILE'
        );
        captureProviderError(
            () => proposeCoreObviousProofPlanPatches({
                index,
                type: qType(),
                plan: rootPlan(),
                goalId: 'goal',
                seed: 'bad\nseed'
            }),
            'INVALID_SEED'
        );
        captureProviderError(
            () => proposeCoreObviousProofPlanPatches({
                index,
                type: qType(),
                plan: rootPlan(),
                goalId: 'goal',
                budget: {
                    premiseLimit:
                        CORE_OBVIOUS_PROOF_PROVIDER_PROFILE
                            .maximumBudget.premiseLimit + 1
                }
            }),
            'INVALID_BUDGET'
        );
    });
});
