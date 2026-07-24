/**
 * Focused pre-review tests for the exact H-DTTLF-01 profile.
 */

import assert from 'node:assert/strict';
import {
    readFileSync
} from 'node:fs';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT
} from '../src/v3_2/lf_checker';
import {
    CORE_LF_CONTINUATION_PROFILE_PROPOSAL,
    CoreLfProfileProposalError,
    validateCoreLfProfileProposal
} from '../src/v3_2/lf_profile_proposal';
import {
    CORE_MVP_MANIFEST
} from '../src/v3_2/manifest';
import {
    CORE_MVP_RUNTIME_PROGRAM
} from '../src/v3_2/runtime';

const cloneProfile = (): any =>
    JSON.parse(JSON.stringify(CORE_LF_CONTINUATION_PROFILE_PROPOSAL));

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(assertDeepFrozen);
};

const assertProfileError = (
    mutate: (profile: any) => void,
    expectedCode: CoreLfProfileProposalError['code']
): void => {
    const profile = cloneProfile();
    mutate(profile);
    assert.throws(
        () => validateCoreLfProfileProposal(profile),
        error =>
            error instanceof CoreLfProfileProposalError &&
            error.code === expectedCode
    );
};

describe('TypeScript v3.2 H-DTTLF-01 outer-LF profile proposal', () => {
    it('freezes the exact continuation-only conversion profile', () => {
        const profile = CORE_LF_CONTINUATION_PROFILE_PROPOSAL;
        assert.equal(profile.revision, 'LF-PROFILE-1');
        assert.equal(
            profile.status,
            'proposal-awaiting-h-dttlf-01'
        );
        assert.equal(profile.reviewGate, 'H-DTTLF-01');
        assert.deepEqual(
            profile.conversion.transitionOrder,
            ['zonk', 'beta', 'delta', 'reviewed-runtime']
        );
        assert.equal(
            profile.conversion.defaultStepLimit,
            CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT
        );
        assert.equal(
            profile.conversion.budgetScope,
            'global-across-both-sides-and-all-congruence-paths'
        );
        assert.equal(profile.conversion.eta, 'disabled');
        assert.equal(
            profile.conversion.arbitraryUserRules,
            'excluded'
        );
    });

    it('records the acyclic declaration and scoped-surface policies', () => {
        const profile = CORE_LF_CONTINUATION_PROFILE_PROPOSAL;
        assert.deepEqual(profile.declarations, {
            storage: 'persistent-immutable-environment',
            defaultTransparency: 'opaque',
            transparentAssumption: 'rejected',
            bodyCheckingEnvironment: 'strictly-preceding',
            bodyDependencyOrder: 'strictly-earlier-ordinals',
            selfReference: 'rejected',
            forwardReference: 'rejected',
            globalRegistry: 'absent'
        });
        assert.equal(profile.checker.annotatedLambdaInference, true);
        assert.equal(profile.checker.unannotatedLambdaInference, false);
        assert.equal(
            profile.checker.rigidConstraintRevisit,
            'combined-conversion'
        );
        assert.equal(profile.surface.callbackStorage, 'none');
        assert.equal(profile.surface.trustedLowering, 'de-bruijn-core');
        assert.equal(profile.surface.let, 'annotated-lambda-beta-sugar');
    });

    it('pins only the exact reviewed MVP runtime subprogram', () => {
        const component =
            CORE_LF_CONTINUATION_PROFILE_PROPOSAL
                .reviewedRuntimeComponent;
        assert.deepEqual(component, {
            manifestRevision: CORE_MVP_MANIFEST.revision,
            manifestContentHash: CORE_MVP_MANIFEST.contentHash,
            ruleIds: CORE_MVP_RUNTIME_PROGRAM.rules.map(rule => rule.id),
            authority: 'exact-reviewed-runtime-subprogram-only'
        });
    });

    it('matches the implemented transition selection order', () => {
        const source = readFileSync(
            'src/v3_2/lf_conversion.ts',
            'utf8'
        );
        const zonk = source.indexOf('const zonked = session.zonk');
        const beta = source.indexOf(
            'const beta = coreLfBetaReduceHead'
        );
        const delta = source.indexOf(
            'const delta = coreLfDeltaReduceHead'
        );
        const runtime = source.indexOf(
            'const runtime = coreRuntimeRewriteHead'
        );
        assert.ok(zonk >= 0);
        assert.ok(zonk < beta);
        assert.ok(beta < delta);
        assert.ok(delta < runtime);
    });

    it('stays out of the browser and preserves all withheld claims', () => {
        const browser = readFileSync('src/v3_2/browser.ts', 'utf8');
        assert.doesNotMatch(
            browser,
            /lf_profile|CoreLf|coreLf|LF_CONTINUATION/
        );
        assert.deepEqual(
            CORE_LF_CONTINUATION_PROFILE_PROPOSAL.claims,
            {
                boundedStopping: 'implemented',
                unrestrictedNormalization: 'withheld',
                termination: 'withheld',
                confluence: 'withheld',
                typescriptSubjectReduction: 'withheld',
                performanceSla: 'withheld'
            }
        );
        assert.equal(
            CORE_LF_CONTINUATION_PROFILE_PROPOSAL
                .integrationBoundary.frozenMvpMutation,
            false
        );
    });

    it('is deeply frozen and validates unchanged', () => {
        assertDeepFrozen(CORE_LF_CONTINUATION_PROFILE_PROPOSAL);
        assert.doesNotThrow(() => validateCoreLfProfileProposal());
    });

    it('rejects boundary, conversion, declaration, and surface drift', () => {
        assertProfileError(
            profile => {
                profile.status = 'approved';
            },
            'INVALID_PROFILE_BOUNDARY'
        );
        assertProfileError(
            profile => {
                profile.conversion.transitionOrder.reverse();
            },
            'INVALID_CONVERSION_PROFILE'
        );
        assertProfileError(
            profile => {
                profile.declarations.defaultTransparency = 'transparent';
            },
            'INVALID_DECLARATION_POLICY'
        );
        assertProfileError(
            profile => {
                profile.surface.callbackStorage = 'closures';
            },
            'INVALID_CHECKER_SURFACE'
        );
    });

    it('rejects runtime, claim, and exact-content drift', () => {
        assertProfileError(
            profile => {
                profile.reviewedRuntimeComponent.ruleIds.pop();
            },
            'MVP_RUNTIME_DRIFT'
        );
        assertProfileError(
            profile => {
                profile.claims.termination = 'claimed';
            },
            'UNAUTHORIZED_CLAIM'
        );
        assertProfileError(
            profile => {
                profile.surface.parser = 'implemented';
            },
            'PROFILE_DRIFT'
        );
    });
});
