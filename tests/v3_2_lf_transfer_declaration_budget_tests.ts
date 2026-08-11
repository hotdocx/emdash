/**
 * Focused semantic regressions for declaration-checker budget propagation.
 */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT,
    CoreLfDeclarationCompilerError,
    compileCoreLfDeclarations,
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    coreLfTransferExplicitBody,
    createCoreLfModuleSpec,
    createCoreLfTransferDeclarationCheckerFactory,
    createCoreLfTransferDeclarationLinkage,
    createCoreLfTransferPolicyOverlay
} from '../src/v3_2';
import {
    validateCoreLfTransferDeclarationBudgetReview
} from '../src/v3_2/lf_transfer_declaration_budget_review';

const moduleId = 'fixture.declaration_budget';
const carrier = coreLfQualifiedSymbol(moduleId, 'Carrier');
const alias = coreLfQualifiedSymbol(moduleId, 'Alias');
const witness = coreLfQualifiedSymbol(moduleId, 'witness');
const cast = coreLfQualifiedSymbol(moduleId, 'cast');

const source = (sourceFragment: string) => ({
    authorityPath: 'tests/fixtures/declaration_budget.lp',
    sourceFragment
});

const declarationBudgetFixture = () => {
    const module = createCoreLfModuleSpec({
        revision: 'declaration-budget-fixture-1',
        moduleId,
        fragmentId: 'one-delta-transparent-body',
        authorityPath: 'tests/fixtures/declaration_budget.lp',
        sourceSha256:
            'sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb',
        dependencies: [],
        externalSymbols: [],
        declarations: [
            {
                order: 0,
                symbol: carrier,
                type: { tag: 'type' as const },
                body: coreLfTransferAbsentBody(),
                modifiers: {
                    visibility: 'public' as const,
                    rigidity: 'ordinary' as const,
                    sourceOpacity: 'opaque' as const
                },
                provenance: source('symbol Carrier : TYPE;')
            },
            {
                order: 1,
                symbol: alias,
                type: { tag: 'type' as const },
                body: coreLfTransferExplicitBody({
                    tag: 'global' as const,
                    symbol: carrier
                }),
                modifiers: {
                    visibility: 'public' as const,
                    rigidity: 'ordinary' as const,
                    sourceOpacity: 'transparent' as const
                },
                provenance: source('symbol Alias : TYPE ≔ Carrier;')
            },
            {
                order: 2,
                symbol: witness,
                type: { tag: 'global' as const, symbol: carrier },
                body: coreLfTransferAbsentBody(),
                modifiers: {
                    visibility: 'public' as const,
                    rigidity: 'ordinary' as const,
                    sourceOpacity: 'opaque' as const
                },
                provenance: source('symbol witness : Carrier;')
            },
            {
                order: 3,
                symbol: cast,
                type: { tag: 'global' as const, symbol: alias },
                body: coreLfTransferExplicitBody({
                    tag: 'global' as const,
                    symbol: witness
                }),
                modifiers: {
                    visibility: 'public' as const,
                    rigidity: 'ordinary' as const,
                    sourceOpacity: 'transparent' as const
                },
                provenance: source('symbol cast : Alias ≔ witness;')
            }
        ],
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    const policies = [
        'opaque-signature',
        'checked-transparent-definition',
        'opaque-signature',
        'checked-transparent-definition'
    ] as const;
    const policy = createCoreLfTransferPolicyOverlay(module, {
        revision: 'declaration-budget-policy-1',
        moduleRevision: module.revision,
        entries: module.declarations.map((declaration, order) => ({
            order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy: policies[order],
            evidence: 'focused declaration-budget fixture'
        }))
    });
    const linkage = createCoreLfTransferDeclarationLinkage(module, {
        revision: 'declaration-budget-linkage-1',
        moduleRevision: module.revision,
        entries: module.declarations.map((declaration, order) => ({
            order,
            symbol: declaration.symbol,
            kind: 'free-declaration' as const,
            coreName: `declaration_budget_${declaration.symbol.name}`,
            backendName: declaration.symbol.name
        }))
    });
    return { module, policy, linkage };
};

describe('Core LF transfer declaration budget propagation', () => {
    it('requires its separately reviewed correction', () => {
        const review = validateCoreLfTransferDeclarationBudgetReview();
        assert.equal(review.authorization.implementationAuthorized, true);
    });

    it('rejects a one-delta body under an explicit zero-step limit', () => {
        const fixture = declarationBudgetFixture();
        assert.throws(
            () => compileCoreLfDeclarations(
                fixture.module,
                fixture.policy,
                fixture.linkage,
                { comparisonStepLimit: 0 }
            ),
            error =>
                error instanceof CoreLfDeclarationCompilerError &&
                error.code === 'DECLARATION_CHECK_FAILED' &&
                /exceeded 0 steps/u.test(error.message)
        );
    });

    it('accepts the same one-delta body under limit one', () => {
        const fixture = declarationBudgetFixture();
        const compiled = compileCoreLfDeclarations(
            fixture.module,
            fixture.policy,
            fixture.linkage,
            { comparisonStepLimit: 1 }
        );
        assert.equal(compiled.comparisonStepLimit, 1);
        assert.equal(compiled.declaration(cast)?.status,
            'installed-transparent');
    });

    it('preserves the default and public one-argument factory contract',
        () => {
            const fixture = declarationBudgetFixture();
            const compiled = compileCoreLfDeclarations(
                fixture.module,
                fixture.policy,
                fixture.linkage
            );
            assert.equal(
                compiled.comparisonStepLimit,
                CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT
            );
            assert.equal(CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT, 256);
            assert.equal(
                createCoreLfTransferDeclarationCheckerFactory.length,
                1
            );
        });

    it('continues to reject an invalid selected limit', () => {
        const fixture = declarationBudgetFixture();
        assert.throws(
            () => compileCoreLfDeclarations(
                fixture.module,
                fixture.policy,
                fixture.linkage,
                { comparisonStepLimit: -1 }
            ),
            error =>
                error instanceof CoreLfDeclarationCompilerError &&
                error.code === 'DECLARATION_CHECK_FAILED' &&
                error.path === 'options.comparisonStepLimit'
        );
    });
});
