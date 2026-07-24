/**
 * Focused TSK-1A tests for the pre-H-03 Core manifest proposal.
 */

import assert from 'node:assert';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_MVP_MANIFEST_PROPOSAL,
    CoreManifestProposalInput,
    CoreManifestValidationCode,
    CoreManifestValidationError,
    LAMBDAPI_V32_RULE_EVIDENCE_BINDINGS,
    LambdapiRuleEvidenceCatalogInput,
    validateCoreManifestProposal,
    validateLambdapiRuleEvidenceBindings
} from '../src/v3_2';

const cloneProposal = (): CoreManifestProposalInput =>
    JSON.parse(JSON.stringify(CORE_MVP_MANIFEST_PROPOSAL));

const expectManifestError = (
    mutate: (proposal: any) => void,
    code: CoreManifestValidationCode
): CoreManifestValidationError => {
    const proposal = cloneProposal() as any;
    mutate(proposal);
    try {
        validateCoreManifestProposal(proposal);
    } catch (error: unknown) {
        assert.ok(error instanceof CoreManifestValidationError);
        assert.equal(error.code, code);
        return error;
    }
    assert.fail(`Expected CoreManifestValidationError ${code}`);
};

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') {
        return;
    }
    assert.equal(Object.isFrozen(value), true);
    Object.values(value).forEach(assertDeepFrozen);
};

describe('TypeScript v3.2 TSK-1A manifest proposal', () => {
    it('recommends an exact dependency-closed 16-owner MVP signature', () => {
        const candidates = CORE_MVP_MANIFEST_PROPOSAL.owners
            .filter(owner => owner.membership === 'mvp-candidate')
            .map(owner => owner.owner);
        const excluded = CORE_MVP_MANIFEST_PROPOSAL.owners
            .filter(owner => owner.membership === 'conformance-only')
            .map(owner => owner.owner);

        assert.deepEqual(candidates, [
            'groupoid-universe',
            'category-universe',
            'decode',
            'object-classifier',
            'functor-classifier',
            'hom-classifier',
            'transfor-classifier',
            'hom-category',
            'transfor-category',
            'functor-object',
            'functor-hom-full',
            'functor-hom-capped',
            'transfor-component-full',
            'transfor-component-capped',
            'transfor-hom-full',
            'transfor-hom-capped'
        ]);
        assert.deepEqual(excluded, [
            'category-of-categories',
            'opposite-category',
            'displayed-category-category',
            'internal-hom-source',
            'internal-hom-target',
            'displayed-pullback',
            'constant-displayed-family',
            'section-category'
        ]);
        assert.deepEqual(
            CORE_MVP_MANIFEST_PROPOSAL.recommendation.ownerIds,
            candidates
        );
        assert.equal(
            CORE_MVP_MANIFEST_PROPOSAL.status,
            'proposal-awaiting-h03'
        );
        assert.equal(
            CORE_MVP_MANIFEST_PROPOSAL.ruleSelection,
            'closed-world'
        );
        assert.doesNotThrow(() =>
            validateCoreManifestProposal(CORE_MVP_MANIFEST_PROPOSAL)
        );
    });

    it('keeps every exclusion explicit and risk-classified', () => {
        const exclusions = CORE_MVP_MANIFEST_PROPOSAL.owners.filter(
            owner => owner.membership === 'conformance-only'
        );
        assert.equal(exclusions.length, 8);
        for (const owner of exclusions) {
            assert.ok(owner.exclusion);
            assert.ok(owner.exclusion.reason.length > 20);
            assert.ok(owner.exclusion.openRisks.length > 0);
            assert.ok(owner.consumers.length > 0);
        }

        assert.deepEqual(
            CORE_MVP_MANIFEST_PROPOSAL.excludedRuleFamilies.map(
                family => family.id
            ),
            [
                'classifier.presentation-and-inversion',
                'ordinary.identity-and-composition',
                'internal-hom.variance-conversions',
                'displayed.reindexing-reductions',
                'displayed.section-bridges',
                'all-unlisted-active-rules'
            ]
        );
        assert.ok(
            CORE_MVP_MANIFEST_PROPOSAL.excludedRuleFamilies.every(
                family =>
                    family.reason.length > 20 &&
                    family.openRisks.length > 0
            )
        );
    });

    it('records exactly three runtime candidates and no proof-time candidate', () => {
        const candidates = CORE_MVP_MANIFEST_PROPOSAL.rules.filter(
            rule => rule.disposition === 'mvp-candidate'
        );
        assert.deepEqual(
            candidates.map(rule => [rule.id, rule.authority]),
            [
                [
                    'projection.functor-hom.evaluate',
                    'runtime-reduction'
                ],
                [
                    'projection.transfor-component.evaluate',
                    'runtime-reduction'
                ],
                [
                    'projection.transfor-hom.evaluate',
                    'runtime-reduction'
                ]
            ]
        );
        assert.deepEqual(
            CORE_MVP_MANIFEST_PROPOSAL.recommendation.runtimeRuleIds,
            candidates.map(rule => rule.id)
        );
        assert.deepEqual(
            CORE_MVP_MANIFEST_PROPOSAL.recommendation.proofTimeRuleIds,
            []
        );
    });

    it('represents full-to-capped projection beta without evaluating it', () => {
        const rule = CORE_MVP_MANIFEST_PROPOSAL.rules[0];
        assert.equal(rule.left.tag, 'owner-application');
        assert.equal(rule.right.tag, 'owner-application');
        if (
            rule.left.tag !== 'owner-application' ||
            rule.right.tag !== 'owner-application'
        ) {
            assert.fail('Expected owner-application patterns');
        }
        assert.equal(rule.left.owner, 'functor-object');
        assert.equal(rule.left.arguments[2].tag, 'owner-application');
        if (rule.left.arguments[2].tag !== 'owner-application') {
            assert.fail('Expected full functor-hom owner');
        }
        assert.equal(
            rule.left.arguments[2].owner,
            'functor-hom-full'
        );
        assert.equal(rule.right.owner, 'functor-hom-capped');
        assert.deepEqual(rule.variables, ['A', 'B', 'F', 'X', 'Y', 'f']);
    });

    it('separates proof-time comparison from intentional runtime non-conversion', () => {
        const proofTime = CORE_MVP_MANIFEST_PROPOSAL.rules[3];
        const nonConversion = CORE_MVP_MANIFEST_PROPOSAL.rules[4];

        assert.equal(proofTime.authority, 'proof-time-comparison');
        assert.equal(proofTime.disposition, 'conformance-evidence');
        assert.equal(proofTime.consequences?.length, 2);
        assert.equal(nonConversion.authority, 'intentional-non-conversion');
        assert.equal(nonConversion.disposition, 'conformance-evidence');
        assert.equal(nonConversion.consequences, undefined);
        assert.deepEqual(
            CORE_MVP_MANIFEST_PROPOSAL.recommendation
                .nonConversionEvidenceIds,
            ['nonconversion.constant-section.runtime']
        );

        assert.equal(proofTime.left.tag, 'owner-application');
        assert.equal(proofTime.right.tag, 'owner-application');
        if (
            proofTime.left.tag !== 'owner-application' ||
            proofTime.right.tag !== 'owner-application'
        ) {
            assert.fail('Expected category-level comparison patterns');
        }
        assert.equal(proofTime.left.owner, 'section-category');
        assert.equal(proofTime.right.owner, 'hom-category');
        assert.equal(
            proofTime.right.arguments[0].tag,
            'owner-application'
        );
        if (proofTime.right.arguments[0].tag !== 'owner-application') {
            assert.fail('Expected category universe category pattern');
        }
        assert.equal(
            proofTime.right.arguments[0].owner,
            'category-of-categories'
        );
    });

    it('keeps backend spellings and paths out of the Core proposal', () => {
        const serialized = JSON.stringify(CORE_MVP_MANIFEST_PROPOSAL);
        assert.doesNotMatch(
            serialized,
            /emdash3_2\.lp|fapp0|fapp1_func|tapp0_func|tapp1_func|Pi_cat/
        );
    });

    it('deep-freezes every manifest proposal record', () => {
        assertDeepFrozen(CORE_MVP_MANIFEST_PROPOSAL);
    });

    it('rejects unknown, duplicate, incomplete, and reordered owners', () => {
        assert.match(
            expectManifestError(
                proposal => {
                    proposal.owners[0].owner = 'missing-owner';
                },
                'UNKNOWN_OWNER'
            ).message,
            /missing-owner/
        );
        assert.match(
            expectManifestError(
                proposal => {
                    proposal.owners[1].owner = proposal.owners[0].owner;
                },
                'DUPLICATE_OWNER'
            ).message,
            /more than once/
        );
        assert.match(
            expectManifestError(
                proposal => {
                    proposal.owners.pop();
                },
                'INCOMPLETE_OWNER_COVERAGE'
            ).message,
            /missing/
        );
        assert.match(
            expectManifestError(
                proposal => {
                    proposal.owners[0].order = 1;
                },
                'OWNER_ORDER_MISMATCH'
            ).message,
            /expected order 0/
        );
    });

    it('rejects a candidate whose signature escapes the selected owners', () => {
        const error = expectManifestError(
            proposal => {
                const homCategory = proposal.owners.find(
                    (owner: any) => owner.owner === 'hom-category'
                );
                homCategory.membership = 'conformance-only';
                homCategory.exclusion = {
                    reason: 'test exclusion',
                    openRisks: ['rule-inventory']
                };
            },
            'CANDIDATE_SIGNATURE_DEPENDENCY'
        );
        assert.match(error.message, /hom-category/);
    });

    it('rejects duplicate, noncanonical, and nondeterministic rule identities', () => {
        assert.match(
            expectManifestError(
                proposal => {
                    proposal.rules[1].id = proposal.rules[0].id;
                },
                'DUPLICATE_RULE_ID'
            ).message,
            /more than once/
        );
        assert.match(
            expectManifestError(
                proposal => {
                    proposal.rules[0].id = 'Not Canonical';
                },
                'INVALID_RULE_ID'
            ).message,
            /not canonical/
        );
        assert.match(
            expectManifestError(
                proposal => {
                    proposal.rules[1].order = 8;
                },
                'RULE_ORDER_MISMATCH'
            ).message,
            /expected 1/
        );
    });

    it('rejects unknown owners, malformed arity, and unbound variables in rules', () => {
        assert.match(
            expectManifestError(
                proposal => {
                    proposal.rules[0].left.owner = 'missing-owner';
                },
                'UNKNOWN_RULE_OWNER'
            ).message,
            /missing-owner/
        );
        assert.match(
            expectManifestError(
                proposal => {
                    proposal.rules[0].left.arguments.pop();
                },
                'RULE_OWNER_ARITY_MISMATCH'
            ).message,
            /expected 4/
        );
        assert.match(
            expectManifestError(
                proposal => {
                    const right = proposal.rules[0].right;
                    right.arguments[right.arguments.length - 1] = {
                        tag: 'variable',
                        name: 'unbound'
                    };
                },
                'UNBOUND_RULE_VARIABLE'
            ).message,
            /unbound/
        );
    });

    it('rejects right-side scope escape and cross-class rule shapes', () => {
        assert.match(
            expectManifestError(
                proposal => {
                    proposal.rules[0].variables.push('fresh');
                    const right = proposal.rules[0].right;
                    right.arguments[right.arguments.length - 1] = {
                        tag: 'variable',
                        name: 'fresh'
                    };
                },
                'RUNTIME_SCOPE_ESCAPE'
            ).message,
            /absent from its left side/
        );
        assert.match(
            expectManifestError(
                proposal => {
                    proposal.rules[3].variables.push('Fresh');
                    proposal.rules[3].consequences.push({
                        left: {
                            tag: 'variable',
                            name: 'K'
                        },
                        right: {
                            tag: 'variable',
                            name: 'Fresh'
                        }
                    });
                },
                'COMPARISON_CONSEQUENCE_SCOPE_ESCAPE'
            ).message,
            /absent from both comparison sides/
        );
        assert.match(
            expectManifestError(
                proposal => {
                    proposal.rules[0].authority =
                        'proof-time-comparison';
                },
                'AUTHORITY_SHAPE_MISMATCH'
            ).message,
            /requires at least one/
        );
        assert.match(
            expectManifestError(
                proposal => {
                    proposal.rules[4].disposition = 'mvp-candidate';
                },
                'AUTHORITY_SHAPE_MISMATCH'
            ).message,
            /non-executable/
        );
    });

    it('rejects an executable rule that refers to an excluded owner', () => {
        const error = expectManifestError(
            proposal => {
                const full = proposal.owners.find(
                    (owner: any) => owner.owner === 'functor-hom-full'
                );
                full.membership = 'conformance-only';
                full.exclusion = {
                    reason: 'test exclusion',
                    openRisks: ['rule-inventory']
                };
            },
            'CANDIDATE_RULE_USES_EXCLUDED_OWNER'
        );
        assert.match(error.message, /functor-hom-full/);
    });

    it('rejects an H-03 recommendation that drifts from its proposal', () => {
        assert.match(
            expectManifestError(
                proposal => {
                    proposal.recommendation.runtimeRuleIds.pop();
                },
                'RECOMMENDATION_MISMATCH'
            ).message,
            /does not exactly match/
        );
    });

    it('binds every semantic evidence key to exact backend provenance', () => {
        assert.doesNotThrow(() =>
            validateLambdapiRuleEvidenceBindings()
        );
        assert.deepEqual(
            Object.keys(LAMBDAPI_V32_RULE_EVIDENCE_BINDINGS),
            CORE_MVP_MANIFEST_PROPOSAL.rules.map(
                rule => rule.provenance.evidence
            )
        );

        const runtime =
            LAMBDAPI_V32_RULE_EVIDENCE_BINDINGS[
                'projection.functor-hom.evaluate'
            ];
        assert.equal(runtime.authority, 'runtime-reduction');
        assert.equal(
            runtime.provenance.sources[0].authorityPath,
            'emdash2/emdash3_2.lp'
        );
        assert.match(
            runtime.provenance.sources[0].declaration,
            /^rule /
        );

        const proof =
            LAMBDAPI_V32_RULE_EVIDENCE_BINDINGS[
                'comparison.constant-section'
            ];
        assert.equal(proof.authority, 'proof-time-comparison');
        assert.equal(proof.provenance.sources.length, 2);
        assert.match(
            proof.provenance.sources[0].declaration,
            /^rule Hom_cat/
        );
        assert.match(
            proof.provenance.sources[1].declaration,
            /^unif_rule /
        );

        const negative =
            LAMBDAPI_V32_RULE_EVIDENCE_BINDINGS[
                'nonconversion.constant-section.runtime'
            ];
        assert.equal(
            negative.provenance.sources[1].authorityPath,
            'tests/v3_2_dependent_context_tests.ts'
        );
        assert.match(
            negative.provenance.sources[1].declaration,
            /assertnot/
        );
    });

    it('relocates every recorded source fragment in the active workspace', () => {
        const normalize = (source: string): string =>
            source.replace(/\s+/g, ' ').trim();
        const workspaceRoot = resolve(__dirname, '..');

        for (const binding of
            Object.values(LAMBDAPI_V32_RULE_EVIDENCE_BINDINGS)) {
            for (const source of binding.provenance.sources) {
                const text = readFileSync(
                    resolve(workspaceRoot, source.authorityPath),
                    'utf8'
                );
                assert.ok(
                    text.includes(source.section),
                    `Missing section '${source.section}' in ` +
                    source.authorityPath
                );
                assert.ok(
                    normalize(text).includes(normalize(source.declaration)),
                    `Missing declaration '${source.declaration}' in ` +
                    source.authorityPath
                );
            }
        }
    });

    it('rejects missing, unknown, and cross-class backend evidence', () => {
        const cloneBindings = (): any =>
            JSON.parse(JSON.stringify(
                LAMBDAPI_V32_RULE_EVIDENCE_BINDINGS
            ));

        const missing = cloneBindings();
        delete missing['projection.functor-hom.evaluate'];
        assert.throws(
            () => validateLambdapiRuleEvidenceBindings(missing),
            /missing key 'projection\.functor-hom\.evaluate'/
        );

        const unknown = cloneBindings();
        unknown['unknown.evidence'] =
            unknown['projection.functor-hom.evaluate'];
        assert.throws(
            () => validateLambdapiRuleEvidenceBindings(unknown),
            /unknown key 'unknown\.evidence'/
        );

        const crossClass = cloneBindings();
        crossClass['comparison.constant-section'].authority =
            'runtime-reduction';
        assert.throws(
            () => validateLambdapiRuleEvidenceBindings(
                crossClass as LambdapiRuleEvidenceCatalogInput
            ),
            /expected proof-time-comparison/
        );
    });
});
