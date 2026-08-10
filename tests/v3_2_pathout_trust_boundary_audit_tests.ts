/**
 * Focused PATHOUT-TRUST-BOUNDARY-0A authority and dependency tests.
 */

import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT,
    validateCorePathoutTrustBoundary0aAudit
} from '../src/v3_2/pathout_trust_boundary_audit';

const repositoryRoot = resolve(__dirname, '..');

const read = (path: string): string =>
    readFileSync(resolve(repositoryRoot, path), 'utf8');

const sha256 = (value: string): string =>
    'sha256:' + createHash('sha256').update(value).digest('hex');

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value as object).forEach(key =>
        assertDeepFrozen(
            (value as Record<PropertyKey, unknown>)[key]
        )
    );
};

const escapeRegularExpression = (value: string): string =>
    value.replace(/[.*+?^${}()|[\]\\]/gu, '\\$&');

const declarationBlock = (
    lines: readonly string[],
    firstLine: number
): string => {
    const block: string[] = [];
    for (let index = firstLine - 1; index < lines.length; index += 1) {
        block.push(lines[index]);
        if (/;\s*$/u.test(lines[index])) break;
    }
    return block.join('\n');
};

describe('PATHOUT-TRUST-BOUNDARY-0A read-only audit', () => {
    it('pins both active authority inputs by byte digest', () => {
        const { authority } = CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT;
        assert.equal(sha256(read(authority.source.path)), authority.source.sha256);
        assert.equal(sha256(read(authority.checks.path)), authority.checks.sha256);
    });

    it('matches all selected owner positions, kinds, and body status', () => {
        const source = read(
            CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.authority.source.path
        );
        const lines = source.split(/\r?\n/u);

        for (
            const entry of
                CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.selectedOwners
        ) {
            const prefix = entry.sourceKind === 'constant-symbol'
                ? 'constant symbol'
                : entry.sourceKind === 'injective-symbol'
                    ? 'injective symbol'
                    : 'symbol';
            assert.match(
                lines[entry.line - 1],
                new RegExp(
                    `^${prefix} ${escapeRegularExpression(entry.name)}\\b`,
                    'u'
                )
            );
            assert.equal(
                declarationBlock(lines, entry.line).includes('≔'),
                entry.hasBody,
                entry.name
            );
        }
    });

    it('pins selected and explicitly deferred rule positions', () => {
        const lines = read(
            CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.authority.source.path
        ).split(/\r?\n/u);

        for (
            const entry of
                CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.observedRules
        ) {
            const sourceLine = lines[entry.line - 1].trim();
            if (entry.sourceKind === 'runtime-rule') {
                assert.match(sourceLine, /^rule\s/u, entry.id);
            } else {
                assert.equal(sourceLine, 'unif_rule', entry.id);
            }
        }
    });

    it('records the four real prerequisite closures and their status', () => {
        const closures =
            CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.prerequisiteClosures;
        assert.deepEqual(
            closures.map(entry => [entry.id, entry.status]),
            [
                [
                    'represented-source-action',
                    'missing-selected-profile-transfer'
                ],
                [
                    'sigma-totalization-functor-action',
                    'missing-selected-profile-transfer'
                ],
                [
                    'covariant-fibre-transport',
                    'missing-selected-profile-transfer'
                ],
                [
                    'sigma-total-transfd-uncurrying',
                    'isolated-qualification-not-selected-profile-transfer'
                ]
            ]
        );
        assert.deepEqual(
            closures.map(entry => entry.opaqueOwners.map(owner => owner.name)),
            [
                ['hom_int_precomp_tele_func', 'hom_int_precomp_func'],
                ['Sigma_func'],
                ['fib_cov_int', 'fib_cov_src_func', 'fib_cov_transf'],
                ['Sigma_transfd_funcd']
            ]
        );
        assert.deepEqual(
            closures.map(entry => [
                entry.runtimeRules.length,
                entry.proofRules.length
            ]),
            [[3, 1], [2, 0], [3, 0], [1, 0]]
        );
    });

    it('matches prerequisite owner and rule positions in the authority',
        () => {
            const lines = read(
                CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.authority.source.path
            ).split(/\r?\n/u);
            for (
                const closure of
                    CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT
                        .prerequisiteClosures
            ) {
                const prerequisiteOwners = [
                    ...closure.transparentDefinitions.map(entry => ({
                        entry,
                        hasBody: true
                    })),
                    ...closure.opaqueOwners.map(entry => ({
                        entry,
                        hasBody: false
                    }))
                ];
                for (const { entry, hasBody } of prerequisiteOwners) {
                    const prefix = entry.sourceKind === 'constant-symbol'
                        ? 'constant symbol'
                        : entry.sourceKind === 'injective-symbol'
                            ? 'injective symbol'
                            : 'symbol';
                    assert.match(
                        lines[entry.line - 1],
                        new RegExp(
                            `^${prefix} ` +
                                `${escapeRegularExpression(entry.name)}\\b`,
                            'u'
                        ),
                        entry.name
                    );
                    assert.equal(
                        declarationBlock(lines, entry.line).includes('≔'),
                        hasBody,
                        entry.name
                    );
                }
                for (const entry of closure.runtimeRules) {
                    assert.match(
                        lines[entry.line - 1],
                        /^rule\s/u,
                        entry.id
                    );
                }
                for (const entry of closure.proofRules) {
                    assert.equal(
                        lines[entry.line - 1].trim(),
                        'unif_rule',
                        entry.id
                    );
                }
            }
        });

    it('checks current transfer-anchor evidence without importing profiles',
        () => {
            for (
                const anchor of
                    CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT
                        .currentTransferAnchors
            ) {
                assert.match(
                    read(`src/v3_2/${anchor.provider}`),
                    new RegExp(escapeRegularExpression(anchor.name), 'u'),
                    anchor.name
                );
            }
        });

    it('is deeply frozen, non-self-authorizing, and internally valid', () => {
        validateCorePathoutTrustBoundary0aAudit();
        assertDeepFrozen(CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT);
        assert.equal(
            CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT
                .selectedOwners.filter(entry =>
                    entry.disposition === 'trusted-profile'
                ).length,
            5
        );
        assert.deepEqual(
            CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.productEffects,
            []
        );
    });

    it('does not enter npm public barrels or the browser surface', () => {
        for (
            const path of [
                'src/v3_2/package_core.ts',
                'src/v3_2/package_authoring.ts',
                'src/v3_2/package_workspace.ts',
                'src/v3_2/index.ts',
                'src/v3_2/browser.ts'
            ]
        ) {
            const source = read(path);
            assert.doesNotMatch(
                source,
                /pathout_trust_boundary_audit|CORE_PATHOUT_TRUST_BOUNDARY/u,
                path
            );
        }
    });
});
