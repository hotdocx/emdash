/**
 * Focused USABILITY-2A0 transfer evidence for the first closed-index
 * displayed applications.
 */

import assert from 'node:assert/strict';
import {
    createHash
} from 'node:crypto';
import {
    readFileSync
} from 'node:fs';
import {
    resolve
} from 'node:path';
import {
    describe,
    it
} from 'node:test';
import * as browser from '../src/v3_2/browser';
import {
    CORE_CATEGORICAL_DEPENDENT_PREREQUISITES,
    CORE_CATEGORICAL_DEPENDENT_SOURCE_SHA256,
    CORE_CATEGORICAL_DEPENDENT_SYMBOLS,
    CORE_CATEGORICAL_DEPENDENT_TRANSFER_BOUNDARY,
    CORE_CATEGORICAL_DEPENDENT_TRANSFER_LINKAGE,
    CORE_CATEGORICAL_DEPENDENT_TRANSFER_MODULE,
    CORE_CATEGORICAL_DEPENDENT_TRANSFER_POLICY,
    CORE_MVP_MANIFEST,
    CORE_OWNER_SCHEMAS,
    compileCoreCategoricalDependentTransfer,
    coreCategoricalDependentCoreName
} from '../src/v3_2';

const repositoryRoot = resolve(__dirname, '..');

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    if (value instanceof Map) return;
    Reflect.ownKeys(value).forEach(key =>
        assertDeepFrozen(
            (value as Record<PropertyKey, unknown>)[key]
        )
    );
};

describe(
    'TypeScript v3.2 USABILITY-2A0 dependent declaration transfer',
    () => {
        it('pins exactly the two active closed-index owners', () => {
            assert.deepEqual(
                CORE_CATEGORICAL_DEPENDENT_PREREQUISITES.map(
                    prerequisite => prerequisite.id
                ),
                [
                    'displayed-functor-fibre',
                    'displayed-functor-transport'
                ]
            );
            assert.deepEqual(
                CORE_CATEGORICAL_DEPENDENT_TRANSFER_MODULE.declarations.map(
                    declaration => declaration.symbol.name
                ),
                [
                    'Fibre_func',
                    'functord_transport_func'
                ]
            );
            assert.deepEqual(
                CORE_CATEGORICAL_DEPENDENT_TRANSFER_POLICY.entries.map(
                    entry => entry.policy
                ),
                [
                    'opaque-signature',
                    'opaque-signature'
                ]
            );
            assert.equal(
                CORE_CATEGORICAL_DEPENDENT_TRANSFER_LINKAGE.entries.length,
                11
            );
            assert.equal(
                CORE_CATEGORICAL_DEPENDENT_TRANSFER_BOUNDARY
                    .wholeDisplayedLaxityStatus,
                'deliberately-inactive-in-authority'
            );
            assertDeepFrozen(
                CORE_CATEGORICAL_DEPENDENT_PREREQUISITES
            );
            assertDeepFrozen(
                CORE_CATEGORICAL_DEPENDENT_TRANSFER_MODULE
            );
            assertDeepFrozen(
                CORE_CATEGORICAL_DEPENDENT_TRANSFER_POLICY
            );
            assertDeepFrozen(
                CORE_CATEGORICAL_DEPENDENT_TRANSFER_LINKAGE
            );
            assertDeepFrozen(
                CORE_CATEGORICAL_DEPENDENT_TRANSFER_BOUNDARY
            );
        });

        it('compiles both signatures through the generic LF engine', () => {
            const compilation =
                compileCoreCategoricalDependentTransfer();
            assert.equal(
                compilation.compiled.initialDeclarationCount,
                23
            );
            assert.equal(
                compilation.compiled.declarations.length,
                2
            );
            assert.equal(
                compilation.compiled.environment.declarations.length,
                25
            );
            assert.equal(
                compilation.compiled.declarations.every(
                    declaration =>
                        declaration.status === 'installed-opaque' &&
                        declaration.link.kind === 'free-declaration'
                ),
                true
            );
            compilation.compiled.createChecker().validateEnvironment();

            for (
                const prerequisite of
                CORE_CATEGORICAL_DEPENDENT_PREREQUISITES
            ) {
                const declaration = compilation.compiled.declaration(
                    prerequisite.symbol
                );
                assert.equal(
                    declaration?.link.kind,
                    'free-declaration'
                );
                if (
                    declaration !== undefined &&
                    declaration.link.kind === 'free-declaration'
                ) {
                    assert.equal(
                        declaration.link.coreName,
                        coreCategoricalDependentCoreName(
                            prerequisite.id
                        )
                    );
                    assert.equal(
                        declaration.link.backendName,
                        prerequisite.symbol.name
                    );
                }
            }
        });

        it('pins source bytes and exact active declaration anchors', () => {
            const authorityPath = resolve(
                repositoryRoot,
                CORE_CATEGORICAL_DEPENDENT_TRANSFER_MODULE.authorityPath
            );
            const source = readFileSync(authorityPath);
            const digest = createHash('sha256')
                .update(source)
                .digest('hex');
            assert.equal(
                `sha256:${digest}`,
                CORE_CATEGORICAL_DEPENDENT_SOURCE_SHA256
            );
            for (
                const declaration of
                CORE_CATEGORICAL_DEPENDENT_TRANSFER_MODULE.declarations
            ) {
                assert.equal(
                    source.includes(Buffer.from(
                        declaration.provenance.sourceFragment,
                        'utf8'
                    )),
                    true,
                    declaration.symbol.name
                );
            }
            assert.match(
                source.toString('utf8'),
                /Intended declaration, deliberately not active yet:[\s\S]*symbol functord_laxity_transf/u
            );
            assert.equal(
                CORE_CATEGORICAL_DEPENDENT_TRANSFER_MODULE.declarations.some(
                    declaration =>
                        declaration.symbol.name ===
                            'functord_laxity_transf'
                ),
                false
            );
        });

        it('does not expand intrinsic, runtime, proof, or browser scope', () => {
            assert.equal(
                Object.prototype.hasOwnProperty.call(
                    CORE_OWNER_SCHEMAS,
                    'displayed-functor-fibre'
                ),
                false
            );
            assert.equal(
                Object.prototype.hasOwnProperty.call(
                    CORE_OWNER_SCHEMAS,
                    'displayed-functor-transport'
                ),
                false
            );
            assert.equal(Object.keys(CORE_OWNER_SCHEMAS).length, 24);
            assert.equal(CORE_MVP_MANIFEST.owners.length, 16);
            assert.deepEqual(
                CORE_CATEGORICAL_DEPENDENT_TRANSFER_MODULE.runtimeRules,
                []
            );
            assert.deepEqual(
                CORE_CATEGORICAL_DEPENDENT_TRANSFER_MODULE.proofRules,
                []
            );
            assert.equal(
                'compileCoreCategoricalDependentTransfer' in browser,
                false
            );
            assert.deepEqual(
                CORE_CATEGORICAL_DEPENDENT_SYMBOLS,
                {
                    fibreFunctor: {
                        moduleId: 'emdash.emdash3_2',
                        name: 'Fibre_func'
                    },
                    displayedTransportFunctor: {
                        moduleId: 'emdash.emdash3_2',
                        name: 'functord_transport_func'
                    }
                }
            );
        });
    }
);
