/**
 * Focused USABILITY-1C generic signature-transfer evidence for the ordinary
 * categorical structural basis.
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
import {
    CORE_CATEGORICAL_STRUCTURAL_PREREQUISITES,
    CORE_CATEGORICAL_STRUCTURAL_SOURCE_SHA256,
    CORE_CATEGORICAL_STRUCTURAL_SYMBOLS,
    CORE_CATEGORICAL_STRUCTURAL_TRANSFER_BOUNDARY,
    CORE_CATEGORICAL_STRUCTURAL_TRANSFER_LINKAGE,
    CORE_CATEGORICAL_STRUCTURAL_TRANSFER_MODULE,
    CORE_CATEGORICAL_STRUCTURAL_TRANSFER_POLICY,
    CORE_CATEGORICAL_STRUCTURAL_RUNTIME_MODULE,
    CORE_CATEGORICAL_STRUCTURAL_RUNTIME_POLICY,
    CORE_MVP_MANIFEST,
    CORE_OWNER_SCHEMAS,
    KernelExpression,
    compileCoreCategoricalStructuralTransfer,
    coreCategoricalStructuralCoreName,
    coreCategoricalStructuralSymbolCoreName,
    kernelCall,
    kernelExpressionEquals,
    kernelFree,
    provenance
} from '../src/v3_2';
import * as browser from '../src/v3_2/browser';

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
    'TypeScript v3.2 USABILITY-1C structural declaration transfer',
    () => {
        it('pins thirteen prerequisites plus classifier support', () => {
            assert.deepEqual(
                CORE_CATEGORICAL_STRUCTURAL_PREREQUISITES.map(
                    entry => entry.id
                ),
                [
                    'identity-functor',
                    'constant-functor-abstraction',
                    'exchange-functor-abstraction',
                    'diagonal-functor-abstraction',
                    'product-category',
                    'product-left-projection',
                    'product-right-projection',
                    'product-pair',
                    'product-map',
                    'evaluation-functor',
                    'functor-composition',
                    'curry-package',
                    'uncurry-package'
                ]
            );
            assert.deepEqual(
                CORE_CATEGORICAL_STRUCTURAL_TRANSFER_MODULE.declarations.map(
                    declaration => declaration.symbol.name
                ),
                [
                    'Functor_cat',
                    'Functor',
                    'id_func',
                    'comp_cat_fapp0',
                    'Product_cat',
                    'Product_pair',
                    'Product_projL_func',
                    'Product_projR_func',
                    'Product_map_func',
                    'Eval_func',
                    'curry_func_func',
                    'uncurry_func_func',
                    'Const_func_func',
                    'sym_func_func',
                    'diag_func_func'
                ]
            );
            assert.equal(
                CORE_CATEGORICAL_STRUCTURAL_TRANSFER_POLICY.entries[1]
                    .policy,
                'checked-transparent-definition'
            );
            assert.equal(
                CORE_CATEGORICAL_STRUCTURAL_TRANSFER_POLICY.entries
                    .filter((_, index) => index !== 1)
                    .every(entry =>
                        entry.policy === 'opaque-signature'
                    ),
                true
            );
            assert.equal(
                CORE_CATEGORICAL_STRUCTURAL_TRANSFER_LINKAGE.entries.length,
                19
            );
            assert.equal(
                CORE_CATEGORICAL_STRUCTURAL_TRANSFER_BOUNDARY
                    .supportDeclarationCount,
                2
            );
            assertDeepFrozen(
                CORE_CATEGORICAL_STRUCTURAL_PREREQUISITES
            );
            assertDeepFrozen(
                CORE_CATEGORICAL_STRUCTURAL_TRANSFER_MODULE
            );
            assertDeepFrozen(
                CORE_CATEGORICAL_STRUCTURAL_TRANSFER_POLICY
            );
            assertDeepFrozen(
                CORE_CATEGORICAL_STRUCTURAL_TRANSFER_LINKAGE
            );
            assertDeepFrozen(
                CORE_CATEGORICAL_STRUCTURAL_TRANSFER_BOUNDARY
            );
        });

        it('compiles all signatures through the generic LF engine', () => {
            const compilation =
                compileCoreCategoricalStructuralTransfer();
            assert.equal(
                compilation.compiled.initialDeclarationCount,
                9
            );
            assert.equal(
                compilation.initialDeclarations.declarations.length,
                29
            );
            assert.equal(
                compilation.compiled.declarations.length,
                15
            );
            assert.equal(
                compilation.compiled.environment.declarations.length,
                23
            );
            assert.equal(
                compilation.compiled.declarations[1].status,
                'intrinsic-transparent'
            );
            assert.equal(
                compilation.compiled.declarations
                    .filter((_, index) => index !== 1)
                    .every(
                        declaration =>
                            declaration.status === 'installed-opaque' &&
                            declaration.link.kind === 'free-declaration'
                    ),
                true
            );
            compilation.compiled.createChecker().validateEnvironment();

            for (
                const prerequisite of
                CORE_CATEGORICAL_STRUCTURAL_PREREQUISITES
            ) {
                const coreName = coreCategoricalStructuralCoreName(
                    prerequisite.id
                );
                const declaration =
                    compilation.compiled.declaration(
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
                    assert.equal(declaration.link.coreName, coreName);
                    assert.equal(
                        declaration.link.backendName,
                        prerequisite.symbol.name
                    );
                }
            }
        });

        it('installs the exact generic product-functor normalization', () => {
            const compilation =
                compileCoreCategoricalStructuralTransfer();
            assert.deepEqual(
                CORE_CATEGORICAL_STRUCTURAL_RUNTIME_MODULE.runtimeRules
                    .map(rule => rule.id),
                ['categorical.product-functor.normalize']
            );
            assert.deepEqual(
                CORE_CATEGORICAL_STRUCTURAL_RUNTIME_POLICY.entries.map(
                    entry => entry.policy
                ),
                ['runtime-rewrite']
            );
            assert.deepEqual(
                compilation.runtime.ruleIds,
                ['categorical.product-functor.normalize']
            );
            assert.equal(
                compilation.composedRuntime.ruleIds.slice(-1)[0],
                'categorical.product-functor.normalize'
            );

            const source = provenance(
                'derived',
                'USABILITY-1C runtime witness'
            );
            const X = kernelFree('structural_X', source);
            const A = kernelFree('structural_A', source);
            const B = kernelFree('structural_B', source);
            const functorCategoryName =
                coreCategoricalStructuralSymbolCoreName(
                    CORE_CATEGORICAL_STRUCTURAL_SYMBOLS.functorCategory
                );
            const productCategoryName =
                coreCategoricalStructuralCoreName('product-category');
            const call = (
                name: string,
                arguments_: readonly KernelExpression[]
            ) => kernelCall(
                kernelFree(name, source),
                arguments_.map(value => ({
                    plicity: 'explicit' as const,
                    value
                })),
                source
            );
            const before = call(functorCategoryName, [
                X,
                call(productCategoryName, [A, B])
            ]);
            const expected = call(productCategoryName, [
                call(functorCategoryName, [X, A]),
                call(functorCategoryName, [X, B])
            ]);
            const rewrite =
                compilation.composedRuntime.rewriteHead(before);
            assert.equal(rewrite.status, 'rewritten');
            if (rewrite.status === 'rewritten') {
                assert.equal(
                    rewrite.ruleId,
                    'categorical.product-functor.normalize'
                );
                assert.equal(
                    kernelExpressionEquals(rewrite.after, expected),
                    true
                );
            }
            assertDeepFrozen(
                CORE_CATEGORICAL_STRUCTURAL_RUNTIME_MODULE
            );
            assertDeepFrozen(
                CORE_CATEGORICAL_STRUCTURAL_RUNTIME_POLICY
            );
        });

        it('pins source bytes and exact declaration anchors', () => {
            const authorityPath = resolve(
                repositoryRoot,
                CORE_CATEGORICAL_STRUCTURAL_TRANSFER_MODULE.authorityPath
            );
            const source = readFileSync(authorityPath);
            const digest = createHash('sha256')
                .update(source)
                .digest('hex');
            assert.equal(
                `sha256:${digest}`,
                CORE_CATEGORICAL_STRUCTURAL_SOURCE_SHA256
            );
            for (
                const declaration of
                CORE_CATEGORICAL_STRUCTURAL_TRANSFER_MODULE.declarations
            ) {
                assert.equal(
                    source.includes(
                        Buffer.from(
                            declaration.provenance.sourceFragment,
                            'utf8'
                        )
                    ),
                    true,
                    declaration.symbol.name
                );
            }
        });

        it('does not expand the intrinsic or browser profile', () => {
            assert.equal(
                Object.prototype.hasOwnProperty.call(
                    CORE_OWNER_SCHEMAS,
                    'identity-functor'
                ),
                false
            );
            assert.equal(
                CORE_MVP_MANIFEST.owners.length,
                16
            );
            assert.equal(
                Object.keys(CORE_OWNER_SCHEMAS).length,
                24
            );
            assert.equal(
                Object.prototype.hasOwnProperty.call(
                    browser,
                    'compileCoreCategoricalStructuralTransfer'
                ),
                false
            );
            assert.equal(
                Object.prototype.hasOwnProperty.call(
                    browser,
                    'CORE_CATEGORICAL_STRUCTURAL_SYMBOLS'
                ),
                false
            );
            assert.equal(
                CORE_CATEGORICAL_STRUCTURAL_SYMBOLS
                    .functorCategory.name,
                'Functor_cat'
            );
            assert.deepEqual(
                CORE_CATEGORICAL_STRUCTURAL_TRANSFER_MODULE.runtimeRules,
                []
            );
            assert.equal(
                CORE_CATEGORICAL_STRUCTURAL_RUNTIME_MODULE.runtimeRules
                    .length,
                1
            );
            assert.deepEqual(
                CORE_CATEGORICAL_STRUCTURAL_TRANSFER_MODULE.proofRules,
                []
            );
        });
    }
);
