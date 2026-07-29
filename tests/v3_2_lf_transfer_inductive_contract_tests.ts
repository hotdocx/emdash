/**
 * Focused generic generated-owner association tests for
 * SCALE-INDUCTIVE-1B1.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { describe, it } from 'node:test';
import {
    CoreLfGeneratedInductiveContractError,
    CoreLfGeneratedInductiveContractSpec,
    CoreLfModuleSpec,
    associateCoreLfGeneratedInductiveContract,
    binderMode,
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    createCoreLfModuleSpec
} from '../src/v3_2';
import * as browser from '../src/v3_2/browser';

const moduleId = 'fixture.generated_inductive';
const code = coreLfQualifiedSymbol(moduleId, 'Code');
const indexedBox = coreLfQualifiedSymbol(moduleId, 'IndexedBox');
const makeBox = coreLfQualifiedSymbol(moduleId, 'make_box');
const indIndexedBox =
    coreLfQualifiedSymbol(moduleId, 'ind_IndexedBox');

const provenance = (sourceFragment: string) => ({
    authorityPath: 'tests/fixtures/generated-inductive.lp',
    sourceFragment
});

const explicitMode = binderMode('explicit', 'functorial');

const sourceModule = (): CoreLfModuleSpec =>
    createCoreLfModuleSpec({
        revision: 'generated-inductive-source-1',
        moduleId,
        fragmentId: 'generated-inductive-source',
        authorityPath:
            'tests/fixtures/generated-inductive.lp',
        sourceSha256:
            'sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa' +
            'aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa',
        dependencies: [],
        externalSymbols: [{
            symbol: code,
            availability: 'existing-core'
        }],
        declarations: [],
        inductives: [{
            order: 0,
            symbol: indexedBox,
            parameters: [],
            indices: [{
                hint: 'i',
                mode: explicitMode,
                type: {
                    tag: 'global',
                    symbol: code
                }
            }],
            sort: { tag: 'type' },
            constructors: [{
                order: 0,
                symbol: makeBox,
                binders: [{
                    hint: 'i',
                    mode: explicitMode,
                    type: {
                        tag: 'global',
                        symbol: code
                    }
                }],
                result: {
                    tag: 'call',
                    callee: {
                        tag: 'global',
                        symbol: indexedBox
                    },
                    arguments: [{
                        plicity: 'explicit',
                        value: {
                            tag: 'bound',
                            index: 0
                        }
                    }]
                },
                provenance: provenance('| make_box (i : Code)')
            }],
            generatedSymbols: [indIndexedBox],
            modifiers: {
                visibility: 'public',
                rigidity: 'injective',
                sourceOpacity: 'opaque'
            },
            provenance: provenance(
                'inductive IndexedBox (i : Code) : TYPE'
            )
        }],
        runtimeRules: [],
        proofRules: []
    });

const contractModule = (): CoreLfModuleSpec =>
    createCoreLfModuleSpec({
        revision: 'generated-inductive-contract-1',
        moduleId,
        fragmentId: 'generated-inductive-contract',
        authorityPath:
            'tests/fixtures/generated-inductive.lp',
        sourceSha256:
            'sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb' +
            'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb',
        dependencies: [],
        externalSymbols: [
            {
                symbol: indexedBox,
                availability: 'earlier-fragment'
            },
            {
                symbol: makeBox,
                availability: 'earlier-fragment'
            }
        ],
        declarations: [{
            order: 0,
            symbol: indIndexedBox,
            type: { tag: 'type' },
            body: coreLfTransferAbsentBody(),
            modifiers: {
                visibility: 'public',
                rigidity: 'ordinary',
                sourceOpacity: 'opaque',
                generatedBy: indexedBox
            },
            provenance: provenance('generated print ind_IndexedBox')
        }],
        inductives: [],
        runtimeRules: [{
            order: 1,
            id: 'generated-inductive.beta',
            groupId: 'generated-inductive',
            clauseOrder: 0,
            sourceOwner: indIndexedBox,
            variables: [],
            left: {
                tag: 'global',
                symbol: indIndexedBox
            },
            right: {
                tag: 'global',
                symbol: indIndexedBox
            },
            provenance: provenance(
                'generated rule ind_IndexedBox ↪ ind_IndexedBox'
            )
        }],
        proofRules: []
    });

const contractSpec = (
    source: CoreLfModuleSpec = sourceModule(),
    contract: CoreLfModuleSpec = contractModule()
): CoreLfGeneratedInductiveContractSpec => ({
    revision: 'generated-inductive-association-1',
    sourceModuleRevision: source.revision,
    contractModuleRevision: contract.revision,
    block: indexedBox,
    generatedOwner: indIndexedBox,
    runtimeRuleIds: ['generated-inductive.beta'],
    classification: {
        kind: 'nonrecursive-indexed',
        expectedParameterCount: 0,
        expectedIndexCount: 1,
        expectedConstructorCount: 1
    }
});

const assertContractError = (
    action: () => unknown,
    code_: CoreLfGeneratedInductiveContractError['code']
): void => {
    assert.throws(
        action,
        error =>
            error instanceof
                CoreLfGeneratedInductiveContractError &&
            error.code === code_
    );
};

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value as object).forEach(key =>
        assertDeepFrozen(
            (value as Record<PropertyKey, unknown>)[key]
        )
    );
};

describe('SCALE-INDUCTIVE-1B1 generated-owner contracts', () => {
    it('associates one explicit nonrecursive indexed contract', () => {
        const source = sourceModule();
        const contract = contractModule();
        const association =
            associateCoreLfGeneratedInductiveContract(
                source,
                contract,
                contractSpec(source, contract)
            );
        assert.deepEqual(association.classification, {
            kind: 'nonrecursive-indexed',
            parameterCount: 0,
            indexCount: 1,
            constructorCount: 1,
            recursiveOccurrencePaths: [],
            strictPositivity: 'trivial-nonrecursive'
        });
        assert.deepEqual(
            association.runtimeRuleIds,
            ['generated-inductive.beta']
        );
        assertDeepFrozen(association);
    });

    it('requires one listed generated identity and linked declaration', () => {
        const source = sourceModule();
        const contract = contractModule();
        const foreignOwner =
            coreLfQualifiedSymbol(moduleId, 'ind_Foreign');
        assertContractError(
            () => associateCoreLfGeneratedInductiveContract(
                source,
                contract,
                {
                    ...contractSpec(source, contract),
                    generatedOwner: foreignOwner
                }
            ),
            'GENERATED_OWNER_NOT_UNIQUE'
        );

        const declaration = contract.declarations[0];
        const unlinked = createCoreLfModuleSpec({
            ...contract,
            revision: 'generated-inductive-unlinked-1',
            declarations: [{
                ...declaration,
                modifiers: {
                    ...declaration.modifiers,
                    generatedBy: undefined
                }
            }]
        });
        assertContractError(
            () => associateCoreLfGeneratedInductiveContract(
                source,
                unlinked,
                contractSpec(source, unlinked)
            ),
            'INVALID_GENERATED_DECLARATION'
        );

        const transparent = createCoreLfModuleSpec({
            ...contract,
            revision: 'generated-inductive-transparent-1',
            declarations: [{
                ...declaration,
                modifiers: {
                    ...declaration.modifiers,
                    sourceOpacity: 'transparent'
                }
            }]
        });
        assertContractError(
            () => associateCoreLfGeneratedInductiveContract(
                source,
                transparent,
                contractSpec(source, transparent)
            ),
            'INVALID_GENERATED_DECLARATION'
        );
    });

    it('requires an exact generated-owner beta set', () => {
        const source = sourceModule();
        const contract = contractModule();
        assertContractError(
            () => associateCoreLfGeneratedInductiveContract(
                source,
                contract,
                {
                    ...contractSpec(source, contract),
                    runtimeRuleIds: ['missing.beta']
                }
            ),
            'INVALID_GENERATED_RULE_OWNERSHIP'
        );
    });

    it('fails closed on classification drift and direct recursion', () => {
        const source = sourceModule();
        const contract = contractModule();
        assertContractError(
            () => associateCoreLfGeneratedInductiveContract(
                source,
                contract,
                {
                    ...contractSpec(source, contract),
                    classification: {
                        kind: 'nonrecursive-indexed',
                        expectedParameterCount: 0,
                        expectedIndexCount: 2,
                        expectedConstructorCount: 1
                    }
                }
            ),
            'GENERATED_CLASSIFICATION_DRIFT'
        );

        const block = source.inductives[0];
        const constructor = block.constructors[0];
        const recursive = createCoreLfModuleSpec({
            ...source,
            revision: 'generated-inductive-recursive-1',
            inductives: [{
                ...block,
                constructors: [{
                    ...constructor,
                    binders: [
                        ...constructor.binders,
                        {
                            hint: 'previous',
                            mode: explicitMode,
                            type: {
                                tag: 'call',
                                callee: {
                                    tag: 'global',
                                    symbol: indexedBox
                                },
                                arguments: [{
                                    plicity: 'explicit',
                                    value: {
                                        tag: 'bound',
                                        index: 0
                                    }
                                }]
                            }
                        }
                    ],
                    result: {
                        tag: 'call',
                        callee: {
                            tag: 'global',
                            symbol: indexedBox
                        },
                        arguments: [{
                            plicity: 'explicit',
                            value: {
                                tag: 'bound',
                                index: 1
                            }
                        }]
                    }
                }]
            }]
        });
        assertContractError(
            () => associateCoreLfGeneratedInductiveContract(
                recursive,
                contract,
                contractSpec(recursive, contract)
            ),
            'UNSUPPORTED_GENERATED_RECURSION'
        );
    });

    it('keeps the generic path owner-free and outside the browser', () => {
        const implementation = readFileSync(
            'src/v3_2/lf_transfer_inductive_contract.ts',
            'utf8'
        );
        assert.doesNotMatch(
            implementation,
            /τΣ_|Struct_sigma|ind_τΣ_|IndexedBox|ind_IndexedBox/u
        );
        assert.equal(
            'associateCoreLfGeneratedInductiveContract' in browser,
            false
        );
    });
});
