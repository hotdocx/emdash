/**
 * Focused SCALE-STRESS-1A typed representation and gap-classification tests.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_LF_SCALE_STRESS_1_ACQUISITION_CONTRACTS,
    CORE_LF_SCALE_STRESS_1_REPRESENTATION,
    CoreLfDeclarationCompilerError,
    CoreLfDeclarationEnvironment,
    CoreLfRuntimeCompilerError,
    CoreLfScaleStress1Representation,
    CoreLfScaleStress1RepresentationError,
    CoreLfTransferExpression,
    compileCoreLfDeclarations,
    compileCoreLfRuntimeProgram,
    validateCoreLfScaleStress1Representation
} from '../src/v3_2';
import * as browser from '../src/v3_2/browser';

const repositoryRoot = resolve(__dirname, '..');
const representation = CORE_LF_SCALE_STRESS_1_REPRESENTATION;

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(
        assertDeepFrozen
    );
};

const cloneRepresentation = (
): CoreLfScaleStress1Representation =>
    JSON.parse(JSON.stringify(representation)) as
        CoreLfScaleStress1Representation;

const expressionContains = (
    expression: CoreLfTransferExpression,
    predicate: (candidate: CoreLfTransferExpression) => boolean
): boolean => {
    if (predicate(expression)) return true;
    switch (expression.tag) {
        case 'call':
            return (
                expressionContains(expression.callee, predicate) ||
                expression.arguments.some(argument =>
                    expressionContains(argument.value, predicate)
                )
            );
        case 'pi':
        case 'lambda':
            return (
                expressionContains(expression.binder.type, predicate) ||
                expressionContains(expression.body, predicate)
            );
        case 'type':
        case 'bound':
        case 'global':
        case 'capture':
        case 'wildcard':
            return false;
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

const isCapture = (
    expression: CoreLfTransferExpression,
    name: string
): boolean =>
    expression.tag === 'capture' && expression.name === name;

const sourceItems = (
    side: 'core' | 'nat'
) => {
    const module = representation[side].module;
    return [
        ...module.declarations,
        ...module.inductives,
        ...module.runtimeRules,
        ...module.proofRules
    ].sort((left, right) => left.order - right.order);
};

describe('TypeScript v3.2 SCALE-STRESS-1A representation', () => {
    it('freezes the exact representation-only boundary', () => {
        assert.equal(
            representation.revision,
            'SCALE-STRESS-1A-REPRESENTATION-1'
        );
        assert.equal(representation.semanticStatus, 'representation-only');
        assert.deepEqual(representation.productEffects, []);
        assert.equal(representation.assessments.length, 4);
        assert.ok(
            representation.doesNotAuthorize.includes(
                'active-runtime-execution'
            )
        );
        assert.ok(
            representation.doesNotAuthorize.includes(
                'mechanical-transfer-qualification'
            )
        );
        [
            ...representation.core.policy.entries,
            ...representation.nat.policy.entries
        ].forEach(entry =>
            assert.equal(entry.policy, 'conformance-only')
        );
        assertDeepFrozen(representation);
        assert.doesNotThrow(() =>
            validateCoreLfScaleStress1Representation()
        );
    });

    it('preserves acquired command order and relocatable source evidence', () => {
        assert.deepEqual(
            sourceItems('core').map(item => item.order),
            [0, 1, 2, 3, 4, 5, 6]
        );
        assert.deepEqual(
            sourceItems('core').map(
                item => item.provenance.canonicalCommandOrdinal
            ),
            [13, 14, 54, 63, 64, 74, 75]
        );
        assert.deepEqual(
            sourceItems('nat').map(item => item.order),
            [0, 1, 2, 3]
        );
        assert.deepEqual(
            sourceItems('nat').map(
                item => item.provenance.canonicalCommandOrdinal
            ),
            [3, 4, 4, 4]
        );

        (['core', 'nat'] as const).forEach(side => {
            const module = representation[side].module;
            const authority = readFileSync(
                resolve(repositoryRoot, module.authorityPath),
                'utf8'
            );
            sourceItems(side).forEach(item =>
                assert.equal(
                    authority.includes(item.provenance.sourceFragment),
                    true,
                    item.provenance.sourceFragment
                )
            );
            module.inductives.forEach(block =>
                block.constructors.forEach(constructor =>
                    assert.equal(
                        authority.includes(
                            constructor.provenance.sourceFragment
                        ),
                        true,
                        constructor.provenance.sourceFragment
                    )
                )
            );
        });

        const acquiredIds =
            CORE_LF_SCALE_STRESS_1_ACQUISITION_CONTRACTS.flatMap(
                contract => contract.commands.map(command => command.id)
            ).sort();
        const assessedIds = representation.assessments.flatMap(
            assessment => assessment.commandIds
        ).sort();
        assert.deepEqual(assessedIds, acquiredIds);
    });

    it('lowers J motive wildcard without losing dependent guards', () => {
        const rule = representation.core.module.runtimeRules.find(
            candidate =>
                candidate.id === 'stress.outer-j.reflexivity'
        );
        assert.notEqual(rule, undefined);
        if (rule === undefined) return;

        assert.deepEqual(
            rule.variables.map(variable => variable.name),
            ['a', 'y', 'P', 'u']
        );
        const motiveType = rule.variables[2].type;
        assert.equal(
            expressionContains(
                motiveType,
                candidate => isCapture(candidate, 'a')
            ),
            true
        );
        assert.equal(
            expressionContains(
                motiveType,
                candidate => isCapture(candidate, 'y')
            ),
            true
        );
        assert.equal(rule.left.tag, 'call');
        if (rule.left.tag !== 'call') return;
        assert.equal(rule.left.arguments.length, 6);
        assert.equal(
            isCapture(rule.left.arguments[2].value, 'P'),
            true
        );
        assert.deepEqual(
            rule.left.arguments[1].value,
            rule.left.arguments[4].value
        );
        assert.equal(
            expressionContains(
                rule.left.arguments[5].value,
                candidate =>
                    candidate.tag === 'global' &&
                    candidate.symbol.name === 'eq_refl'
            ),
            true
        );
        assert.equal(
            expressionContains(
                rule.left,
                candidate => candidate.tag === 'wildcard'
            ),
            false
        );
        assert.equal(isCapture(rule.right, 'u'), true);

        const assessment = representation.assessments.find(
            candidate => candidate.mechanism === 'outer-dependent-j'
        );
        assert.match(
            assessment?.typedRepresentation ?? '',
            /typed RHS-unused motive capture/u
        );
        assert.match(
            assessment?.nextRequirement ?? '',
            /mixed-phase planner.*foreign-category.*wrong-endpoint/u
        );
    });

    it('represents the binder-producing decoded groupoidal Pi rule', () => {
        const declaration = representation.core.module.declarations.find(
            candidate => candidate.symbol.name === 'Pi_grpd'
        );
        const rule = representation.core.module.runtimeRules.find(
            candidate => candidate.id === 'stress.pi-grpd.decode'
        );
        assert.equal(declaration?.modifiers.rigidity, 'constant');
        assert.notEqual(rule, undefined);
        if (rule === undefined) return;

        assert.equal(rule.right.tag, 'pi');
        if (rule.right.tag !== 'pi') return;
        assert.equal(
            expressionContains(
                rule.right.binder.type,
                candidate => isCapture(candidate, 'A')
            ),
            true
        );
        assert.equal(
            expressionContains(
                rule.right.body,
                candidate => isCapture(candidate, 'B')
            ),
            true
        );
        assert.equal(
            expressionContains(
                rule.right.body,
                candidate =>
                    candidate.tag === 'bound' &&
                    candidate.index === 0
            ),
            true
        );

        const assessment = representation.assessments.find(
            candidate => candidate.mechanism === 'decoded-groupoidal-pi'
        );
        assert.match(
            assessment?.nextRequirement ?? '',
            /mixed-phase planner.*binder RHS subject-reduction/u
        );
    });

    it('represents dependent Sigma ownership and records its compiler gap', () => {
        const block = representation.core.module.inductives[0];
        assert.equal(block.symbol.name, 'τΣ_');
        assert.deepEqual(
            block.parameters.map(parameter => [
                parameter.hint,
                parameter.mode.plicity
            ]),
            [
                ['a', 'implicit'],
                ['P', 'explicit']
            ]
        );
        assert.deepEqual(
            block.generatedSymbols.map(symbol => symbol.name),
            ['ind_τΣ_']
        );
        assert.equal(block.constructors.length, 1);
        const constructor = block.constructors[0];
        assert.equal(constructor.symbol.name, 'Struct_sigma');
        assert.deepEqual(
            constructor.binders.map(binder => binder.hint),
            ['sigma_Fst', 'sigma_Snd']
        );
        assert.equal(
            expressionContains(
                constructor.binders[1].type,
                candidate =>
                    candidate.tag === 'bound' &&
                    candidate.index === 1
            ),
            true
        );
        assert.equal(constructor.result.tag, 'call');

        const beta = representation.core.module.runtimeRules.find(
            candidate =>
                candidate.id === 'stress.sigma.eliminator-beta'
        );
        assert.notEqual(beta, undefined);
        if (beta === undefined || beta.left.tag !== 'call') return;
        assert.equal(
            isCapture(beta.left.arguments[2].value, 'Q'),
            true
        );
        assert.equal(
            expressionContains(
                beta.left,
                candidate => candidate.tag === 'wildcard'
            ),
            false
        );

        const assessment = representation.assessments.find(
            candidate =>
                candidate.mechanism === 'decoded-dependent-sigma'
        );
        assert.match(
            assessment?.currentBoundary ?? '',
            /no generic inductive compiler or mixed-phase planner/u
        );
        assert.match(
            assessment?.nextRequirement ?? '',
            /generic immutable inductive/u
        );
    });

    it('represents imported grouped Nat recursion without promotion', () => {
        const module = representation.nat.module;
        assert.deepEqual(module.dependencies, ['emdash.emdash3_2']);
        assert.ok(
            module.externalSymbols.every(
                external =>
                    external.availability === 'dependency-module'
            )
        );
        assert.equal(module.declarations[0].symbol.name, 'nat_add');
        assert.equal(module.declarations[0].modifiers.rigidity, 'injective');
        assert.deepEqual(
            module.runtimeRules.map(rule => [
                rule.order,
                rule.id,
                rule.groupId,
                rule.clauseOrder
            ]),
            [
                [1, 'stress.nat-add.zero-left', 'stress.nat-add', 0],
                [2, 'stress.nat-add.succ-left', 'stress.nat-add', 1],
                [3, 'stress.nat-add.zero-right', 'stress.nat-add', 2]
            ]
        );
        assert.equal(
            expressionContains(
                module.runtimeRules[1].right,
                candidate =>
                    candidate.tag === 'global' &&
                    candidate.symbol.name === 'nat_add'
            ),
            true
        );
        assert.ok(
            representation.nat.policy.entries.every(
                entry => entry.policy === 'conformance-only'
            )
        );
        const assessment = representation.assessments.find(
            candidate =>
                candidate.mechanism ===
                    'imported-grouped-nat-recursion'
        );
        assert.match(
            assessment?.currentBoundary ?? '',
            /mixed phase\/dependency planning/u
        );
    });

    it('fails closed on boundary or exact representation drift', () => {
        const promoted = cloneRepresentation();
        (
            promoted.core.policy.entries[0] as {
                policy: string;
            }
        ).policy = 'opaque-signature';
        assert.throws(
            () => validateCoreLfScaleStress1Representation(promoted),
            error =>
                error instanceof CoreLfScaleStress1RepresentationError &&
                error.code === 'INVALID_REPRESENTATION_BOUNDARY'
        );

        const drifted = cloneRepresentation();
        (
            drifted.assessments[0] as {
                currentBoundary: string;
            }
        ).currentBoundary = 'silently changed';
        assert.throws(
            () => validateCoreLfScaleStress1Representation(drifted),
            error =>
                error instanceof CoreLfScaleStress1RepresentationError &&
                error.code === 'REPRESENTATION_DRIFT'
        );
    });

    it('keeps mixed specs non-executable and generic engines owner-free', () => {
        const core = representation.core;
        assert.throws(
            () => compileCoreLfDeclarations(
                core.module,
                core.policy,
                {
                    revision: 'stress-refusal-linkage-1',
                    moduleRevision: core.module.revision,
                    moduleId: core.module.moduleId,
                    fragmentId: core.module.fragmentId,
                    entries: []
                }
            ),
            error =>
                error instanceof CoreLfDeclarationCompilerError &&
                error.code === 'UNSUPPORTED_MODULE_CONTENT'
        );
        assert.throws(
            () => compileCoreLfRuntimeProgram(
                core.module,
                core.policy,
                {
                    environment: CoreLfDeclarationEnvironment.empty(),
                    declaration: () => undefined
                }
            ),
            error =>
                error instanceof CoreLfRuntimeCompilerError &&
                error.code === 'UNSUPPORTED_MODULE_CONTENT'
        );

        [
            'src/v3_2/lf_transfer.ts',
            'src/v3_2/lf_transfer_compiler.ts',
            'src/v3_2/lf_transfer_runtime.ts',
            'src/v3_2/lf_transfer_proof.ts',
            'src/v3_2/lf_transfer_acquisition.ts'
        ].forEach(path => {
            const source = readFileSync(
                resolve(repositoryRoot, path),
                'utf8'
            );
            assert.doesNotMatch(
                source,
                /ind_eqr|Pi_grpd|τΣ_|nat_add/u
            );
        });
        assert.equal(
            'CORE_LF_SCALE_STRESS_1_REPRESENTATION' in browser,
            false
        );
    });
});
