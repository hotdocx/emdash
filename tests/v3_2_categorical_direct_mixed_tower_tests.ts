/**
 * D-DTTLF-USABILITY-054 direct arbitrary-finite tower source action.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CoreCategoricalDisplayedFamily,
    CORE_CATEGORICAL_DIRECT_MIXED_INTRODUCTION_PROGRAM_REVISION,
    CoreCategoricalFrontendError,
    CoreCategoricalProgram,
    CoreCategoricalProgramError,
    CoreCategoricalSlotToken,
    CoreCategoricalTerm,
    coreCategoricalMixedActionCoreName
} from '../src/v3_2';

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value).forEach(key =>
        assertDeepFrozen(
            (value as Record<PropertyKey, unknown>)[key]
        )
    );
};

const countOccurrences = (text: string, needle: string): number =>
    text.split(needle).length - 1;

const applySpine = (
    emdash: CoreCategoricalProgram,
    subject: CoreCategoricalTerm,
    innerTokens: readonly CoreCategoricalTerm[]
): CoreCategoricalTerm => innerTokens.reduce(
    (current, token) => emdash.apply(current, token),
    subject
);

const towerFamily = (
    emdash: CoreCategoricalProgram,
    innerFamilies: readonly CoreCategoricalDisplayedFamily[],
    targetFamily: CoreCategoricalDisplayedFamily
): CoreCategoricalDisplayedFamily => innerFamilies.reduceRight(
    (target, source) =>
        emdash.mixedDisplayedFunctorFamily(source, target),
    targetFamily
);

const emdash = new CoreCategoricalProgram({
    sourceFile: 'tests/fixtures/categorical-direct-mixed-tower.ts',
    profile: 'fibred-direct-mixed-introduction-1'
});
const K = emdash.category('direct_mixed_tower_K');
const opK = emdash.oppositeCategory(K);
const C = emdash.displayedFamily('direct_mixed_tower_C', K);
const B = emdash.displayedFamily('direct_mixed_tower_B', K);
const D = emdash.displayedFamily('direct_mixed_tower_D', K);
const innerFamilies = (prefix: string, depth: number) =>
    Array.from({ length: depth }, (_, index) =>
        emdash.displayedFamily(
            `direct_mixed_tower_${prefix}_A${index + 1}`,
            opK
        )
    );
const bindings = (
    prefix: string,
    families: readonly CoreCategoricalDisplayedFamily[]
) => families.map((family, index) => ({
    name: `${prefix}a${index + 1}`,
    family
}));

const towerEvidence = (term: CoreCategoricalTerm) =>
    emdash.inspect(term).abstractions.find(candidate =>
        candidate.rule ===
            'categorical.direct-mixed-displayed-functor-tower'
    );

describe('DIRECT-MIXED-TOWER-SOURCE-ACTION-1R direct binder', () => {
    it('lowers depth-two eta directly to the coherent subject', () => {
        const inners = innerFamilies('eta2_', 2);
        const expected = towerFamily(emdash, inners, B);
        const F = emdash.displayedFunctor(
            'direct_mixed_tower_eta2_F',
            C,
            expected
        );
        let calls = 0;
        let receivedFrozenTokens = false;
        const result = emdash.mixedDisplayedFunctorTowerLambda(
            { name: 'eta2c', family: C },
            bindings('eta2', inners),
            B,
            (outer, innerTokens) => {
                calls += 1;
                receivedFrozenTokens = Object.isFrozen(innerTokens);
                return applySpine(
                    emdash,
                    emdash.apply(F, outer),
                    innerTokens
                );
            }
        );
        const compiled = emdash.compile(result);
        const evidence = towerEvidence(result);

        assert.equal(calls, 1);
        assert.equal(
            CORE_CATEGORICAL_DIRECT_MIXED_INTRODUCTION_PROGRAM_REVISION,
            'DIRECT-MIXED-TOWER-SOURCE-ACTION-1R-' +
                'CATEGORICAL-PROGRAM-1'
        );
        assert.equal(receivedFrozenTokens, true);
        assert.equal(
            compiled.explicitCore,
            '(free "direct_mixed_tower_eta2_F")'
        );
        assert.equal(
            compiled.explicitInferredType,
            compiled.explicitExpectedType
        );
        assert.equal(compiled.productionLambdapiDependency, false);
        assert.equal(evidence?.towerDepth, 2);
        assert.equal(evidence?.contextSize, 4);
        assert.deepEqual(evidence?.innerUsageCounts, [1, 1]);
        assert.equal(evidence?.outerUsageCount, 1);
        assert.equal(evidence?.baseUsageCount, 1);
        assert.deepEqual(evidence?.sourceChainLengths, [0, 0]);
        assert.equal(evidence?.sourceActionCount, 0);
        assert.equal(evidence?.sourcePrefixLiftCount, 0);
        assert.equal(evidence?.targetChainLength, 0);
        assert.doesNotMatch(
            compiled.explicitCore,
            /mixed_curry|total.context|coerc|cast|equation/u
        );
        assertDeepFrozen(emdash.inspect(result));
    });

    it('uses the same recursive spine at generated depth six', () => {
        const depth = 6;
        const inners = innerFamilies('eta6_', depth);
        const expected = towerFamily(emdash, inners, B);
        const F = emdash.displayedFunctor(
            'direct_mixed_tower_eta6_F',
            C,
            expected
        );
        const result = emdash.mixedDisplayedFunctorTowerLambda(
            { name: 'eta6c', family: C },
            bindings('eta6', inners),
            B,
            (outer, innerTokens) => applySpine(
                emdash,
                emdash.apply(F, outer),
                innerTokens
            )
        );
        const compiled = emdash.compile(result);
        const evidence = towerEvidence(result);

        assert.equal(
            compiled.explicitCore,
            '(free "direct_mixed_tower_eta6_F")'
        );
        assert.equal(evidence?.towerDepth, depth);
        assert.equal(evidence?.contextSize, depth + 2);
        assert.deepEqual(
            evidence?.innerUsageCounts,
            Array.from({ length: depth }, () => 1)
        );
        assert.equal(evidence?.bindingNames.length, depth + 2);
        assert.equal(evidence?.bindingModes[0], 'natural');
        assert.deepEqual(
            evidence?.bindingModes.slice(1),
            Array.from({ length: depth + 1 }, () => 'functorial')
        );
    });

    it('lowers the depth-three bound outer spine to identity', () => {
        const inners = innerFamilies('identity3_', 3);
        const expected = towerFamily(emdash, inners, B);
        const result = emdash.mixedDisplayedFunctorTowerLambda(
            { name: 'identity3c', family: expected },
            bindings('identity3', inners),
            B,
            (outer, innerTokens) => applySpine(
                emdash,
                outer,
                innerTokens
            )
        );
        const compiled = emdash.compile(result);
        const evidence = towerEvidence(result);

        assert.match(compiled.explicitCore, /displayed-identity/u);
        assert.equal(evidence?.rootKind, 'bound-outer-identity');
        assert.equal(evidence?.towerDepth, 3);
        assert.equal(evidence?.baseUsageCount, 0);
        assert.deepEqual(evidence?.sourceChainLengths, [0, 0, 0]);
        assert.equal(evidence?.sourceActionCount, 0);
        assert.deepEqual(evidence?.innerUsageCounts, [1, 1, 1]);
        assert.deepEqual(evidence?.dependentPrerequisites, [
            'stable-functor-family',
            'displayed-identity'
        ]);
    });

    it('lifts two closed target maps through a depth-three rich target',
    () => {
        const inners = innerFamilies('mapped3_', 3);
        const initialTower = towerFamily(emdash, inners, B);
        const F = emdash.displayedFunctor(
            'direct_mixed_tower_mapped3_F',
            C,
            initialTower
        );
        const G = emdash.displayedFunctor(
            'direct_mixed_tower_mapped3_G',
            B,
            D
        );
        const carrier = emdash.displayedFamily(
            'direct_mixed_tower_mapped3_carrier',
            K
        );
        const source = emdash.section(
            'direct_mixed_tower_mapped3_source',
            emdash.oppositeDisplayedFamily(carrier)
        );
        const target = emdash.section(
            'direct_mixed_tower_mapped3_target',
            carrier
        );
        const richTarget = emdash.mixedDisplayedHomFamily(
            carrier,
            source,
            target
        );
        const H = emdash.displayedFunctor(
            'direct_mixed_tower_mapped3_H',
            D,
            richTarget
        );
        const result = emdash.mixedDisplayedFunctorTowerLambda(
            { name: 'mapped3c', family: C },
            bindings('mapped3', inners),
            richTarget,
            (outer, innerTokens) => {
                const leaf = applySpine(
                    emdash,
                    emdash.apply(F, outer),
                    innerTokens
                );
                return emdash.apply(H, emdash.apply(G, leaf));
            }
        );
        const compiled = emdash.compile(result);
        const evidence = towerEvidence(result);
        const targetActionName = coreCategoricalMixedActionCoreName(
            'mixedFunctorFamilyPartial'
        );

        assert.equal(compiled.surfaceType.tag, 'displayed-functor');
        assert.match(compiled.explicitExpectedType, /Hom_catd/u);
        assert.equal(evidence?.towerDepth, 3);
        assert.equal(evidence?.targetChainLength, 2);
        assert.equal(evidence?.targetLiftCount, 6);
        assert.equal(evidence?.baseUsageCount, 3);
        assert.equal(
            countOccurrences(compiled.explicitCore, 'functor-hom-capped'),
            6
        );
        assert.equal(
            countOccurrences(compiled.explicitCore, targetActionName),
            6
        );
        assert.match(
            compiled.explicitCore,
            /emdash\.categorical\.generic-category-composition/u
        );
        assert.doesNotMatch(
            compiled.explicitCore,
            /mixed_curry|total.context|coerc|cast|equation/u
        );
        assert.equal(compiled.productionLambdapiDependency, false);
        assertDeepFrozen(emdash.inspect(result));
    });

    it('maps a source chain independently at every depth-three layer', () => {
        for (let mappedIndex = 0; mappedIndex < 3; mappedIndex += 1) {
            const prefix = `source_position_${mappedIndex}`;
            const bound = innerFamilies(`${prefix}_bound_`, 3);
            const roots = [...bound];
            roots[mappedIndex] = emdash.displayedFamily(
                `direct_mixed_tower_${prefix}_root`,
                opK
            );
            const mapper = emdash.displayedFunctor(
                `direct_mixed_tower_${prefix}_mapper`,
                bound[mappedIndex],
                roots[mappedIndex]
            );
            const F = emdash.displayedFunctor(
                `direct_mixed_tower_${prefix}_F`,
                C,
                towerFamily(emdash, roots, B)
            );
            let calls = 0;
            const result = emdash.mixedDisplayedFunctorTowerLambda(
                { name: `${prefix}c`, family: C },
                bindings(prefix, bound),
                B,
                (outer, tokens) => {
                    calls += 1;
                    const argumentsWithSource: CoreCategoricalTerm[] = [
                        ...tokens
                    ];
                    argumentsWithSource[mappedIndex] = emdash.apply(
                        mapper,
                        tokens[mappedIndex]
                    );
                    return applySpine(
                        emdash,
                        emdash.apply(F, outer),
                        argumentsWithSource
                    );
                }
            );
            const compiled = emdash.compile(result);
            const evidence = towerEvidence(result);

            assert.equal(calls, 1);
            assert.equal(compiled.surfaceType.tag, 'displayed-functor');
            assert.deepEqual(
                evidence?.sourceChainLengths,
                [0, 0, 0].map((value, index) =>
                    index === mappedIndex ? 1 : value
                )
            );
            assert.equal(evidence?.rootSourceFamilies.length, 3);
            assert.equal(evidence?.sourceActionCount, 1);
            assert.equal(
                evidence?.sourcePrefixLiftCount,
                mappedIndex
            );
            assert.equal(evidence?.baseUsageCount, 2);
            assert.match(compiled.explicitCore, /Functor_catd_func/u);
            assert.doesNotMatch(
                compiled.explicitCore,
                /mixed_curry|total.context|coerc|cast|equation/u
            );
            assert.equal(compiled.productionLambdapiDependency, false);
            assertDeepFrozen(emdash.inspect(result));
        }
    });

    it('composes simultaneous finite source chains deepest-outward', () => {
        const bound = innerFamilies('source_multi_bound_', 3);
        const middle0 = emdash.displayedFamily(
            'direct_mixed_tower_source_multi_middle0',
            opK
        );
        const roots = innerFamilies('source_multi_root_', 3);
        const first0 = emdash.displayedFunctor(
            'direct_mixed_tower_source_multi_first0',
            bound[0],
            middle0
        );
        const second0 = emdash.displayedFunctor(
            'direct_mixed_tower_source_multi_second0',
            middle0,
            roots[0]
        );
        const mapper1 = emdash.displayedFunctor(
            'direct_mixed_tower_source_multi_mapper1',
            bound[1],
            roots[1]
        );
        const mapper2 = emdash.displayedFunctor(
            'direct_mixed_tower_source_multi_mapper2',
            bound[2],
            roots[2]
        );
        const F = emdash.displayedFunctor(
            'direct_mixed_tower_source_multi_F',
            C,
            towerFamily(emdash, roots, B)
        );
        const result = emdash.mixedDisplayedFunctorTowerLambda(
            { name: 'sourceMultic', family: C },
            bindings('sourceMulti', bound),
            B,
            (outer, tokens) => applySpine(
                emdash,
                emdash.apply(F, outer),
                [
                    emdash.apply(
                        second0,
                        emdash.apply(first0, tokens[0])
                    ),
                    emdash.apply(mapper1, tokens[1]),
                    emdash.apply(mapper2, tokens[2])
                ]
            )
        );
        const compiled = emdash.compile(result);
        const evidence = towerEvidence(result);

        assert.deepEqual(evidence?.sourceChainLengths, [2, 1, 1]);
        assert.equal(evidence?.sourceActionCount, 4);
        assert.equal(evidence?.sourcePrefixLiftCount, 3);
        assert.equal(evidence?.baseUsageCount, 5);
        assert.equal(
            countOccurrences(compiled.explicitCore, 'Functor_catd_func'),
            4
        );
        assert.equal(
            countOccurrences(compiled.explicitCore, 'functor-hom-capped'),
            7
        );
        assert.equal(compiled.surfaceType.tag, 'displayed-functor');
        assertDeepFrozen(emdash.inspect(result));
    });

    it('maps a bound-outer root without exposing a total context', () => {
        const bound = innerFamilies('source_identity_bound_', 3);
        const roots = [...bound];
        roots[1] = emdash.displayedFamily(
            'direct_mixed_tower_source_identity_root',
            opK
        );
        const mapper = emdash.displayedFunctor(
            'direct_mixed_tower_source_identity_mapper',
            bound[1],
            roots[1]
        );
        const rootTower = towerFamily(emdash, roots, B);
        const result = emdash.mixedDisplayedFunctorTowerLambda(
            { name: 'sourceIdentityc', family: rootTower },
            bindings('sourceIdentity', bound),
            B,
            (outer, tokens) => applySpine(
                emdash,
                outer,
                [
                    tokens[0],
                    emdash.apply(mapper, tokens[1]),
                    tokens[2]
                ]
            )
        );
        const compiled = emdash.compile(result);
        const evidence = towerEvidence(result);

        assert.equal(evidence?.rootKind, 'bound-outer-identity');
        assert.equal(evidence?.sourceActionCount, 1);
        assert.equal(evidence?.sourcePrefixLiftCount, 1);
        assert.equal(evidence?.baseUsageCount, 1);
        assert.match(compiled.explicitCore, /Functor_catd_func/u);
        assert.doesNotMatch(
            compiled.explicitCore,
            /mixed_curry|total.context|coerc|cast|equation/u
        );
        assertDeepFrozen(emdash.inspect(result));
    });

    it('finishes source actions before target maps into a rich Hom family',
    () => {
        const bound = innerFamilies('source_rich_bound_', 3);
        const roots = [...bound];
        roots[1] = emdash.displayedFamily(
            'direct_mixed_tower_source_rich_root',
            opK
        );
        const mapper = emdash.displayedFunctor(
            'direct_mixed_tower_source_rich_mapper',
            bound[1],
            roots[1]
        );
        const F = emdash.displayedFunctor(
            'direct_mixed_tower_source_rich_F',
            C,
            towerFamily(emdash, roots, B)
        );
        const G = emdash.displayedFunctor(
            'direct_mixed_tower_source_rich_G',
            B,
            D
        );
        const carrier = emdash.displayedFamily(
            'direct_mixed_tower_source_rich_carrier',
            K
        );
        const source = emdash.section(
            'direct_mixed_tower_source_rich_source',
            emdash.oppositeDisplayedFamily(carrier)
        );
        const target = emdash.section(
            'direct_mixed_tower_source_rich_target',
            carrier
        );
        const richTarget = emdash.mixedDisplayedHomFamily(
            carrier,
            source,
            target
        );
        const H = emdash.displayedFunctor(
            'direct_mixed_tower_source_rich_H',
            D,
            richTarget
        );
        const result = emdash.mixedDisplayedFunctorTowerLambda(
            { name: 'sourceRichc', family: C },
            bindings('sourceRich', bound),
            richTarget,
            (outer, tokens) => {
                const leaf = applySpine(
                    emdash,
                    emdash.apply(F, outer),
                    [
                        tokens[0],
                        emdash.apply(mapper, tokens[1]),
                        tokens[2]
                    ]
                );
                return emdash.apply(H, emdash.apply(G, leaf));
            }
        );
        const compiled = emdash.compile(result);
        const evidence = towerEvidence(result);

        assert.equal(evidence?.sourceActionCount, 1);
        assert.equal(evidence?.sourcePrefixLiftCount, 1);
        assert.equal(evidence?.targetChainLength, 2);
        assert.equal(evidence?.targetLiftCount, 6);
        assert.match(compiled.explicitExpectedType, /Hom_catd/u);
        assert.equal(compiled.surfaceType.tag, 'displayed-functor');
        assert.doesNotMatch(
            compiled.explicitCore,
            /mixed_curry|total.context|coerc|cast|equation/u
        );
        assertDeepFrozen(emdash.inspect(result));
    });

    it('uses the same source-action recursion at generated depth six', () => {
        const depth = 6;
        const bound = innerFamilies('source_depth6_bound_', depth);
        const roots = innerFamilies('source_depth6_root_', depth);
        const mappers = bound.map((family, index) =>
            emdash.displayedFunctor(
                `direct_mixed_tower_source_depth6_mapper${index}`,
                family,
                roots[index]
            )
        );
        const F = emdash.displayedFunctor(
            'direct_mixed_tower_source_depth6_F',
            C,
            towerFamily(emdash, roots, B)
        );
        const result = emdash.mixedDisplayedFunctorTowerLambda(
            { name: 'sourceDepth6c', family: C },
            bindings('sourceDepth6', bound),
            B,
            (outer, tokens) => applySpine(
                emdash,
                emdash.apply(F, outer),
                tokens.map((token, index) =>
                    emdash.apply(mappers[index], token)
                )
            )
        );
        const compiled = emdash.compile(result);
        const evidence = towerEvidence(result);

        assert.deepEqual(
            evidence?.sourceChainLengths,
            Array.from({ length: depth }, () => 1)
        );
        assert.equal(evidence?.sourceActionCount, depth);
        assert.equal(evidence?.sourcePrefixLiftCount, 15);
        assert.equal(evidence?.baseUsageCount, depth + 1);
        assert.equal(compiled.surfaceType.tag, 'displayed-functor');
        assert.equal(compiled.productionLambdapiDependency, false);
        assertDeepFrozen(emdash.inspect(result));
    });

    it('fails closed at the tower context and body boundaries', () => {
        const inners = innerFamilies('negative_', 3);
        const expected = towerFamily(emdash, inners, B);
        const F = emdash.displayedFunctor(
            'direct_mixed_tower_negative_F',
            C,
            expected
        );
        const G = emdash.displayedFunctor(
            'direct_mixed_tower_negative_G',
            B,
            D
        );
        const wrongBase = emdash.displayedFamily(
            'direct_mixed_tower_negative_wrong_base',
            K
        );
        const assertRejected = (operation: () => unknown): void => {
            assert.throws(operation, error =>
                error instanceof CoreCategoricalProgramError ||
                error instanceof CoreCategoricalFrontendError
            );
        };

        assertRejected(() =>
            emdash.mixedDisplayedFunctorTowerLambda(
                { name: 'tooShortC', family: C },
                [{ name: 'only', family: inners[0] }],
                B,
                () => { throw new Error('callback must not run'); }
            )
        );
        assertRejected(() =>
            emdash.mixedDisplayedFunctorTowerLambda(
                { name: 'duplicate', family: C },
                [
                    { name: 'duplicate', family: inners[0] },
                    { name: 'other', family: inners[1] }
                ],
                B,
                () => { throw new Error('callback must not run'); }
            )
        );
        assertRejected(() =>
            emdash.mixedDisplayedFunctorTowerLambda(
                { name: 'wrongBaseC', family: C },
                [
                    { name: 'wrongBase', family: wrongBase },
                    { name: 'rightBase', family: inners[1] }
                ],
                B,
                () => { throw new Error('callback must not run'); }
            )
        );

        const direct = (
            suffix: string,
            body: (
                outer: CoreCategoricalSlotToken,
                tokens: readonly CoreCategoricalSlotToken[]
            ) => CoreCategoricalTerm,
            targetFamilyValue = B
        ) => emdash.mixedDisplayedFunctorTowerLambda(
            { name: `${suffix}c`, family: C },
            bindings(suffix, inners),
            targetFamilyValue,
            body
        );
        assertRejected(() => direct('swapped', (outer, tokens) =>
            applySpine(
                emdash,
                emdash.apply(F, outer),
                [tokens[1], tokens[0], tokens[2]]
            )
        ));
        assertRejected(() => direct('missing', (outer, tokens) =>
            applySpine(
                emdash,
                emdash.apply(F, outer),
                tokens.slice(0, 2)
            )
        ));
        assertRejected(() => direct('repeated', (outer, tokens) =>
            applySpine(
                emdash,
                emdash.apply(F, outer),
                [tokens[0], tokens[1], tokens[1]]
            )
        ));
        assertRejected(() => direct('wrongTarget', (outer, tokens) =>
            emdash.apply(
                G,
                applySpine(
                    emdash,
                    emdash.apply(F, outer),
                    tokens
                )
            )
        ));

        const foreignProgram = new CoreCategoricalProgram({
            sourceFile:
                'tests/fixtures/categorical-direct-mixed-tower-foreign.ts'
        });
        const foreignCategory = foreignProgram.category(
            'direct_mixed_tower_foreign_category'
        );
        let foreignToken: CoreCategoricalSlotToken | undefined;
        foreignProgram.lambda(
            'foreignToken',
            foreignCategory,
            foreignCategory,
            token => {
                foreignToken = token;
                return token;
            }
        );
        assert.ok(foreignToken);
        assertRejected(() => direct('foreign', (outer, tokens) =>
            applySpine(
                emdash,
                emdash.apply(F, outer),
                [foreignToken as CoreCategoricalSlotToken, ...tokens.slice(1)]
            )
        ));

        const nonclosedMapper = Object.freeze({
            ...G,
            closed: undefined,
            usage: Object.freeze([])
        }) as unknown as CoreCategoricalTerm;
        assert.throws(
            () => direct(
                'nonclosedMapper',
                (outer, tokens) => emdash.apply(
                    nonclosedMapper,
                    applySpine(
                        emdash,
                        emdash.apply(F, outer),
                        tokens
                    )
                ),
                D
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'UNAVAILABLE_DISPLAYED_ACTION'
        );

        const sourceRoot = emdash.displayedFamily(
            'direct_mixed_tower_negative_source_root',
            opK
        );
        const sourceMap = emdash.displayedFunctor(
            'direct_mixed_tower_negative_source_map',
            inners[0],
            sourceRoot
        );
        const sourceF = emdash.displayedFunctor(
            'direct_mixed_tower_negative_source_F',
            C,
            towerFamily(
                emdash,
                [sourceRoot, ...inners.slice(1)],
                B
            )
        );
        const nonclosedSourceMap = Object.freeze({
            ...sourceMap,
            closed: undefined,
            usage: Object.freeze([])
        }) as unknown as CoreCategoricalTerm;
        assertRejected(() => direct('nonclosedSource', (outer, tokens) =>
            applySpine(
                emdash,
                emdash.apply(sourceF, outer),
                [
                    emdash.apply(nonclosedSourceMap, tokens[0]),
                    ...tokens.slice(1)
                ]
            )
        ));

        const wrongOrientationSource = emdash.displayedFamily(
            'direct_mixed_tower_negative_wrong_orientation_source',
            K
        );
        const wrongOrientationTarget = emdash.displayedFamily(
            'direct_mixed_tower_negative_wrong_orientation_target',
            K
        );
        const wrongOrientationMap = emdash.displayedFunctor(
            'direct_mixed_tower_negative_wrong_orientation_map',
            wrongOrientationSource,
            wrongOrientationTarget
        );
        assertRejected(() => direct('wrongOrientation', (outer, tokens) =>
            applySpine(
                emdash,
                emdash.apply(F, outer),
                [
                    emdash.apply(wrongOrientationMap, tokens[0]),
                    ...tokens.slice(1)
                ]
            )
        ));

        const chainMiddle = emdash.displayedFamily(
            'direct_mixed_tower_negative_chain_middle',
            opK
        );
        const chainOther = emdash.displayedFamily(
            'direct_mixed_tower_negative_chain_other',
            opK
        );
        const chainFirst = emdash.displayedFunctor(
            'direct_mixed_tower_negative_chain_first',
            inners[0],
            chainMiddle
        );
        const chainBroken = emdash.displayedFunctor(
            'direct_mixed_tower_negative_chain_broken',
            chainOther,
            sourceRoot
        );
        assertRejected(() => direct('brokenChain', (outer, tokens) =>
            applySpine(
                emdash,
                emdash.apply(sourceF, outer),
                [
                    emdash.apply(
                        chainBroken,
                        emdash.apply(chainFirst, tokens[0])
                    ),
                    ...tokens.slice(1)
                ]
            )
        ));
        assertRejected(() => direct('unfinishedChain', (outer, tokens) =>
            applySpine(
                emdash,
                emdash.apply(sourceF, outer),
                [
                    emdash.apply(chainFirst, tokens[0]),
                    ...tokens.slice(1)
                ]
            )
        ));

        const shared = emdash.displayedFamily(
            'direct_mixed_tower_negative_shared',
            opK
        );
        const sharedRoot = emdash.displayedFamily(
            'direct_mixed_tower_negative_shared_root',
            opK
        );
        const sharedMapper = emdash.displayedFunctor(
            'direct_mixed_tower_negative_shared_mapper',
            shared,
            sharedRoot
        );
        const sharedF = emdash.displayedFunctor(
            'direct_mixed_tower_negative_shared_F',
            C,
            towerFamily(emdash, [sharedRoot, shared, inners[2]], B)
        );
        assertRejected(() =>
            emdash.mixedDisplayedFunctorTowerLambda(
                { name: 'wrongLayerc', family: C },
                bindings('wrongLayer', [shared, shared, inners[2]]),
                B,
                (outer, tokens) => applySpine(
                    emdash,
                    emdash.apply(sharedF, outer),
                    [
                        emdash.apply(sharedMapper, tokens[1]),
                        tokens[0],
                        tokens[2]
                    ]
                )
            )
        );

        const weakening = emdash.displayedFunctor(
            'direct_mixed_tower_negative_weakening',
            C,
            B
        );
        assertRejected(() => direct('weakening', outer =>
            emdash.apply(weakening, outer)
        ));

        const product = emdash.displayedProduct(B, B);
        assertRejected(() => direct(
            'pair',
            (outer, tokens) => {
                const leaf = applySpine(
                    emdash,
                    emdash.apply(F, outer),
                    tokens
                );
                return emdash.fibrePair(leaf, leaf);
            },
            product
        ));

        const middle = emdash.category(
            'direct_mixed_tower_negative_middle'
        );
        const constantK = emdash.constantDisplayedFamily(K, middle);
        const constantOpK = emdash.constantDisplayedFamily(opK, middle);
        const constantTower = towerFamily(
            emdash,
            inners,
            constantK
        );
        const constantF = emdash.displayedFunctor(
            'direct_mixed_tower_negative_constant_F',
            C,
            constantTower
        );
        const constantG = emdash.displayedFunctor(
            'direct_mixed_tower_negative_constant_G',
            C,
            emdash.mixedDisplayedFunctorFamily(constantOpK, B)
        );
        assertRejected(() => direct('constantMiddle', (outer, tokens) =>
            emdash.apply(
                emdash.apply(constantG, outer),
                applySpine(
                    emdash,
                    emdash.apply(constantF, outer),
                    tokens
                )
            )
        ));

        const transforSource = emdash.displayedFunctor(
            'direct_mixed_tower_negative_transfor_source',
            B,
            D
        );
        const transforTarget = emdash.displayedFunctor(
            'direct_mixed_tower_negative_transfor_target',
            B,
            D
        );
        const transformation = emdash.displayedTransfor(
            'direct_mixed_tower_negative_transformation',
            transforSource,
            transforTarget
        );
        assertRejected(() => direct(
            'nestedTransformation',
            () => emdash.displayedTransforLambda(
                'nestedTransformationBase',
                transforSource,
                transforTarget,
                token => emdash.apply(
                    transformation,
                    token,
                    { expectedShape: 'displayed-component' }
                )
            )
        ));
    });
});
