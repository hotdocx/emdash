/**
 * DIRECT-MIXED-INTRODUCTION-1D direct recursive binder coverage.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CoreCategoricalFrontendError,
    CoreCategoricalProgram,
    CoreCategoricalProgramError,
    coreCategoricalDirectMixedProductDistributionCoreName,
    coreCategoricalDirectMixedWeakeningCoreName,
    coreCategoricalFibredStructureCoreName,
    coreCategoricalMixedActionCoreName,
    serializeCoreExpression
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

const fixture = (suffix: string) => {
    const emdash = new CoreCategoricalProgram({
        sourceFile:
            `tests/fixtures/categorical-direct-mixed-${suffix}.ts`,
        profile: 'fibred-direct-mixed-introduction-1'
    });
    const K = emdash.category(`direct_mixed_${suffix}_K`);
    const opK = emdash.oppositeCategory(K);
    const C = emdash.displayedFamily(
        `direct_mixed_${suffix}_C`,
        K
    );
    const A = emdash.displayedFamily(
        `direct_mixed_${suffix}_A`,
        opK
    );
    const B = emdash.displayedFamily(
        `direct_mixed_${suffix}_B`,
        K
    );
    const D = emdash.displayedFamily(
        `direct_mixed_${suffix}_D`,
        K
    );
    const E = emdash.displayedFamily(
        `direct_mixed_${suffix}_E`,
        K
    );
    const AB = emdash.mixedDisplayedFunctorFamily(A, B);
    const F = emdash.displayedFunctor(
        `direct_mixed_${suffix}_F`,
        C,
        AB
    );
    const G = emdash.displayedFunctor(
        `direct_mixed_${suffix}_G`,
        B,
        D
    );
    const H = emdash.displayedFunctor(
        `direct_mixed_${suffix}_H`,
        D,
        E
    );
    return { emdash, K, opK, C, A, B, D, E, F, G, H };
};

describe('DIRECT-MIXED-INTRODUCTION-1D direct binder', () => {
    it('lowers the fundamental bound-outer application to identity', () => {
        const { emdash, A, B, D, G } = fixture('bound_identity');
        const C = emdash.mixedDisplayedFunctorFamily(A, B);
        const result = emdash.mixedDisplayedFunctorLambda(
            { name: 'c', family: C },
            { name: 'a', family: A },
            B,
            (c, a) => emdash.apply(c, a)
        );
        const mapped = emdash.mixedDisplayedFunctorLambda(
            { name: 'cMapped', family: C },
            { name: 'aMapped', family: A },
            D,
            (c, a) => emdash.apply(G, emdash.apply(c, a))
        );
        const compiled = emdash.compile(result);
        const mappedCompiled = emdash.compile(mapped);
        const inspection = emdash.inspect(result);
        const evidence = inspection.abstractions.find(candidate =>
            candidate.rule ===
                'categorical.direct-mixed-displayed-functor'
        );

        assert.match(compiled.explicitCore, /displayed-identity/u);
        assert.doesNotMatch(compiled.explicitCore, /mixed_curry/u);
        assert.equal(evidence?.rootKind, 'bound-outer-identity');
        assert.equal(evidence?.targetChainLength, 0);
        assert.deepEqual(evidence?.dependentPrerequisites, [
            'stable-functor-family',
            'displayed-identity'
        ]);
        assert.equal(evidence?.body.tag, 'typed-application');
        if (
            evidence?.body.tag !== 'typed-application' ||
            evidence.body.subject.type.tag !== 'indexed-functor'
        ) {
            assert.fail('Missing enriched bound-outer functor view');
        }
        assert.ok(
            evidence.body.subject.type.underlyingObjectFamily
        );
        assert.match(
            mappedCompiled.explicitCore,
            /generic-category-composition/u
        );
        assert.equal(
            emdash.inspect(mapped).abstractions.find(candidate =>
                candidate.rule ===
                    'categorical.direct-mixed-displayed-functor'
            )?.rootKind,
            'bound-outer-identity'
        );
        assertDeepFrozen(inspection);
    });

    it('lowers exact nested eta directly to F with three scoped binders',
    () => {
        const { emdash, C, A, B, F } = fixture('eta');
        let calls = 0;
        const result = emdash.mixedDisplayedFunctorLambda(
            { name: 'c', family: C },
            { name: 'a', family: A },
            B,
            (c, a) => {
                calls += 1;
                return emdash.apply(emdash.apply(F, c), a);
            }
        );
        const compiled = emdash.compile(result);
        const inspection = emdash.inspect(result);
        const evidence = inspection.abstractions.find(candidate =>
            candidate.rule ===
                'categorical.direct-mixed-displayed-functor'
        );

        assert.equal(calls, 1);
        assert.equal(
            compiled.explicitCore,
            '(free "direct_mixed_eta_F")'
        );
        assert.equal(
            compiled.explicitInferredType,
            compiled.explicitExpectedType
        );
        assert.doesNotMatch(compiled.explicitCore, /mixed_curry/u);
        assert.ok(evidence);
        assert.deepEqual(evidence.bindingNames, ['cBase', 'c', 'a']);
        assert.deepEqual(
            evidence.bindingModes,
            ['natural', 'functorial', 'functorial']
        );
        assert.equal(evidence.contextSize, 3);
        assert.equal(evidence.targetChainLength, 0);
        assert.equal(evidence.body.tag, 'typed-application');
        if (evidence.body.tag !== 'typed-application') {
            assert.fail('Missing direct mixed eta body');
        }
        assert.equal(evidence.body.argument.tag, 'slot-reference');
        if (evidence.body.argument.tag === 'slot-reference') {
            assert.equal(evidence.body.argument.index, 0);
        }
        assert.equal(evidence.body.subject.tag, 'typed-application');
        if (evidence.body.subject.tag === 'typed-application') {
            assert.equal(
                evidence.body.subject.argument.tag,
                'slot-reference'
            );
            if (
                evidence.body.subject.argument.tag ===
                    'slot-reference'
            ) {
                assert.equal(evidence.body.subject.argument.index, 1);
            }
            assert.equal(
                evidence.body.subject.subject.tag,
                'typed-application'
            );
            if (
                evidence.body.subject.subject.tag ===
                    'typed-application' &&
                evidence.body.subject.subject.argument.tag ===
                    'slot-reference'
            ) {
                assert.equal(
                    evidence.body.subject.subject.argument.index,
                    2
                );
            }
        }
        assertDeepFrozen(inspection);
    });

    it('retains object membership through a nested positive target', () => {
        const { emdash, K, opK, C, A, D } = fixture('nested_target');
        const X = emdash.displayedFamily(
            'direct_mixed_nested_target_X',
            opK
        );
        const Y = emdash.displayedFamily(
            'direct_mixed_nested_target_Y',
            K
        );
        const nestedTarget = emdash.mixedDisplayedFunctorFamily(X, Y);
        const outerTarget = emdash.mixedDisplayedFunctorFamily(
            A,
            nestedTarget
        );
        const F = emdash.displayedFunctor(
            'direct_mixed_nested_target_F_nested',
            C,
            outerTarget
        );
        const G = emdash.displayedFunctor(
            'direct_mixed_nested_target_G_nested',
            nestedTarget,
            D
        );
        const eta = emdash.mixedDisplayedFunctorLambda(
            { name: 'c', family: C },
            { name: 'a', family: A },
            nestedTarget,
            (c, a) => emdash.apply(emdash.apply(F, c), a)
        );
        const mapped = emdash.mixedDisplayedFunctorLambda(
            { name: 'c2', family: C },
            { name: 'a2', family: A },
            D,
            (c, a) => emdash.apply(
                G,
                emdash.apply(emdash.apply(F, c), a)
            )
        );
        const etaCompiled = emdash.compile(eta);
        const mappedCompiled = emdash.compile(mapped);
        const etaEvidence = emdash.inspect(eta).abstractions.find(
            candidate => candidate.rule ===
                'categorical.direct-mixed-displayed-functor'
        );

        assert.equal(
            etaCompiled.explicitCore,
            '(free "direct_mixed_nested_target_F_nested")'
        );
        assert.equal(
            etaEvidence?.rootKind,
            'closed-coherent-subject'
        );
        assert.equal(etaEvidence?.body.type.tag, 'indexed-functor');
        if (etaEvidence?.body.type.tag !== 'indexed-functor') {
            assert.fail('Missing nested positive indexed-functor result');
        }
        assert.ok(etaEvidence.body.type.underlyingObjectFamily);
        assert.match(
            mappedCompiled.explicitCore,
            /generic-category-composition/u
        );
        assert.doesNotMatch(mappedCompiled.explicitCore, /mixed_curry/u);
    });

    it('uses kernel conversion for natural nested mixed classifiers', () => {
        const { emdash, K, opK, C } = fixture('nested_conversion');

        // These domain families intentionally use natural K rather than a
        // literal Op(Op(K)). The active opposite-involution computation is
        // authoritative for both nested mixed constructors.
        const P = emdash.displayedFamily(
            'direct_mixed_nested_conversion_P',
            K
        );
        const Q = emdash.displayedFamily(
            'direct_mixed_nested_conversion_Q',
            opK
        );
        const PPrime = emdash.displayedFamily(
            'direct_mixed_nested_conversion_P_prime',
            K
        );
        const QPrime = emdash.displayedFamily(
            'direct_mixed_nested_conversion_Q_prime',
            opK
        );
        const nestedSource = emdash.mixedDisplayedFunctorFamily(P, Q);
        const nestedSourcePrime =
            emdash.mixedDisplayedFunctorFamily(PPrime, QPrime);
        const L = emdash.displayedFunctor(
            'direct_mixed_nested_conversion_L',
            nestedSourcePrime,
            nestedSource
        );

        const homCarrier = emdash.displayedFamily(
            'direct_mixed_nested_conversion_hom_carrier',
            K
        );
        const x = emdash.section(
            'direct_mixed_nested_conversion_x',
            emdash.oppositeDisplayedFamily(homCarrier)
        );
        const y = emdash.section(
            'direct_mixed_nested_conversion_y',
            homCarrier
        );
        const homTarget = emdash.mixedDisplayedHomFamily(
            homCarrier,
            x,
            y
        );

        const targetA = emdash.displayedFamily(
            'direct_mixed_nested_conversion_target_A',
            opK
        );
        const targetB = emdash.displayedFamily(
            'direct_mixed_nested_conversion_target_B',
            K
        );
        const functorTarget = emdash.mixedDisplayedFunctorFamily(
            targetA,
            targetB
        );
        const alpha = emdash.section(
            'direct_mixed_nested_conversion_alpha',
            emdash.oppositeDisplayedFamily(functorTarget)
        );
        const beta = emdash.section(
            'direct_mixed_nested_conversion_beta',
            functorTarget
        );
        const transforTarget = emdash.mixedDisplayedTransforFamily(
            targetA,
            targetB,
            alpha,
            beta
        );

        // Exercise the same conversion seam in Transf_catd at base Op(K).
        const functorOverOp =
            emdash.mixedDisplayedFunctorFamily(P, Q);
        const mu = emdash.section(
            'direct_mixed_nested_conversion_mu',
            emdash.oppositeDisplayedFamily(functorOverOp)
        );
        const nu = emdash.section(
            'direct_mixed_nested_conversion_nu',
            functorOverOp
        );
        const transforOverOp = emdash.mixedDisplayedTransforFamily(
            P,
            Q,
            mu,
            nu
        );

        const nestedTarget = emdash.mixedDisplayedFunctorFamily(
            nestedSource,
            homTarget
        );
        const nestedF = emdash.displayedFunctor(
            'direct_mixed_nested_conversion_nested_F',
            C,
            nestedTarget
        );
        const targetG = emdash.displayedFunctor(
            'direct_mixed_nested_conversion_target_G',
            homTarget,
            transforTarget
        );
        const transforSourceTarget =
            emdash.mixedDisplayedFunctorFamily(
                transforOverOp,
                homTarget
            );
        const transforH = emdash.displayedFunctor(
            'direct_mixed_nested_conversion_transfor_H',
            C,
            transforSourceTarget
        );

        const eta = emdash.mixedDisplayedFunctorLambda(
            { name: 'cEta', family: C },
            { name: 'nested', family: nestedSource },
            homTarget,
            (c, nested) => emdash.apply(
                emdash.apply(nestedF, c),
                nested
            )
        );
        const mapped = emdash.mixedDisplayedFunctorLambda(
            { name: 'cMapped', family: C },
            { name: 'nestedPrime', family: nestedSourcePrime },
            transforTarget,
            (c, nestedPrime) => emdash.apply(
                targetG,
                emdash.apply(
                    emdash.apply(nestedF, c),
                    emdash.apply(L, nestedPrime)
                )
            )
        );
        const transforSourceEta = emdash.mixedDisplayedFunctorLambda(
            { name: 'cTransfor', family: C },
            { name: 'etaCell', family: transforOverOp },
            homTarget,
            (c, etaCell) => emdash.apply(
                emdash.apply(transforH, c),
                etaCell
            )
        );

        const etaCompiled = emdash.compile(eta);
        const mappedCompiled = emdash.compile(mapped);
        const transforSourceCompiled = emdash.compile(transforSourceEta);
        const evidence = emdash.inspect(mapped).abstractions.find(
            candidate => candidate.rule ===
                'categorical.direct-mixed-displayed-functor'
        );

        assert.equal(
            etaCompiled.explicitCore,
            '(free "direct_mixed_nested_conversion_nested_F")'
        );
        assert.equal(
            transforSourceCompiled.explicitCore,
            '(free "direct_mixed_nested_conversion_transfor_H")'
        );
        assert.equal(mappedCompiled.surfaceType.tag, 'displayed-functor');
        assert.match(
            mappedCompiled.explicitCore,
            /generic-category-composition/u
        );
        assert.match(mappedCompiled.explicitExpectedType, /Transf_catd/u);
        assert.doesNotMatch(
            mappedCompiled.explicitCore,
            /mixed_curry|coerc|cast/u
        );
        assert.equal(evidence?.sourceChainLength, 1);
        assert.equal(evidence?.targetChainLength, 1);
        assertDeepFrozen(emdash.inspect(mapped));
    });

    it('recursively maps one and two coherent target functors', () => {
        const { emdash, C, A, D, E, F, G, H } =
            fixture('mapped');
        const one = emdash.mixedDisplayedFunctorLambda(
            { name: 'c', family: C },
            { name: 'a', family: A },
            D,
            (c, a) => emdash.apply(
                G,
                emdash.apply(emdash.apply(F, c), a)
            )
        );
        const two = emdash.mixedDisplayedFunctorLambda(
            { name: 'c2', family: C },
            { name: 'a2', family: A },
            E,
            (c, a) => emdash.apply(
                H,
                emdash.apply(
                    G,
                    emdash.apply(emdash.apply(F, c), a)
                )
            )
        );
        const oneCompiled = emdash.compile(one);
        const twoCompiled = emdash.compile(two);
        const actionName = coreCategoricalMixedActionCoreName(
            'mixedFunctorFamilyPartial'
        );
        const oneEvidence = emdash.inspect(one).abstractions.find(
            evidence =>
                evidence.rule ===
                    'categorical.direct-mixed-displayed-functor'
        );
        const twoEvidence = emdash.inspect(two).abstractions.find(
            evidence =>
                evidence.rule ===
                    'categorical.direct-mixed-displayed-functor'
        );

        assert.match(
            oneCompiled.explicitCore,
            /emdash\.categorical\.generic-category-composition/u
        );
        assert.match(oneCompiled.explicitCore, /functor-hom-capped/u);
        assert.match(oneCompiled.explicitCore, new RegExp(actionName, 'u'));
        assert.doesNotMatch(oneCompiled.explicitCore, /mixed_curry/u);
        assert.equal(oneCompiled.surfaceType.tag, 'displayed-functor');
        assert.equal(oneCompiled.productionLambdapiDependency, false);
        assert.equal(oneEvidence?.targetChainLength, 1);
        assert.equal(twoEvidence?.targetChainLength, 2);
        assert.equal(twoCompiled.surfaceType.tag, 'displayed-functor');
        assert.equal(twoCompiled.productionLambdapiDependency, false);
    });

    it('recursively maps finite contravariant sources before target maps',
    () => {
        const { emdash, opK, C, A, B, D, F, G } =
            fixture('source_mapped');
        const APrime = emdash.displayedFamily(
            'direct_mixed_source_mapped_A_prime',
            opK
        );
        const ADoublePrime = emdash.displayedFamily(
            'direct_mixed_source_mapped_A_double_prime',
            opK
        );
        const L = emdash.displayedFunctor(
            'direct_mixed_source_mapped_L',
            APrime,
            A
        );
        const M = emdash.displayedFunctor(
            'direct_mixed_source_mapped_M',
            ADoublePrime,
            APrime
        );
        const boundFamily = emdash.mixedDisplayedFunctorFamily(A, B);
        const boundIdentity = emdash.mixedDisplayedFunctorLambda(
            { name: 'h', family: boundFamily },
            { name: 'aPrime', family: APrime },
            B,
            (h, aPrime) => emdash.apply(
                h,
                emdash.apply(L, aPrime)
            )
        );
        const eta = emdash.mixedDisplayedFunctorLambda(
            { name: 'c', family: C },
            { name: 'aPrime', family: APrime },
            B,
            (c, aPrime) => emdash.apply(
                emdash.apply(F, c),
                emdash.apply(L, aPrime)
            )
        );
        const twoSources = emdash.mixedDisplayedFunctorLambda(
            { name: 'c2', family: C },
            { name: 'aDoublePrime', family: ADoublePrime },
            B,
            (c, aDoublePrime) => emdash.apply(
                emdash.apply(F, c),
                emdash.apply(L, emdash.apply(M, aDoublePrime))
            )
        );
        const sourceThenTarget = emdash.mixedDisplayedFunctorLambda(
            { name: 'c3', family: C },
            { name: 'aPrime2', family: APrime },
            D,
            (c, aPrime) => emdash.apply(
                G,
                emdash.apply(
                    emdash.apply(F, c),
                    emdash.apply(L, aPrime)
                )
            )
        );
        const boundCompilation = emdash.compile(boundIdentity);
        const etaCompilation = emdash.compile(eta);
        const twoCompilation = emdash.compile(twoSources);
        const mixedCompilation = emdash.compile(sourceThenTarget);
        const evidence = (term: typeof eta) =>
            emdash.inspect(term).abstractions.find(candidate =>
                candidate.rule ===
                    'categorical.direct-mixed-displayed-functor'
            );

        assert.match(boundCompilation.explicitCore, /displayed-identity/u);
        assert.match(
            boundCompilation.explicitCore,
            /Functor_catd_func/u
        );
        assert.doesNotMatch(boundCompilation.explicitCore, /mixed_curry/u);
        assert.match(etaCompilation.explicitCore, /generic-category-composition/u);
        assert.match(twoCompilation.explicitCore, /generic-category-composition/u);
        assert.match(mixedCompilation.explicitCore, /generic-category-composition/u);
        assert.equal(evidence(eta)?.sourceChainLength, 1);
        assert.equal(evidence(twoSources)?.sourceChainLength, 2);
        assert.equal(evidence(sourceThenTarget)?.sourceChainLength, 1);
        assert.equal(evidence(sourceThenTarget)?.targetChainLength, 1);
        assert.deepEqual(evidence(twoSources)?.bindingNames, [
            'c2Base',
            'c2',
            'aDoublePrime'
        ]);
        assert.deepEqual(evidence(twoSources)?.bindingModes, [
            'natural',
            'functorial',
            'functorial'
        ]);
        assertDeepFrozen(emdash.inspect(twoSources));
    });

    it('recursively compiles distinct, contracted and mapped fibre pairs',
    () => {
        const { emdash, C, A, B, D, E, F } = fixture('product');
        const AD = emdash.mixedDisplayedFunctorFamily(A, D);
        const F2 = emdash.displayedFunctor(
            'direct_mixed_product_F2',
            C,
            AD
        );
        const productBD = emdash.displayedProduct(B, D);
        const productBB = emdash.displayedProduct(B, B);
        const consumePair = emdash.displayedFunctor(
            'direct_mixed_product_consume_pair',
            productBD,
            E
        );
        const distinct = emdash.mixedDisplayedFunctorLambda(
            { name: 'cDistinct', family: C },
            { name: 'aDistinct', family: A },
            productBD,
            (c, a) => emdash.fibrePair(
                emdash.apply(emdash.apply(F, c), a),
                emdash.apply(emdash.apply(F2, c), a)
            )
        );
        const contracted = emdash.mixedDisplayedFunctorLambda(
            { name: 'cContract', family: C },
            { name: 'aContract', family: A },
            productBB,
            (c, a) => {
                const leaf = emdash.apply(emdash.apply(F, c), a);
                return emdash.fibrePair(leaf, leaf);
            }
        );
        const mapped = emdash.mixedDisplayedFunctorLambda(
            { name: 'cMappedPair', family: C },
            { name: 'aMappedPair', family: A },
            E,
            (c, a) => emdash.apply(
                consumePair,
                emdash.fibrePair(
                    emdash.apply(emdash.apply(F, c), a),
                    emdash.apply(emdash.apply(F2, c), a)
                )
            )
        );
        const distinctCompiled = emdash.compile(distinct);
        const contractedCompiled = emdash.compile(contracted);
        const mappedCompiled = emdash.compile(mapped);
        const pairName = coreCategoricalFibredStructureCoreName(
            'displayed-product-pair'
        );
        const distributorName =
            coreCategoricalDirectMixedProductDistributionCoreName(
                'distributor'
            );
        const evidence = emdash.inspect(distinct).abstractions.find(
            candidate => candidate.rule ===
                'categorical.direct-mixed-displayed-functor'
        );
        const mappedEvidence = emdash.inspect(mapped).abstractions.find(
            candidate => candidate.rule ===
                'categorical.direct-mixed-displayed-functor'
        );

        for (const compiled of [
            distinctCompiled,
            contractedCompiled,
            mappedCompiled
        ]) {
            const rawCore = serializeCoreExpression(
                compiled.explicitTerm
            );
            assert.equal(
                compiled.surfaceType.tag,
                'displayed-functor'
            );
            assert.match(rawCore, new RegExp(pairName, 'u'));
            assert.match(
                rawCore,
                new RegExp(distributorName, 'u')
            );
            assert.doesNotMatch(
                compiled.explicitCore,
                /mixed_curry|coerc|cast/u
            );
        }
        assert.equal(evidence?.rootKind, 'recursive-pair');
        assert.equal(evidence?.leafCount, 2);
        assert.equal(evidence?.pairNodeCount, 1);
        assert.equal(evidence?.pairDepth, 1);
        assert.deepEqual(evidence?.dependentPrerequisites, [
            'stable-functor-family',
            'internal-product-functor',
            'displayed-product-pair',
            'mixed-functor-product-distributor',
            'generic-category-composition',
            'displayed-hom-classifier-reduction'
        ]);
        assert.equal(mappedEvidence?.targetChainLength, 1);
        assertDeepFrozen(emdash.inspect(distinct));
        assertDeepFrozen(emdash.inspect(mapped));
    });

    it('recurses through source/target maps and generated deep pair trees',
    () => {
        const { emdash, opK, C, A, B, D, F, G } =
            fixture('deep_product');
        const APrime = emdash.displayedFamily(
            'direct_mixed_deep_product_A_prime',
            opK
        );
        const L = emdash.displayedFunctor(
            'direct_mixed_deep_product_L',
            APrime,
            A
        );
        const mappedProduct = emdash.displayedProduct(B, D);
        const mappedBranches = emdash.mixedDisplayedFunctorLambda(
            { name: 'cBranches', family: C },
            { name: 'aBranches', family: APrime },
            mappedProduct,
            (c, a) => {
                const sourceMapped = emdash.apply(
                    emdash.apply(F, c),
                    emdash.apply(L, a)
                );
                return emdash.fibrePair(
                    sourceMapped,
                    emdash.apply(G, sourceMapped)
                );
            }
        );

        const depth = 7;
        let deepTarget = B;
        for (let index = 0; index < depth; index += 1) {
            deepTarget = emdash.displayedProduct(deepTarget, B);
        }
        const deep = emdash.mixedDisplayedFunctorLambda(
            { name: 'cDeep', family: C },
            { name: 'aDeep', family: A },
            deepTarget,
            (c, a) => {
                const leaf = emdash.apply(emdash.apply(F, c), a);
                let tree = leaf;
                for (let index = 0; index < depth; index += 1) {
                    tree = emdash.fibrePair(tree, leaf);
                }
                return tree;
            }
        );
        const mappedCompiled = emdash.compile(mappedBranches);
        const deepCompiled = emdash.compile(deep);
        const mappedEvidence = emdash.inspect(mappedBranches)
            .abstractions.find(candidate => candidate.rule ===
                'categorical.direct-mixed-displayed-functor');
        const deepEvidence = emdash.inspect(deep).abstractions.find(
            candidate => candidate.rule ===
                'categorical.direct-mixed-displayed-functor'
        );

        assert.equal(mappedCompiled.surfaceType.tag, 'displayed-functor');
        assert.equal(deepCompiled.surfaceType.tag, 'displayed-functor');
        assert.equal(mappedEvidence?.leafCount, 2);
        assert.equal(mappedEvidence?.sourceChainLength, 2);
        assert.equal(mappedEvidence?.targetChainLength, 1);
        assert.equal(deepEvidence?.leafCount, depth + 1);
        assert.equal(deepEvidence?.pairNodeCount, depth);
        assert.equal(deepEvidence?.pairDepth, depth);
        assert.doesNotMatch(
            deepCompiled.explicitCore,
            /mixed_curry|coerc|cast/u
        );
        assertDeepFrozen(emdash.inspect(deep));
    });

    it('directly weakens an unused inner binder and recurses above it', () => {
        const { emdash, C, A, B, D, F, G } = fixture('weakening');
        const H = emdash.displayedFunctor(
            'direct_mixed_weakening_outer_H',
            C,
            B
        );
        const product = emdash.displayedProduct(B, B);
        const direct = emdash.mixedDisplayedFunctorLambda(
            { name: 'c', family: C },
            { name: 'a', family: A },
            B,
            (c, _a) => emdash.apply(H, c)
        );
        const mapped = emdash.mixedDisplayedFunctorLambda(
            { name: 'cMapped', family: C },
            { name: 'aMapped', family: A },
            D,
            (c, _a) => emdash.apply(G, emdash.apply(H, c))
        );
        const paired = emdash.mixedDisplayedFunctorLambda(
            { name: 'cPair', family: C },
            { name: 'aPair', family: A },
            product,
            (c, a) => emdash.fibrePair(
                emdash.apply(H, c),
                emdash.apply(emdash.apply(F, c), a)
            )
        );
        const directCompiled = emdash.compile(direct);
        const mappedCompiled = emdash.compile(mapped);
        const pairedCompiled = emdash.compile(paired);
        const directEvidence = emdash.inspect(direct).abstractions.find(
            candidate => candidate.rule ===
                'categorical.direct-mixed-displayed-functor'
        );
        const pairEvidence = emdash.inspect(paired).abstractions.find(
            candidate => candidate.rule ===
                'categorical.direct-mixed-displayed-functor'
        );
        const weakeningName = coreCategoricalDirectMixedWeakeningCoreName(
            'weakening'
        );

        assert.equal(directEvidence?.rootKind, 'outer-value-weakening');
        assert.equal(directEvidence?.leafCount, 1);
        assert.equal(directEvidence?.outerUsageCount, 1);
        assert.equal(directEvidence?.innerUsageCount, 0);
        assert.deepEqual(directEvidence?.dependentPrerequisites, [
            'stable-functor-family',
            'mixed-functor-weakening',
            'generic-category-composition',
            'displayed-hom-classifier-reduction'
        ]);
        assert.match(
            directCompiled.explicitCore,
            new RegExp(weakeningName, 'u')
        );
        assert.match(
            mappedCompiled.explicitCore,
            new RegExp(weakeningName, 'u')
        );
        assert.equal(pairEvidence?.rootKind, 'recursive-pair');
        assert.equal(pairEvidence?.leafCount, 2);
        assert.equal(pairEvidence?.outerUsageCount, 2);
        assert.equal(pairEvidence?.innerUsageCount, 1);
        assert.match(
            pairedCompiled.explicitCore,
            new RegExp(weakeningName, 'u')
        );
        assert.match(
            pairedCompiled.explicitCore,
            new RegExp(
                coreCategoricalDirectMixedProductDistributionCoreName(
                    'distributor'
                ),
                'u'
            )
        );
        assert.doesNotMatch(
            `${directCompiled.explicitCore}\n` +
                `${mappedCompiled.explicitCore}\n` +
                pairedCompiled.explicitCore,
            /mixed_curry|mix_uncurried_family|coerc|cast/u
        );
        assertDeepFrozen(emdash.inspect(paired));
    });

    it('fails closed for wrong variance and unsupported bodies',
    () => {
        const { emdash, K, opK, C, A, B, D, F } =
            fixture('negative');
        const wrongA = emdash.displayedFamily(
            'direct_mixed_negative_wrong_A',
            K
        );
        assert.throws(
            () => emdash.mixedDisplayedFunctorLambda(
                { name: 'c', family: C },
                { name: 'a', family: wrongA },
                B,
                (_c, _a) => emdash.apply(
                    emdash.displayedFunctor(
                        'direct_mixed_negative_CB',
                        C,
                        B
                    ),
                    _c
                )
            ),
            (error: unknown) =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'DISPLAYED_BASE_MISMATCH'
        );

        const otherA = emdash.displayedFamily(
            'direct_mixed_negative_other_A',
            opK
        );
        assert.throws(
            () => emdash.mixedDisplayedFunctorLambda(
                { name: 'c', family: C },
                { name: 'a', family: otherA },
                B,
                (c, a) => emdash.apply(emdash.apply(F, c), a)
            ),
            (error: unknown) =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
        );

        const unrelatedK = emdash.category(
            'direct_mixed_negative_unrelated_K'
        );
        const unrelatedSource = emdash.displayedFamily(
            'direct_mixed_negative_unrelated_source',
            emdash.oppositeCategory(unrelatedK)
        );
        const unrelatedTarget = emdash.displayedFamily(
            'direct_mixed_negative_unrelated_target',
            emdash.oppositeCategory(unrelatedK)
        );
        const unrelatedMap = emdash.displayedFunctor(
            'direct_mixed_negative_unrelated_map',
            unrelatedSource,
            unrelatedTarget
        );
        assert.throws(
            () => emdash.mixedDisplayedFunctorLambda(
                { name: 'cSource', family: C },
                { name: 'aSource', family: otherA },
                B,
                (c, a) => emdash.apply(
                    emdash.apply(F, c),
                    emdash.apply(unrelatedMap, a)
                )
            ),
            (error: unknown) =>
                (
                    error instanceof CoreCategoricalFrontendError &&
                    error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
                ) || (
                    error instanceof CoreCategoricalProgramError &&
                    error.code === 'DISPLAYED_BASE_MISMATCH'
                )
        );

        assert.throws(
            () => emdash.mixedDisplayedFunctorLambda(
                { name: 'c', family: C },
                { name: 'a', family: A },
                B,
                (c, _a) => emdash.apply(emdash.apply(F, c), _a),
                { polarity: 'contravariant' }
            ),
            (error: unknown) =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'POLARITY_MISMATCH'
        );
    });

    it('keeps the binder behind its dedicated profile', () => {
        const emdash = new CoreCategoricalProgram({
            profile: 'fibred-displayed-mixed-nest-1'
        });
        const K = emdash.category('direct_mixed_gate_K');
        const C = emdash.displayedFamily('direct_mixed_gate_C', K);
        const A = emdash.displayedFamily(
            'direct_mixed_gate_A',
            emdash.oppositeCategory(K)
        );
        const B = emdash.displayedFamily('direct_mixed_gate_B', K);
        assert.throws(
            () => emdash.mixedDisplayedFunctorLambda(
                { name: 'c', family: C },
                { name: 'a', family: A },
                B,
                (_c, _a) => _c
            ),
            (error: unknown) =>
                error instanceof CoreCategoricalProgramError &&
                error.code ===
                    'UNAVAILABLE_DIRECT_MIXED_INTRODUCTION'
        );
    });
});
