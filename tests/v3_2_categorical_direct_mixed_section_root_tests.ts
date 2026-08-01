/**
 * DIRECT-MIXED-SECTION-ROOT-1K TypeScript-only structural coverage.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CoreCategoricalFrontendError,
    CoreCategoricalProgram,
    coreCategoricalDirectMixedProductDistributionCoreName,
    coreCategoricalDirectMixedWeakeningCoreName
} from '../src/v3_2';
import type {
    CoreCategoricalTerm
} from '../src/v3_2';

const fixture = (suffix: string) => {
    const emdash = new CoreCategoricalProgram({
        sourceFile:
            `tests/fixtures/categorical-direct-section-${suffix}.ts`,
        profile: 'fibred-direct-mixed-introduction-1'
    });
    const K = emdash.category(`direct_section_${suffix}_K`);
    const opK = emdash.oppositeCategory(K);
    const C = emdash.displayedFamily(
        `direct_section_${suffix}_C`,
        K
    );
    const A = emdash.displayedFamily(
        `direct_section_${suffix}_A`,
        opK
    );
    const B = emdash.displayedFamily(
        `direct_section_${suffix}_B`,
        K
    );
    const D = emdash.displayedFamily(
        `direct_section_${suffix}_D`,
        K
    );
    const mixed = emdash.mixedDisplayedFunctorFamily(A, B);
    const S = emdash.section(`direct_section_${suffix}_S`, mixed);
    const b = emdash.section(`direct_section_${suffix}_b`, B);
    const F = emdash.displayedFunctor(
        `direct_section_${suffix}_F`,
        C,
        mixed
    );
    const G = emdash.displayedFunctor(
        `direct_section_${suffix}_G`,
        B,
        D
    );
    return {
        emdash,
        K,
        C,
        A,
        B,
        D,
        mixed,
        S,
        b,
        F,
        G
    };
};

const directEvidence = (
    emdash: CoreCategoricalProgram,
    term: Parameters<CoreCategoricalProgram['compile']>[0]
) => emdash.inspect(term).abstractions.find(candidate =>
    candidate.rule === 'categorical.direct-mixed-displayed-functor'
);

describe('DIRECT-MIXED-SECTION-ROOT-1K direct section roots', () => {
    it('reifies S[k] and lowers S[k](a) through terminal weakening', () => {
        const { emdash, C, A, B, S } = fixture('functor');
        const term = emdash.mixedDisplayedFunctorLambda(
            { name: 'c', family: C },
            { name: 'a', family: A },
            B,
            (_c, a) => emdash.apply(
                emdash.apply(S, emdash.indexOf(a), {
                    expectedShape: 'fibre-functor'
                }),
                a,
                { expectedShape: 'object-value' }
            )
        );
        const compiled = emdash.compile(term);
        const evidence = directEvidence(emdash, term);
        const normalizedBody = evidence?.body;

        assert.equal(
            evidence?.rootKind,
            'section-functor-outer-weakening'
        );
        assert.equal(evidence?.outerUsageCount, 0);
        assert.equal(evidence?.innerUsageCount, 1);
        assert.equal(evidence?.leafCount, 1);
        assert.equal(normalizedBody?.tag, 'typed-application');
        if (
            normalizedBody?.tag !== 'typed-application' ||
            normalizedBody.subject.type.tag !== 'indexed-functor'
        ) {
            assert.fail('S[k](a) lost its canonical indexed-functor view');
        }
        assert.equal(
            normalizedBody.subject.type.underlyingObjectFamily !==
                undefined,
            true
        );
        assert.match(
            compiled.explicitCore,
            /displayed-terminal|Terminal_funcd/u
        );
        assert.equal(
            compiled.explicitCore.includes(
                coreCategoricalDirectMixedWeakeningCoreName('weakening')
            ),
            false
        );
        assert.match(compiled.explicitCore, /generic-category-composition/u);
        assert.doesNotMatch(
            compiled.explicitCore,
            /mixed_curry|mix_uncurried_family|coerc|cast/u
        );
    });

    it('lowers b[k] through direct inner and terminal outer weakening', () => {
        const { emdash, C, A, B, b } = fixture('value');
        const term = emdash.mixedDisplayedFunctorLambda(
            { name: 'c', family: C },
            { name: 'a', family: A },
            B,
            (c, _a) => emdash.apply(
                b,
                emdash.indexOf(c),
                { expectedShape: 'dependent-object' }
            )
        );
        const compiled = emdash.compile(term);
        const evidence = directEvidence(emdash, term);

        assert.equal(
            evidence?.rootKind,
            'section-value-full-weakening'
        );
        assert.equal(evidence?.outerUsageCount, 0);
        assert.equal(evidence?.innerUsageCount, 0);
        assert.equal(evidence?.leafCount, 1);
        assert.match(
            compiled.explicitCore,
            /displayed-terminal|Terminal_funcd/u
        );
        assert.equal(
            compiled.explicitCore.includes(
                coreCategoricalDirectMixedWeakeningCoreName('weakening')
            ),
            true
        );
        assert.doesNotMatch(
            compiled.explicitCore,
            /mixed_curry|mix_uncurried_family|coerc|cast/u
        );
    });

    it('recursively maps and pairs both section-root forms', () => {
        const { emdash, C, A, B, D, S, b, F, G } =
            fixture('recursive');
        const sectionValue = (a: CoreCategoricalTerm) =>
            emdash.apply(
                emdash.apply(S, emdash.indexOf(a), {
                    expectedShape: 'fibre-functor'
                }),
                a,
                { expectedShape: 'object-value' }
            );
        const mappedSection = emdash.mixedDisplayedFunctorLambda(
            { name: 'cS', family: C },
            { name: 'aS', family: A },
            D,
            (_c, a) => emdash.apply(G, sectionValue(a))
        );
        const mappedConstant = emdash.mixedDisplayedFunctorLambda(
            { name: 'cB', family: C },
            { name: 'aB', family: A },
            D,
            (c, _a) => emdash.apply(
                G,
                emdash.apply(b, emdash.indexOf(c), {
                    expectedShape: 'dependent-object'
                })
            )
        );
        const product = emdash.displayedProduct(
            B,
            emdash.displayedProduct(B, B)
        );
        const paired = emdash.mixedDisplayedFunctorLambda(
            { name: 'cPair', family: C },
            { name: 'aPair', family: A },
            product,
            (c, a) => emdash.fibrePair(
                sectionValue(a),
                emdash.fibrePair(
                    emdash.apply(b, emdash.indexOf(c), {
                        expectedShape: 'dependent-object'
                    }),
                    emdash.apply(emdash.apply(F, c), a)
                )
            )
        );
        const mappedSectionCompiled = emdash.compile(mappedSection);
        const mappedConstantCompiled = emdash.compile(mappedConstant);
        const pairedCompiled = emdash.compile(paired);
        const pairedEvidence = directEvidence(emdash, paired);

        assert.equal(
            directEvidence(emdash, mappedSection)?.rootKind,
            'section-functor-outer-weakening'
        );
        assert.equal(
            directEvidence(emdash, mappedConstant)?.rootKind,
            'section-value-full-weakening'
        );
        assert.equal(pairedEvidence?.rootKind, 'recursive-pair');
        assert.equal(pairedEvidence?.leafCount, 3);
        assert.equal(pairedEvidence?.outerUsageCount, 1);
        assert.equal(pairedEvidence?.innerUsageCount, 2);
        assert.equal(
            pairedCompiled.explicitCore.includes(
                coreCategoricalDirectMixedProductDistributionCoreName(
                    'distributor'
                )
            ),
            true
        );
        assert.doesNotMatch(
            [
                mappedSectionCompiled.explicitCore,
                mappedConstantCompiled.explicitCore,
                pairedCompiled.explicitCore
            ].join('\n'),
            /mixed_curry|mix_uncurried_family|coerc|cast/u
        );
    });

    it('keeps noncanonical section fibre views fail-closed', () => {
        const { emdash, K, C, A, B, D } = fixture('negative');
        const wrong = emdash.section('direct_section_wrong', D);
        assert.throws(
            () => emdash.mixedDisplayedFunctorLambda(
                { name: 'c', family: C },
                { name: 'a', family: A },
                B,
                (_c, a) => emdash.apply(
                    wrong,
                    emdash.indexOf(a),
                    { expectedShape: 'fibre-functor' }
                )
            ),
            (error: unknown) =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
        );
        const k = emdash.object('direct_section_closed_k', K);
        const mixed = emdash.mixedDisplayedFunctorFamily(A, B);
        const closedSection = emdash.section(
            'direct_section_closed',
            mixed
        );
        assert.throws(
            () => emdash.apply(closedSection, k, {
                expectedShape: 'fibre-functor'
            }),
            (error: unknown) =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
        );
    });
});
