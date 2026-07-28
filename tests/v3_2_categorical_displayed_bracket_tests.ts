/**
 * DISPLAYED-BRACKET-1A generic first-order displayed contextual compiler.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_DISPLAYED_BRACKET_CONTRACT,
    CORE_CATEGORICAL_DISPLAYED_BRACKET_PROGRAM_REVISION,
    CORE_CATEGORICAL_DISPLAYED_BRACKET_REVIEW,
    CoreCategoricalFrontendError,
    CoreCategoricalProgram,
    CoreCategoricalProgramError,
    CoreCategoricalSlotToken,
    CoreLfComparisonResult,
    coreCategoricalClosedContextClassifier,
    coreCategoricalContextSlotReference,
    coreCategoricalDisplayedContextClassifier,
    kernelFree,
    planCoreCategoricalContextDependencies,
    provenance,
    sourceSpan
} from '../src/v3_2';

const runtimeRuleIds = (
    result: CoreLfComparisonResult
): readonly string[] => result.trace.flatMap(entry =>
    entry.reduction.kind === 'runtime'
        ? [entry.reduction.ruleId]
        : []
);

const fixture = () => {
    const emdash = new CoreCategoricalProgram({
        sourceFile:
            'tests/fixtures/categorical-displayed-bracket.ts',
        profile: 'fibred-displayed-bracket-1'
    });
    const K = emdash.category('K', { line: 1 });
    const B = emdash.displayedFamily('B', K, { line: 2 });
    const C = emdash.displayedFamily('C', K, { line: 3 });
    const D = emdash.displayedFamily('D', K, { line: 4 });
    const Q = emdash.displayedFamily('Q', K, { line: 5 });
    const R = emdash.displayedFamily('R', K, { line: 6 });
    const FF = emdash.displayedFunctor('FF', B, D, { line: 7 });
    const GG = emdash.displayedFunctor('GG', C, Q, { line: 8 });
    const HH = emdash.displayedFunctor('HH', D, R, { line: 9 });
    const x = emdash.object('x', K, { line: 10 });
    const y = emdash.object('y', K, { line: 11 });
    const p = emdash.hom('p', K, x, y, { line: 12 });
    return {
        emdash,
        K,
        B,
        C,
        D,
        Q,
        R,
        FF,
        GG,
        HH,
        x,
        y,
        p
    };
};

describe('DISPLAYED-BRACKET-1A displayed contextual compiler', () => {
    it('compiles projection once and computes object and arrow action', () => {
        assert.equal(
            CORE_CATEGORICAL_DISPLAYED_BRACKET_PROGRAM_REVISION,
            'DISPLAYED-BRACKET-1A-CATEGORICAL-PROGRAM-1'
        );
        assert.equal(
            CORE_CATEGORICAL_DISPLAYED_BRACKET_CONTRACT
                .approval.reviewRevision,
            CORE_CATEGORICAL_DISPLAYED_BRACKET_REVIEW.revision
        );
        assert.equal(
            CORE_CATEGORICAL_DISPLAYED_BRACKET_CONTRACT
                .authority.runtimeFoundation,
            'fibred-weaken-reindex-1'
        );
        const {
            emdash,
            B,
            C,
            x,
            y,
            p
        } = fixture();
        let callbacks = 0;
        const projection = emdash.displayedContextLambda(
            [
                { name: 'b', family: B },
                { name: 'c', family: C }
            ],
            B,
            ([b]) => {
                callbacks += 1;
                return b;
            },
            { source: { line: 20 } }
        );
        assert.equal(callbacks, 1);
        const compiled = emdash.compile(projection);
        const evidence = compiled.abstractions.at(-1);
        assert.equal(
            evidence?.rule,
            'categorical.displayed-context-bracket'
        );
        if (
            evidence?.rule !==
                'categorical.displayed-context-bracket'
        ) {
            assert.fail('Missing displayed contextual evidence');
        }
        assert.deepEqual(evidence.bindingNames, ['b', 'c']);
        assert.equal(evidence.contextSize, 2);
        assert.equal(evidence.body.tag, 'slot-reference');
        if (evidence.body.tag !== 'slot-reference') {
            assert.fail('Projection body lost its slot');
        }
        assert.equal(evidence.body.index, 1);
        assert.equal(evidence.body.type.tag, 'indexed-object');
        if (evidence.body.type.tag !== 'indexed-object') {
            assert.fail('Projection body lost its indexed type');
        }
        assert.equal(evidence.body.type.index, 2);
        assert.match(
            compiled.explicitCore,
            /displayed-product-left-projection/u
        );

        const Bx = emdash.fibre(B, x);
        const Cx = emdash.fibre(C, x);
        const point = emdash.apply(projection, x, {
            expectedShape: 'fibre-functor'
        });
        const expectedPoint =
            emdash.productLeftProjection(Bx, Cx);
        const pointResult = emdash.compare(
            point,
            expectedPoint,
            4_000
        );
        assert.equal(pointResult.status, 'equal');
        assert.equal(
            runtimeRuleIds(pointResult).includes(
                'categorical.fibred-structure.left-projection.point'
            ),
            true
        );

        const capped = emdash.apply(projection, p, {
            expectedShape: 'transport-functor'
        });
        const fullAtP = emdash.apply(
            emdash.displayedFunctorFullAction(
                projection,
                x,
                y
            ),
            p
        );
        const arrowResult = emdash.compare(
            capped,
            fullAtP,
            4_000
        );
        assert.equal(arrowResult.status, 'equal');
        assert.equal(
            runtimeRuleIds(arrowResult).includes(
                'categorical.fibred-structure.' +
                    'left-projection.capped-action'
            ),
            true
        );
    });

    it('derives exchange and contraction from one typed-pair node', () => {
        const {
            emdash,
            B,
            C
        } = fixture();
        const swappedTarget = emdash.displayedProduct(C, B);
        const swap = emdash.displayedContextLambda(
            [
                { name: 'b', family: B },
                { name: 'c', family: C }
            ],
            swappedTarget,
            ([b, c]) => emdash.fibrePair(c, b)
        );
        const swapEvidence = emdash.inspect(swap).abstractions.at(-1);
        assert.equal(
            swapEvidence?.rule,
            'categorical.displayed-context-bracket'
        );
        if (
            swapEvidence?.rule !==
                'categorical.displayed-context-bracket'
        ) {
            assert.fail('Missing displayed swap evidence');
        }
        assert.equal(swapEvidence.body.tag, 'typed-pair');
        assert.match(
            emdash.compile(swap).explicitCore,
            /displayed-product-pair/u
        );
        assert.equal(
            emdash.compare(
                swap,
                emdash.displayedProductSwap(B, C),
                4_000
            ).status,
            'equal'
        );

        const diagonalTarget = emdash.displayedProduct(B, B);
        const diagonal = emdash.displayedContextLambda(
            [{ name: 'b', family: B }],
            diagonalTarget,
            ([b]) => emdash.fibrePair(b, b)
        );
        assert.equal(
            emdash.inspect(diagonal).abstractions.at(-1)?.body.tag,
            'typed-pair'
        );
        assert.equal(
            emdash.compare(
                diagonal,
                emdash.displayedProductDiagonal(B),
                4_000
            ).status,
            'equal'
        );
    });

    it('composes closed displayed functors in both pair branches', () => {
        const {
            emdash,
            B,
            C,
            D,
            Q,
            FF,
            GG,
            x
        } = fixture();
        const target = emdash.displayedProduct(D, Q);
        const mapped = emdash.displayedContextLambda(
            [
                { name: 'b', family: B },
                { name: 'c', family: C }
            ],
            target,
            ([b, c]) => emdash.fibrePair(
                emdash.apply(FF, b),
                emdash.apply(GG, c)
            )
        );
        const compiled = emdash.compile(mapped);
        assert.match(
            compiled.explicitCore,
            /generic-category-composition/u
        );
        assert.deepEqual(
            compiled.dependentPrerequisites.includes(
                'displayed-product-pair'
            ),
            true
        );

        const source = emdash.displayedProduct(B, C);
        const leftProjection =
            emdash.displayedProductLeftProjection(B, C);
        const rightProjection =
            emdash.displayedProductRightProjection(B, C);
        const leftMapped = emdash.displayedFunctorLambda(
            'bc',
            source,
            D,
            bc => emdash.apply(
                FF,
                emdash.apply(leftProjection, bc)
            )
        );
        const rightMapped = emdash.displayedFunctorLambda(
            'bc',
            source,
            Q,
            bc => emdash.apply(
                GG,
                emdash.apply(rightProjection, bc)
            )
        );
        const expected = emdash.displayedProductPair(
            leftMapped,
            rightMapped
        );
        assert.equal(
            emdash.compare(mapped, expected, 12_000).status,
            'equal'
        );
        const point = emdash.apply(mapped, x, {
            expectedShape: 'fibre-functor'
        });
        assert.equal(
            emdash.compare(
                point,
                emdash.apply(expected, x, {
                    expectedShape: 'fibre-functor'
                }),
                12_000
            ).status,
            'equal'
        );
    });

    it('scales projection and pairing to three left-associated siblings', () => {
        const {
            emdash,
            B,
            C,
            D
        } = fixture();
        const target = emdash.displayedProduct(
            emdash.displayedProduct(D, B),
            C
        );
        const reordered = emdash.displayedContextLambda(
            [
                { name: 'b', family: B },
                { name: 'c', family: C },
                { name: 'd', family: D }
            ],
            target,
            ([b, c, d]) => emdash.fibrePair(
                emdash.fibrePair(d, b),
                c
            )
        );
        const evidence = emdash.inspect(reordered).abstractions.at(-1);
        assert.equal(
            evidence?.rule,
            'categorical.displayed-context-bracket'
        );
        if (
            evidence?.rule !==
                'categorical.displayed-context-bracket'
        ) {
            assert.fail('Missing three-sibling evidence');
        }
        assert.equal(evidence.contextSize, 3);
        assert.deepEqual(evidence.bindingNames, ['b', 'c', 'd']);
        assert.match(
            emdash.compile(reordered).explicitCore,
            /generic-category-composition/u
        );
    });

    it('preserves one-slot identity, eta, composition, and weakening', () => {
        const {
            emdash,
            B,
            D,
            R,
            FF,
            HH
        } = fixture();
        const identity = emdash.displayedContextLambda(
            [{ name: 'b', family: B }],
            B,
            ([b]) => b
        );
        const eta = emdash.displayedContextLambda(
            [{ name: 'b', family: B }],
            D,
            ([b]) => emdash.apply(FF, b)
        );
        const composition = emdash.displayedContextLambda(
            [{ name: 'b', family: B }],
            R,
            ([b]) => emdash.apply(
                HH,
                emdash.apply(FF, b)
            )
        );
        assert.equal(
            emdash.compare(
                identity,
                emdash.displayedFunctorLambda(
                    'b',
                    B,
                    B,
                    b => b
                )
            ).status,
            'equal'
        );
        assert.equal(emdash.compare(eta, FF).status, 'equal');
        assert.match(
            emdash.compile(composition).explicitCore,
            /generic-category-composition/u
        );

        const section = emdash.section('s', D);
        const weakening = emdash.displayedContextLambda(
            [{ name: 'b', family: B }],
            D,
            ([b]) => emdash.apply(section, emdash.indexOf(b))
        );
        assert.match(
            emdash.compile(weakening).explicitCore,
            /section-pullback/u
        );
    });

    it('rejects unavailable, empty, duplicate, cross-base, and wrong targets', () => {
        const legacy = new CoreCategoricalProgram();
        const legacyK = legacy.category('LegacyK');
        const legacyB = legacy.displayedFamily('LegacyB', legacyK);
        assert.throws(
            () => legacy.displayedContextLambda(
                [{ name: 'b', family: legacyB }],
                legacyB,
                ([b]) => b
            ),
            error =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'UNAVAILABLE_DISPLAYED_CONTEXT'
        );

        const {
            emdash,
            K,
            B,
            C
        } = fixture();
        assert.throws(
            () => emdash.displayedContextLambda(
                [],
                B,
                () => {
                    throw new Error('must not run');
                }
            ),
            error =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'INVALID_DISPLAYED_CONTEXT'
        );
        assert.throws(
            () => emdash.displayedContextLambda(
                [
                    { name: 'b', family: B },
                    { name: 'b', family: C }
                ],
                B,
                ([b]) => b
            ),
            error =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'INVALID_DISPLAYED_CONTEXT'
        );
        const L = emdash.category('L');
        const EL = emdash.displayedFamily('EL', L);
        assert.throws(
            () => emdash.displayedContextLambda(
                [
                    { name: 'b', family: B },
                    { name: 'e', family: EL }
                ],
                B,
                ([b]) => b
            ),
            error =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'DISPLAYED_BASE_MISMATCH'
        );
        const wrongTarget = emdash.displayedFamily('Wrong', K);
        assert.throws(
            () => emdash.displayedContextLambda(
                [{ name: 'b', family: B }],
                wrongTarget,
                ([b]) => b
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
        );
        assert.throws(
            () => emdash.contravariantCategoryFamily('G', K),
            error =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'UNAVAILABLE_DEPENDENT_TARGET'
        );

        const dependentTarget = new CoreCategoricalProgram({
            profile: 'fibred-dependent-target-1'
        });
        const dependentK = dependentTarget.category('DependentK');
        const dependentB =
            dependentTarget.displayedFamily('DependentB', dependentK);
        assert.throws(
            () => dependentTarget.displayedContextLambda(
                [{ name: 'b', family: dependentB }],
                dependentB,
                ([b]) => b
            ),
            error =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'UNAVAILABLE_DISPLAYED_CONTEXT'
        );
    });

    it('rejects escaped and foreign slots and non-context fibre pairs', () => {
        const {
            emdash,
            B
        } = fixture();
        let escaped: CoreCategoricalSlotToken | undefined;
        emdash.displayedContextLambda(
            [{ name: 'b', family: B }],
            B,
            ([b]) => {
                escaped = b;
                return b;
            }
        );
        assert.throws(
            () => emdash.fibrePair(
                escaped as CoreCategoricalSlotToken,
                escaped as CoreCategoricalSlotToken
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'ESCAPED_SLOT'
        );

        const foreign = new CoreCategoricalProgram({
            profile: 'fibred-displayed-bracket-1'
        });
        const FK = foreign.category('FK');
        const FB = foreign.displayedFamily('FB', FK);
        const foreignIdentity = foreign.displayedContextLambda(
            [{ name: 'fb', family: FB }],
            FB,
            ([fb]) => fb
        );
        assert.throws(
            () => emdash.displayedContextLambda(
                [{ name: 'b', family: B }],
                B,
                () => foreignIdentity
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'FOREIGN_TERM'
        );

        assert.throws(
            () => emdash.displayedContextLambda(
                [{ name: 'b', family: B }],
                B,
                ([b]) => {
                    const pointwiseCapture =
                        emdash.displayedFunctorLambda(
                            'a',
                            B,
                            B,
                            () => b
                        );
                    return emdash.apply(pointwiseCapture, b);
                }
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
        );
    });

    it('uses dependency evidence and rejects a genuine sibling edge', () => {
        const nodeProvenance = provenance(
            'surface',
            'dependent sibling request',
            sourceSpan('dependent-sibling.ts', 1, 1)
        );
        const probeBase = kernelFree(
            'ProbeK',
            nodeProvenance
        );
        const probeB = kernelFree(
            'ProbeB',
            nodeProvenance
        );
        const probeC = kernelFree(
            'ProbeC',
            nodeProvenance
        );
        assert.throws(
            () => planCoreCategoricalContextDependencies({
                slots: [
                    {
                        name: 'k',
                        classifier:
                            coreCategoricalClosedContextClassifier(
                                {
                                    tag: 'object',
                                    category: probeBase
                                },
                                nodeProvenance
                            ),
                        provenance: nodeProvenance
                    },
                    {
                        name: 'b',
                        classifier:
                            coreCategoricalDisplayedContextClassifier(
                                probeBase,
                                probeB,
                                [
                                    coreCategoricalContextSlotReference(
                                        0,
                                        nodeProvenance
                                    )
                                ],
                                {
                                    tag: 'indexed-object',
                                    baseCategory: probeBase,
                                    family: probeB,
                                    index: 0
                                },
                                nodeProvenance
                            ),
                        provenance: nodeProvenance
                    },
                    {
                        name: 'c',
                        classifier:
                            coreCategoricalDisplayedContextClassifier(
                                probeBase,
                                probeC,
                                [
                                    coreCategoricalContextSlotReference(
                                        0,
                                        nodeProvenance
                                    ),
                                    coreCategoricalContextSlotReference(
                                        1,
                                        nodeProvenance
                                    )
                                ],
                                {
                                    tag: 'indexed-object',
                                    baseCategory: probeBase,
                                    family: probeC,
                                    index: 1
                                },
                                nodeProvenance
                            ),
                        provenance: nodeProvenance
                    }
                ],
                siblingGroups: [{
                    positions: [1, 2],
                    provenance: nodeProvenance
                }]
            }),
            error =>
                error instanceof Error &&
                /depends on grouped slot/u.test(error.message)
        );
    });
});
