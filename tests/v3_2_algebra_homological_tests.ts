/** Focused CAS-HOMOLOGICAL-7A bounded-complex and homology tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import {
    algebraMatrix,
    algebraMatrixSpace,
    algebraZeroMatrix
} from '../src/v3_2/algebra_matrix';
import {
    algebraFreeModule,
    algebraModuleCompose,
    algebraModuleIdentity,
    algebraModuleInducedMatrix,
    algebraModuleMorphism,
    algebraModuleMorphismEquivalent,
    algebraModuleMorphismIsZero,
    algebraModuleRealization
} from '../src/v3_2/algebra_module';
import {
    ALGEBRA_HOMOLOGICAL_PROFILE,
    AlgebraHomologicalError,
    algebraModuleChainMap,
    algebraModuleChainMapComponentAt,
    algebraModuleChainMapCompose,
    algebraModuleChainMapHomology,
    algebraModuleChainMapIdentity,
    algebraModuleConnectingMorphism,
    algebraModuleChainComplex,
    algebraModuleChainComplexDifferential,
    algebraModuleChainComplexHomology,
    algebraModuleChainComplexTerm,
    algebraModuleHomology,
    algebraModuleShortExactSequence
} from '../src/v3_2/algebra_homological';

const homologicalError = (code: AlgebraHomologicalError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraHomologicalError);
        assert.equal(error.code, code);
        return true;
    };

const zeroWitness = () => algebraZeroMatrix(algebraMatrixSpace(
    RATIONAL_DOMAIN,
    0,
    0
));

const complexFixture = () => {
    const c0 = algebraFreeModule(RATIONAL_DOMAIN, 1);
    const c1 = algebraFreeModule(RATIONAL_DOMAIN, 2);
    const c2 = algebraFreeModule(RATIONAL_DOMAIN, 1);
    const d1 = algebraModuleMorphism(
        c1,
        c0,
        algebraMatrix(
            algebraMatrixSpace(RATIONAL_DOMAIN, 1, 2),
            [['0', '0']]
        ),
        zeroWitness()
    );
    const d2 = algebraModuleMorphism(
        c2,
        c1,
        algebraMatrix(
            algebraMatrixSpace(RATIONAL_DOMAIN, 2, 1),
            [['1'], ['0']]
        ),
        zeroWitness()
    );
    const complex = algebraModuleChainComplex(
        RATIONAL_DOMAIN,
        [
            { degree: 2, object: c2 },
            { degree: 0, object: c0 },
            { degree: 1, object: c1 }
        ],
        [
            { degree: 2, morphism: d2 },
            { degree: 1, morphism: d1 }
        ]
    );
    return { c0, c1, c2, d1, d2, complex };
};

const scalarChainMap = (
    complex: ReturnType<typeof complexFixture>['complex'],
    scalar: string
) => algebraModuleChainMap(
    complex,
    complex,
    complex.terms.map(term => ({
        degree: term.degree,
        morphism: algebraModuleMorphism(
            term.object,
            term.object,
            algebraMatrix(
                algebraMatrixSpace(
                    RATIONAL_DOMAIN,
                    term.object.generators,
                    term.object.generators
                ),
                Array.from(
                    { length: term.object.generators },
                    (_, row) => Array.from(
                        { length: term.object.generators },
                        (_, column) => row === column ? scalar : '0'
                    )
                )
            ),
            zeroWitness()
        )
    }))
);

const shortExactComplexFixture = () => {
    const zero = algebraFreeModule(RATIONAL_DOMAIN, 0);
    const one = algebraFreeModule(RATIONAL_DOMAIN, 1);
    const zeroFromZeroToOne = algebraModuleMorphism(
        zero,
        one,
        algebraZeroMatrix(algebraMatrixSpace(RATIONAL_DOMAIN, 1, 0)),
        zeroWitness()
    );
    const zeroFromOneToZero = algebraModuleMorphism(
        one,
        zero,
        algebraZeroMatrix(algebraMatrixSpace(RATIONAL_DOMAIN, 0, 1)),
        zeroWitness()
    );
    const identity = algebraModuleIdentity(one);
    const subcomplex = algebraModuleChainComplex(
        RATIONAL_DOMAIN,
        [{ degree: 0, object: one }, { degree: 1, object: zero }],
        [{ degree: 1, morphism: zeroFromZeroToOne }]
    );
    const middle = algebraModuleChainComplex(
        RATIONAL_DOMAIN,
        [{ degree: 0, object: one }, { degree: 1, object: one }],
        [{ degree: 1, morphism: identity }]
    );
    const quotient = algebraModuleChainComplex(
        RATIONAL_DOMAIN,
        [{ degree: 0, object: zero }, { degree: 1, object: one }],
        [{ degree: 1, morphism: zeroFromOneToZero }]
    );
    const inclusion = algebraModuleChainMap(
        subcomplex,
        middle,
        [
            { degree: 0, morphism: identity },
            { degree: 1, morphism: zeroFromZeroToOne }
        ]
    );
    const projection = algebraModuleChainMap(
        middle,
        quotient,
        [
            { degree: 0, morphism: zeroFromOneToZero },
            { degree: 1, morphism: identity }
        ]
    );
    const sequence = algebraModuleShortExactSequence(inclusion, projection);
    return {
        zero,
        one,
        subcomplex,
        middle,
        quotient,
        inclusion,
        projection,
        sequence
    };
};

describe('v3.2 bounded field-module complexes and homology', () => {
    it('constructs a bounded complex and computes whole homology in every degree', () => {
        const { c1, d1, d2, complex } = complexFixture();
        assert.equal(complex.minimumDegree, 0);
        assert.equal(complex.maximumDegree, 2);
        assert.deepEqual(complex.terms.map(term => term.degree), [0, 1, 2]);
        assert.equal(algebraModuleChainComplexTerm(complex, 1), c1);
        assert.equal(algebraModuleChainComplexDifferential(complex, 2), d2);
        assert.equal(
            ALGEBRA_HOMOLOGICAL_PROFILE.differentialOrientation,
            'd_n-from-C_n-to-C_n-minus-1'
        );

        const h0 = algebraModuleChainComplexHomology(complex, 0);
        const h1 = algebraModuleChainComplexHomology(complex, 1);
        const h2 = algebraModuleChainComplexHomology(complex, 2);
        assert.equal(algebraModuleRealization(h0.object).dimension, 1);
        assert.equal(algebraModuleRealization(h1.object).dimension, 1);
        assert.equal(algebraModuleRealization(h2.object).dimension, 0);
        assert.ok(algebraModuleMorphismEquivalent(
            algebraModuleCompose(h1.cycles.inclusion, h1.boundaryLift),
            d2
        ));
        assert.ok(algebraModuleMorphismIsZero(algebraModuleCompose(d1, d2)));
        assert.equal(h1.quotient.object, h1.object);
        assert.equal(h1.degree, 1);
        assert.ok(Object.isFrozen(complex));
        assert.ok(Object.isFrozen(h1));
    });

    it('exposes homology of a composable zero pair as a whole construction', () => {
        const { d1, d2 } = complexFixture();
        const homology = algebraModuleHomology(d2, d1);
        assert.equal(homology.incoming, d2);
        assert.equal(homology.outgoing, d1);
        assert.equal(algebraModuleRealization(homology.object).dimension, 1);
        assert.ok(algebraModuleMorphismEquivalent(
            algebraModuleCompose(
                homology.cycles.inclusion,
                homology.boundaryLift
            ),
            d2
        ));
    });

    it('validates chain maps and descends their components to homology', () => {
        const { complex } = complexFixture();
        const twice = scalarChainMap(complex, '2');
        const induced = algebraModuleChainMapHomology(twice, 1);
        assert.equal(
            RATIONAL_DOMAIN.text(
                algebraModuleInducedMatrix(induced.morphism).entries[0][0]
            ),
            '2'
        );
        const component = algebraModuleChainMapComponentAt(twice, 1);
        assert.ok(algebraModuleMorphismEquivalent(
            algebraModuleCompose(
                induced.targetHomology.cycles.inclusion,
                induced.cycleMap
            ),
            algebraModuleCompose(
                component,
                induced.sourceHomology.cycles.inclusion
            )
        ));
        assert.ok(algebraModuleMorphismEquivalent(
            algebraModuleCompose(
                induced.morphism,
                induced.sourceHomology.quotient.projection
            ),
            algebraModuleCompose(
                induced.targetHomology.quotient.projection,
                induced.cycleMap
            )
        ));
        const identity = algebraModuleChainMapHomology(
            algebraModuleChainMapIdentity(complex),
            1
        );
        assert.ok(algebraModuleMorphismEquivalent(
            identity.morphism,
            algebraModuleIdentity(identity.sourceHomology.object)
        ));
    });

    it('preserves chain-map composition on computed homology', () => {
        const { complex } = complexFixture();
        const twice = scalarChainMap(complex, '2');
        const thrice = scalarChainMap(complex, '3');
        const composite = algebraModuleChainMapCompose(thrice, twice);
        const inducedTwice = algebraModuleChainMapHomology(twice, 1);
        const inducedThrice = algebraModuleChainMapHomology(thrice, 1);
        const inducedComposite = algebraModuleChainMapHomology(composite, 1);
        assert.equal(
            RATIONAL_DOMAIN.text(
                algebraModuleInducedMatrix(
                    inducedComposite.morphism
                ).entries[0][0]
            ),
            '6'
        );
        assert.ok(algebraModuleMorphismEquivalent(
            inducedComposite.morphism,
            algebraModuleCompose(
                inducedThrice.morphism,
                inducedTwice.morphism
            )
        ));
    });

    it('computes the connecting morphism of a short exact sequence', () => {
        const { sequence } = shortExactComplexFixture();
        const connecting = algebraModuleConnectingMorphism(sequence, 1);
        assert.equal(
            RATIONAL_DOMAIN.text(
                algebraModuleInducedMatrix(connecting.morphism).entries[0][0]
            ),
            '1'
        );
        const projection = sequence.projection.components[1].morphism;
        assert.ok(algebraModuleMorphismEquivalent(
            algebraModuleCompose(
                projection,
                connecting.liftedCyclesToMiddle
            ),
            connecting.sourceHomology.cycles.inclusion
        ));
        const inclusion = sequence.inclusion.components[0].morphism;
        assert.ok(algebraModuleMorphismEquivalent(
            algebraModuleCompose(
                sequence.degrees[0].projectionKernel.inclusion,
                connecting.boundaryInProjectionKernel
            ),
            connecting.middleBoundary
        ));
        assert.ok(algebraModuleMorphismEquivalent(
            algebraModuleCompose(
                inclusion,
                connecting.liftedBoundaryToSubcomplex
            ),
            connecting.middleBoundary
        ));
        assert.ok(algebraModuleMorphismEquivalent(
            algebraModuleCompose(
                connecting.targetHomology.cycles.inclusion,
                connecting.cycleMap
            ),
            connecting.liftedBoundaryToSubcomplex
        ));
        assert.ok(algebraModuleMorphismEquivalent(
            algebraModuleCompose(
                connecting.morphism,
                connecting.sourceHomology.quotient.projection
            ),
            algebraModuleCompose(
                connecting.targetHomology.quotient.projection,
                connecting.cycleMap
            )
        ));
        assert.ok(Object.isFrozen(sequence));
        assert.ok(Object.isFrozen(connecting));
    });

    it('rejects a degreewise sequence that is not short exact', () => {
        const fixture = shortExactComplexFixture();
        const badInclusion = algebraModuleChainMap(
            fixture.subcomplex,
            fixture.middle,
            [
                {
                    degree: 0,
                    morphism: algebraModuleMorphism(
                        fixture.one,
                        fixture.one,
                        algebraZeroMatrix(algebraMatrixSpace(
                            RATIONAL_DOMAIN,
                            1,
                            1
                        )),
                        zeroWitness()
                    )
                },
                {
                    degree: 1,
                    morphism: algebraModuleMorphism(
                        fixture.zero,
                        fixture.one,
                        algebraZeroMatrix(algebraMatrixSpace(
                            RATIONAL_DOMAIN,
                            1,
                            0
                        )),
                        zeroWitness()
                    )
                }
            ]
        );
        assert.throws(
            () => algebraModuleShortExactSequence(
                badInclusion,
                fixture.projection
            ),
            homologicalError('SHORT_EXACTNESS_FAILED')
        );
        assert.throws(
            () => algebraModuleConnectingMorphism(fixture.sequence, 0),
            homologicalError('DEGREE_OUT_OF_RANGE')
        );
    });

    it('rejects malformed bounds, endpoints, chain laws, and queried degrees', () => {
        const { c0, c1, c2, d1, d2, complex } = complexFixture();
        assert.throws(
            () => algebraModuleChainComplex(
                RATIONAL_DOMAIN,
                [{ degree: 0, object: c0 }, { degree: 2, object: c2 }],
                [{ degree: 2, morphism: d2 }]
            ),
            homologicalError('NON_CONSECUTIVE_DEGREES')
        );
        assert.throws(
            () => algebraModuleChainComplex(
                RATIONAL_DOMAIN,
                [{ degree: 0, object: c0 }, { degree: 0, object: c0 }],
                [{ degree: 1, morphism: d1 }]
            ),
            homologicalError('DUPLICATE_DEGREE')
        );
        const badD1 = algebraModuleMorphism(
            c1,
            c0,
            algebraMatrix(
                algebraMatrixSpace(RATIONAL_DOMAIN, 1, 2),
                [['1', '0']]
            ),
            zeroWitness()
        );
        assert.throws(
            () => algebraModuleChainComplex(
                RATIONAL_DOMAIN,
                [
                    { degree: 0, object: c0 },
                    { degree: 1, object: c1 },
                    { degree: 2, object: c2 }
                ],
                [
                    { degree: 1, morphism: badD1 },
                    { degree: 2, morphism: d2 }
                ]
            ),
            homologicalError('CHAIN_CONDITION_FAILED')
        );
        assert.throws(
            () => algebraModuleHomology(d2, badD1),
            homologicalError('CHAIN_CONDITION_FAILED')
        );
        assert.throws(
            () => algebraModuleChainComplexTerm(complex, 3),
            homologicalError('DEGREE_OUT_OF_RANGE')
        );
        assert.throws(
            () => algebraModuleChainComplexDifferential(complex, 0),
            homologicalError('DEGREE_OUT_OF_RANGE')
        );
        assert.throws(
            () => algebraModuleChainMap(
                complex,
                complex,
                [
                    {
                        degree: 0,
                        morphism: algebraModuleIdentity(c0)
                    },
                    {
                        degree: 1,
                        morphism: algebraModuleMorphism(
                            c1,
                            c1,
                            algebraMatrix(
                                algebraMatrixSpace(RATIONAL_DOMAIN, 2, 2),
                                [['2', '0'], ['0', '1']]
                            ),
                            zeroWitness()
                        )
                    },
                    {
                        degree: 2,
                        morphism: algebraModuleIdentity(c2)
                    }
                ]
            ),
            homologicalError('CHAIN_MAP_CONDITION_FAILED')
        );
        assert.throws(
            () => algebraModuleChainMapComponentAt(
                algebraModuleChainMapIdentity(complex),
                -1
            ),
            homologicalError('DEGREE_OUT_OF_RANGE')
        );
    });
});
