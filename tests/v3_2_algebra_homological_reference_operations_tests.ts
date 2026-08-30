/** Focused CAS-HOMOLOGICAL-7A6 native-operation and graph tests. */

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
    algebraModuleRealization,
    algebraPresentedModule
} from '../src/v3_2/algebra_module';
import {
    algebraModuleChainComplex,
    algebraModuleChainMap,
    algebraModuleChainMapIdentity,
    algebraModuleShortExactSequence
} from '../src/v3_2/algebra_homological';
import {
    algebraModuleAsGeneralizedSpan,
    algebraModuleGeneralizedSpanHonestRepresentative
} from '../src/v3_2/algebra_generalized';
import {
    algebraModulePresentationResolution
} from '../src/v3_2/algebra_resolution';
import {
    ALGEBRA_HOMOLOGICAL_REFERENCE_OPERATIONS_PROFILE,
    algebraHomologicalReferenceOperations
} from '../src/v3_2/algebra_homological_reference_operations';
import {
    computeAlgebraOperation
} from '../src/v3_2/algebra_engine';
import {
    createAlgebraComputationGraphBuilder,
    executeAlgebraComputationGraph
} from '../src/v3_2/algebra_graph';
import {
    createAlgebraTypeScriptReferenceEngine
} from '../src/v3_2/algebra_reference_engine';

const zeroWitness = () => algebraZeroMatrix(algebraMatrixSpace(
    RATIONAL_DOMAIN,
    0,
    0
));

const exactSequenceFixture = () => {
    const zero = algebraFreeModule(RATIONAL_DOMAIN, 0);
    const one = algebraFreeModule(RATIONAL_DOMAIN, 1);
    const zeroToOne = algebraModuleMorphism(
        zero,
        one,
        algebraZeroMatrix(algebraMatrixSpace(RATIONAL_DOMAIN, 1, 0)),
        zeroWitness()
    );
    const oneToZero = algebraModuleMorphism(
        one,
        zero,
        algebraZeroMatrix(algebraMatrixSpace(RATIONAL_DOMAIN, 0, 1)),
        zeroWitness()
    );
    const identity = algebraModuleIdentity(one);
    const subcomplex = algebraModuleChainComplex(
        RATIONAL_DOMAIN,
        [{ degree: 0, object: one }, { degree: 1, object: zero }],
        [{ degree: 1, morphism: zeroToOne }]
    );
    const middle = algebraModuleChainComplex(
        RATIONAL_DOMAIN,
        [{ degree: 0, object: one }, { degree: 1, object: one }],
        [{ degree: 1, morphism: identity }]
    );
    const quotient = algebraModuleChainComplex(
        RATIONAL_DOMAIN,
        [{ degree: 0, object: zero }, { degree: 1, object: one }],
        [{ degree: 1, morphism: oneToZero }]
    );
    return algebraModuleShortExactSequence(
        algebraModuleChainMap(subcomplex, middle, [
            { degree: 0, morphism: identity },
            { degree: 1, morphism: zeroToOne }
        ]),
        algebraModuleChainMap(middle, quotient, [
            { degree: 0, morphism: oneToZero },
            { degree: 1, morphism: identity }
        ])
    );
};

describe('v3.2 native homological operations and graphs', () => {
    it('executes whole homology and presentation resolution as graph nodes', async () => {
        const operations = algebraHomologicalReferenceOperations(
            RATIONAL_DOMAIN
        );
        const engine = createAlgebraTypeScriptReferenceEngine({
            implementations: operations.implementations
        });
        const module = algebraPresentedModule(
            RATIONAL_DOMAIN,
            2,
            algebraMatrix(
                algebraMatrixSpace(RATIONAL_DOMAIN, 2, 2),
                [['1', '2'], ['0', '0']]
            )
        );
        const directResolution = algebraModulePresentationResolution(module);
        const homologyBuilder = createAlgebraComputationGraphBuilder(
            'fixture.homological.homology',
            'v1'
        );
        const homologyInput = homologyBuilder.input(
            'input',
            operations.homology.input
        );
        const homology = homologyBuilder.operation(
            'homology',
            operations.homology,
            homologyInput
        );
        const homologyExecution = await executeAlgebraComputationGraph({
            graph: homologyBuilder.build([{ id: 'result', value: homology }]),
            engine,
            inputs: [{
                id: 'input',
                value: { complex: directResolution.complex, degree: 0 }
            }]
        });
        assert.equal(
            algebraModuleRealization(
                (homologyExecution.outputs[0].value as
                    typeof directResolution.homology[0]).object
            ).dimension,
            1
        );

        const resolutionBuilder = createAlgebraComputationGraphBuilder(
            'fixture.homological.resolution',
            'v1'
        );
        const moduleInput = resolutionBuilder.input(
            'module',
            operations.presentationResolution.input
        );
        const resolution = resolutionBuilder.operation(
            'resolution',
            operations.presentationResolution,
            moduleInput
        );
        const resolutionExecution = await executeAlgebraComputationGraph({
            graph: resolutionBuilder.build([{ id: 'result', value: resolution }]),
            engine,
            inputs: [{ id: 'module', value: module }]
        });
        assert.equal(
            (resolutionExecution.outputs[0].value as typeof directResolution)
                .projectiveLength,
            2
        );
        assert.equal(
            ALGEBRA_HOMOLOGICAL_REFERENCE_OPERATIONS_PROFILE.wholeResults,
            true
        );
    });

    it('executes functorial homology and generalized-span composition', async () => {
        const operations = algebraHomologicalReferenceOperations(
            RATIONAL_DOMAIN
        );
        const engine = createAlgebraTypeScriptReferenceEngine({
            implementations: operations.implementations
        });
        const module = algebraFreeModule(RATIONAL_DOMAIN, 1);
        const complex = algebraModuleChainComplex(
            RATIONAL_DOMAIN,
            [{ degree: 0, object: module }],
            []
        );
        const functorial = await computeAlgebraOperation({
            engine,
            operation: operations.functorialHomology,
            input: {
                chainMap: algebraModuleChainMapIdentity(complex),
                degree: 0
            }
        });
        assert.ok(algebraModuleMorphismEquivalent(
            functorial.value.morphism,
            algebraModuleIdentity(functorial.value.sourceHomology.object)
        ));

        const first = algebraModuleMorphism(
            module,
            module,
            algebraMatrix(
                algebraMatrixSpace(RATIONAL_DOMAIN, 1, 1),
                [['2']]
            ),
            zeroWitness()
        );
        const second = algebraModuleMorphism(
            module,
            module,
            algebraMatrix(
                algebraMatrixSpace(RATIONAL_DOMAIN, 1, 1),
                [['3']]
            ),
            zeroWitness()
        );
        const composition = await computeAlgebraOperation({
            engine,
            operation: operations.generalizedSpanComposition,
            input: {
                after: algebraModuleAsGeneralizedSpan(second),
                before: algebraModuleAsGeneralizedSpan(first)
            }
        });
        assert.ok(algebraModuleMorphismEquivalent(
            algebraModuleGeneralizedSpanHonestRepresentative(
                composition.value.result
            ),
            algebraModuleCompose(second, first)
        ));
    });

    it('executes the whole connecting map and split resolution natively', async () => {
        const operations = algebraHomologicalReferenceOperations(
            RATIONAL_DOMAIN
        );
        const engine = createAlgebraTypeScriptReferenceEngine({
            implementations: operations.implementations
        });
        const connecting = await computeAlgebraOperation({
            engine,
            operation: operations.connectingMorphism,
            input: { sequence: exactSequenceFixture(), degree: 1 }
        });
        assert.equal(
            RATIONAL_DOMAIN.text(
                algebraModuleInducedMatrix(
                    connecting.value.morphism
                ).entries[0][0]
            ),
            '1'
        );
        const split = await computeAlgebraOperation({
            engine,
            operation: operations.splitResolution,
            input: algebraPresentedModule(
                RATIONAL_DOMAIN,
                2,
                algebraMatrix(
                    algebraMatrixSpace(RATIONAL_DOMAIN, 2, 1),
                    [['1'], ['0']]
                )
            )
        });
        assert.equal(split.value.projectiveLength, 0);
    });
});
