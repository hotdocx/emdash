/** Live Lambdapi conformance for emitted complex and chain-map laws. */

import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    AFFINE_FORMAL_FINITE_MODULE_BINDINGS,
    AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS,
    AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS,
    AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS,
    RATIONAL_DOMAIN,
    affineFormalCommRingType,
    affineFormalRingElementType,
    algebraPolynomialBoundedChainMap,
    algebraPolynomialBoundedFreeComplex,
    algebraPolynomialFreeModule,
    algebraPolynomialIdeal,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleVector,
    algebraPolynomialQuotientRing,
    algebraPolynomialRing,
    algebraPolynomialVariable,
    algebraPolynomialZero,
    algebraPresentedAlgebra,
    checkLambdapiProbe,
    createCoreProofChecker,
    createFormalPresentationMorphismProofEnvironment,
    defineAffineFormalPolynomialReifier,
    defineAlgebraFormalBoundedChainMapRealization,
    defineAlgebraFormalBoundedComplexRealization,
    kernelFree,
    kernelUniverse,
    provenance,
    serializeCoreLfKernelProbe,
    sourceSpan
} from '../src/v3_2';

const because = (detail: string) => provenance('surface', detail);

describe('FBC live emitted-Core conformance', () => {
    it(
        'checks adjacent-zero and recursive chain-map laws in Lambdapi',
        { skip: process.env.EMDASH_RUN_PROOF_CAS_BOUNDED_COMPLEX !== '1' },
        () => {
            const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
            const x = algebraPolynomialVariable(ring, 0);
            const y = algebraPolynomialVariable(ring, 1);
            const zero = algebraPolynomialZero(ring);
            const module = algebraPolynomialFreeModule(ring, 1);
            const map = (value: typeof x) => algebraPolynomialModuleMap(
                module,
                module,
                [algebraPolynomialModuleVector(module, [value])]
            );
            const complex = algebraPolynomialBoundedFreeComplex({
                terms: [module, module, module],
                differentials: [map(x), map(zero)]
            });
            const chainMap = algebraPolynomialBoundedChainMap({
                source: complex,
                target: complex,
                components: [map(y), map(y), map(y)]
            });
            const algebra = algebraPresentedAlgebra(
                algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, []))
            );
            const formalRing = kernelFree('formal_live_complex_R', because('ring'));
            const formalX = kernelFree('formal_live_complex_x', because('x'));
            const formalY = kernelFree('formal_live_complex_y', because('y'));
            const coefficients = new Map<string, ReturnType<typeof kernelFree>>();
            const reifier = defineAffineFormalPolynomialReifier({
                algebra,
                formalRing,
                generatorTerms: [formalX, formalY],
                coefficientReifier: coefficient => {
                    const text = RATIONAL_DOMAIN.text(coefficient);
                    let term = coefficients.get(text);
                    if (term === undefined) {
                        term = kernelFree(
                            `formal_live_complex_coefficient_${text.replace('-', 'neg')}`,
                            because('coefficient')
                        );
                        coefficients.set(text, term);
                    }
                    return term;
                },
                status: 'trusted-computation'
            });
            const formalComplex = defineAlgebraFormalBoundedComplexRealization({
                reifier,
                selected: complex
            });
            const formalMap = defineAlgebraFormalBoundedChainMapRealization({
                reifier,
                selected: chainMap
            });
            const claims = [
                ...formalComplex.conditions.map(condition => condition.claimType),
                ...formalMap.squares.map(square => square.claimType)
            ];
            const elementType = affineFormalRingElementType(formalRing);
            const environment = createFormalPresentationMorphismProofEnvironment([
                { name: formalRing.name, type: affineFormalCommRingType() },
                { name: formalX.name, type: elementType },
                { name: formalY.name, type: elementType },
                ...[...coefficients.values()].map(term => ({
                    name: term.name,
                    type: elementType
                }))
            ]);
            const checker = createCoreProofChecker(environment);
            checker.validateEnvironment();
            const universe = kernelUniverse(because('law universe'));
            claims.forEach(claim => checker.check(
                checker.rootContext,
                claim,
                universe
            ));
            const serialized = serializeCoreLfKernelProbe({
                environment,
                externalFreeReferences: {
                    ...AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS,
                    ...AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS,
                    ...AFFINE_FORMAL_FINITE_MODULE_BINDINGS,
                    ...AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS
                },
                assertions: claims.map((term, index) => ({
                    label: index === 0
                        ? 'bounded complex adjacent-zero law'
                        : `bounded chain-map square ${index}`,
                    term,
                    type: universe,
                    span: sourceSpan(
                        'generated/proof-cas-bounded-complex.ts',
                        index + 1,
                        1,
                        index + 1,
                        2
                    )
                }))
            });
            const probe = {
                ...serialized,
                source: serialized.source.replace(
                    'require open emdash.emdash3_2;',
                    'require open ' +
                        'emdash.emdash3_2_commutative_algebra_' +
                        'bounded_free_chain_maps;'
                )
            };
            const checked = checkLambdapiProbe(probe, {
                packageRoot: resolve(__dirname, '..', 'emdash2'),
                timeoutMs: 60_000
            });
            assert.equal(checked.timedOut, false, checked.diagnostics);
            assert.equal(checked.accepted, true, checked.diagnostics);
        }
    );
});
