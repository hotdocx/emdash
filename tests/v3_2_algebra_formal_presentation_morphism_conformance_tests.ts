/** Live Lambdapi conformance for emitted presentation-morphism equations. */

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
    algebraPolynomialChainMapSquare,
    algebraPolynomialFreeModule,
    algebraPolynomialIdeal,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleVector,
    algebraPolynomialPresentationMorphism,
    algebraPolynomialPresentationMorphismAgreement,
    algebraPolynomialQuotientRing,
    algebraPolynomialRing,
    algebraPolynomialSubmodule,
    algebraPolynomialVariable,
    algebraPolynomialZero,
    algebraPresentedAlgebra,
    algebraPresentedPolynomialModule,
    checkLambdapiProbe,
    createCoreProofChecker,
    createFormalPresentationMorphismProofEnvironment,
    defineAffineFormalPolynomialReifier,
    defineAlgebraFormalChainMapSquareRealization,
    defineAlgebraFormalPresentationAgreementRealization,
    defineAlgebraFormalPresentationMorphismRealization,
    kernelFree,
    kernelUniverse,
    provenance,
    serializeCoreLfKernelProbe,
    sourceSpan
} from '../src/v3_2';

const because = (detail: string) => provenance('surface', detail);

describe('FPMAP live emitted-Core conformance', () => {
    it(
        'checks morphism, agreement, and chain equations in Lambdapi',
        {
            skip: process.env.EMDASH_RUN_PROOF_CAS_PRESENTATION_MORPHISM !== '1'
        },
        () => {
            const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
            const x = algebraPolynomialVariable(ring, 0);
            const y = algebraPolynomialVariable(ring, 1);
            const zero = algebraPolynomialZero(ring);
            const ambient = algebraPolynomialFreeModule(ring, 1);
            const presentation = algebraPresentedPolynomialModule(
                algebraPolynomialSubmodule(ambient, [
                    algebraPolynomialModuleVector(ambient, [x])
                ])
            );
            const map = (polynomial: typeof x) => algebraPolynomialModuleMap(
                ambient,
                ambient,
                [algebraPolynomialModuleVector(ambient, [polynomial])]
            );
            const morphism = algebraPolynomialPresentationMorphism({
                source: presentation,
                target: presentation,
                map: map(y)
            });
            const agreement = algebraPolynomialPresentationMorphismAgreement({
                source: presentation,
                target: presentation,
                left: map(x),
                right: map(zero)
            });
            const chain = algebraPolynomialChainMapSquare({
                differentialSource: map(x),
                differentialTarget: map(x),
                componentPrevious: map(y),
                componentNow: map(y)
            });
            const algebra = algebraPresentedAlgebra(
                algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, []))
            );
            const formalRing = kernelFree('formal_live_map_R', because('ring'));
            const formalX = kernelFree('formal_live_map_x', because('x'));
            const formalY = kernelFree('formal_live_map_y', because('y'));
            const coefficients = new Map<string, ReturnType<typeof kernelFree>>();
            const reifier = defineAffineFormalPolynomialReifier({
                algebra,
                formalRing,
                generatorTerms: [formalX, formalY],
                coefficientReifier: coefficient => {
                    const text = RATIONAL_DOMAIN.text(coefficient);
                    let term = coefficients.get(text);
                    if (term === undefined) {
                        const suffix = [...text].map(character =>
                            character.codePointAt(0)!.toString(16)
                        ).join('_');
                        term = kernelFree(
                            `formal_live_map_coefficient_${suffix}`,
                            because('coefficient')
                        );
                        coefficients.set(text, term);
                    }
                    return term;
                },
                status: 'trusted-computation'
            });
            const claims = [
                defineAlgebraFormalPresentationMorphismRealization({
                    reifier,
                    selected: morphism
                }).claimType,
                defineAlgebraFormalPresentationAgreementRealization({
                    reifier,
                    selected: agreement
                }).claimType,
                defineAlgebraFormalChainMapSquareRealization({
                    reifier,
                    selected: chain
                }).claimType
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
            const universe = kernelUniverse(because('claim universe'));
            claims.forEach(claim => checker.check(
                checker.rootContext,
                claim,
                universe
            ));
            const labels = [
                'presentation morphism law',
                'presentation representative agreement',
                'chain map square'
            ];
            const serialized = serializeCoreLfKernelProbe({
                environment,
                externalFreeReferences: {
                    ...AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS,
                    ...AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS,
                    ...AFFINE_FORMAL_FINITE_MODULE_BINDINGS,
                    ...AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS
                },
                assertions: claims.map((term, index) => ({
                    label: labels[index],
                    term,
                    type: universe,
                    span: sourceSpan(
                        'generated/proof-cas-presentation-morphism.ts',
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
                        'emdash.emdash3_2_commutative_algebra_presentations;'
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
