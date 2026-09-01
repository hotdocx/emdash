/** Live emitted-Core prerequisite for representable Freyd equality. */

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
    algebraPolynomialFreeModule,
    algebraPolynomialIdeal,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleVector,
    algebraPolynomialPresentationMorphismAdd,
    algebraPolynomialPresentationMorphismAgreement,
    algebraPolynomialPresentationMorphismCongruence,
    algebraPolynomialPresentationMorphismIdentity,
    algebraPolynomialPresentationMorphismNegate,
    algebraPolynomialPresentationMorphismZero,
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
    defineAlgebraFormalPresentationAgreementRealization,
    kernelFree,
    kernelUniverse,
    provenance,
    serializeCoreLfKernelProbe,
    sourceSpan
} from '../src/v3_2';

const because = (detail: string) => provenance('surface', detail);

describe('FRP live emitted-Core conformance', () => {
    it(
        'checks the agreement law consumed by the Freyd quotient path',
        { skip: process.env.EMDASH_RUN_PROOF_CAS_FREYD !== '1' },
        () => {
            const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
            const x = algebraPolynomialVariable(ring, 0);
            const zero = algebraPolynomialZero(ring);
            const ambient = algebraPolynomialFreeModule(ring, 1);
            const presentation = algebraPresentedPolynomialModule(
                algebraPolynomialSubmodule(ambient, [
                    algebraPolynomialModuleVector(ambient, [x])
                ])
            );
            const map = (value: typeof x) => algebraPolynomialModuleMap(
                ambient,
                ambient,
                [algebraPolynomialModuleVector(ambient, [value])]
            );
            const agreement = algebraPolynomialPresentationMorphismAgreement({
                source: presentation,
                target: presentation,
                left: map(x),
                right: map(zero)
            });
            const algebra = algebraPresentedAlgebra(
                algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, []))
            );
            const formalRing = kernelFree('formal_live_freyd_R', because('ring'));
            const formalX = kernelFree('formal_live_freyd_x', because('x'));
            const coefficients = new Map<string, ReturnType<typeof kernelFree>>();
            const reifier = defineAffineFormalPolynomialReifier({
                algebra,
                formalRing,
                generatorTerms: [formalX],
                coefficientReifier: coefficient => {
                    const text = RATIONAL_DOMAIN.text(coefficient);
                    let term = coefficients.get(text);
                    if (term === undefined) {
                        term = kernelFree(
                            `formal_live_freyd_coefficient_${text.replace('-', 'neg')}`,
                            because('coefficient')
                        );
                        coefficients.set(text, term);
                    }
                    return term;
                },
                status: 'trusted-computation'
            });
            const realization =
                defineAlgebraFormalPresentationAgreementRealization({
                    reifier,
                    selected: agreement
                });
            const identity = algebraPolynomialPresentationMorphismIdentity(
                presentation
            );
            const zeroMorphism = algebraPolynomialPresentationMorphismZero(
                presentation,
                presentation
            );
            const cancellation = algebraPolynomialPresentationMorphismAdd(
                identity,
                algebraPolynomialPresentationMorphismNegate(identity)
            );
            const cancellationAgreement =
                algebraPolynomialPresentationMorphismCongruence(
                    cancellation,
                    zeroMorphism
                );
            const cancellationRealization =
                defineAlgebraFormalPresentationAgreementRealization({
                    reifier,
                    selected: cancellationAgreement
                });
            const elementType = affineFormalRingElementType(formalRing);
            const environment = createFormalPresentationMorphismProofEnvironment([
                { name: formalRing.name, type: affineFormalCommRingType() },
                { name: formalX.name, type: elementType },
                ...[...coefficients.values()].map(term => ({
                    name: term.name,
                    type: elementType
                }))
            ]);
            const checker = createCoreProofChecker(environment);
            checker.validateEnvironment();
            const universe = kernelUniverse(because('law universe'));
            checker.check(checker.rootContext, realization.claimType, universe);
            checker.check(
                checker.rootContext,
                cancellationRealization.claimType,
                universe
            );
            const serialized = serializeCoreLfKernelProbe({
                environment,
                externalFreeReferences: {
                    ...AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS,
                    ...AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS,
                    ...AFFINE_FORMAL_FINITE_MODULE_BINDINGS,
                    ...AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS
                },
                assertions: [{
                    label: 'Freyd representable agreement prerequisite',
                    term: realization.claimType,
                    type: universe,
                    span: sourceSpan(
                        'generated/proof-cas-freyd.ts',
                        1,
                        1,
                        1,
                        2
                    )
                }, {
                    label: 'Freyd additive cancellation agreement',
                    term: cancellationRealization.claimType,
                    type: universe,
                    span: sourceSpan(
                        'generated/proof-cas-freyd.ts',
                        2,
                        1,
                        2,
                        2
                    )
                }]
            });
            const probe = {
                ...serialized,
                source: serialized.source.replace(
                    'require open emdash.emdash3_2;',
                        'require open ' +
                        'emdash.emdash3_2_commutative_algebra_' +
                        'freyd_preadditive_class_laws;'
                )
            };
            const checked = checkLambdapiProbe(probe, {
                packageRoot: resolve(__dirname, '..', 'emdash2'),
                timeoutMs: 60_000
            });
            assert.equal(checked.timedOut, false, checked.diagnostics);
            assert.equal(checked.accepted, true, checked.diagnostics);
            assert.equal(agreement.agrees, true);
            assert.equal(cancellationAgreement.agrees, true);
        }
    );
});
