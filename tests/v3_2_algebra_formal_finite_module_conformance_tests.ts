/** Live Lambdapi conformance for emitted finite-module Core targets. */

import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    AFFINE_FORMAL_FINITE_MODULE_BINDINGS,
    AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS,
    AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS,
    RATIONAL_DOMAIN,
    affineFormalCommRingType,
    affineFormalRingElementType,
    algebraFormalCompositeZeroClaimType,
    algebraFormalSyzygyClaimType,
    algebraPolynomialFreeModule,
    algebraPolynomialIdeal,
    algebraPolynomialModuleGroebnerBasis,
    algebraPolynomialModuleMembership,
    algebraPolynomialModuleSchreyerSyzygies,
    algebraPolynomialModuleVector,
    algebraPolynomialQuotientRing,
    algebraPolynomialRing,
    algebraPolynomialSchreyerResolution,
    algebraPolynomialSubmodule,
    algebraPolynomialVariable,
    algebraPolynomialZero,
    algebraPresentedAlgebra,
    algebraPresentedPolynomialModule,
    checkLambdapiProbe,
    createCoreProofChecker,
    createFormalFiniteModuleProofEnvironment,
    defineAffineFormalPolynomialReifier,
    defineAlgebraFormalModuleMembershipRealization,
    kernelFree,
    kernelUniverse,
    provenance,
    serializeCoreLfKernelProbe,
    sourceSpan
} from '../src/v3_2';

const because = (detail: string) => provenance('surface', detail);

describe('FPM-CONFORMANCE emitted finite-module targets', () => {
    it(
        'passes bounded Lambdapi checking for membership and chain equations',
        {
            skip: process.env.EMDASH_RUN_PROOF_CAS_FINITE_MODULE !== '1'
        },
        () => {
            const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
            const x = algebraPolynomialVariable(ring, 0);
            const y = algebraPolynomialVariable(ring, 1);
            const zero = algebraPolynomialZero(ring);
            const ambient = algebraPolynomialFreeModule(
                ring,
                2,
                'position-over-term'
            );
            const relations = algebraPolynomialSubmodule(ambient, [
                algebraPolynomialModuleVector(ambient, [x, y]),
                algebraPolynomialModuleVector(ambient, [y, zero])
            ]);
            const basis = algebraPolynomialModuleGroebnerBasis(relations);
            const membership = algebraPolynomialModuleMembership(
                relations.generators[0],
                basis
            );
            const syzygies = algebraPolynomialModuleSchreyerSyzygies(basis);
            const resolution = algebraPolynomialSchreyerResolution(
                algebraPresentedPolynomialModule(relations),
                4
            );
            const algebra = algebraPresentedAlgebra(
                algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, []))
            );
            const formalRing = kernelFree('formal_live_R', because('ring'));
            const formalX = kernelFree('formal_live_x', because('x'));
            const formalY = kernelFree('formal_live_y', because('y'));
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
                            `formal_live_coefficient_${suffix}`,
                            because('coefficient')
                        );
                        coefficients.set(text, term);
                    }
                    return term;
                },
                status: 'trusted-computation'
            });
            const membershipClaim =
                defineAlgebraFormalModuleMembershipRealization({
                    reifier,
                    vector: relations.generators[0],
                    basis,
                    selected: membership
                }).claimType;
            const syzygyClaim = algebraFormalSyzygyClaimType({
                reifier,
                generators: basis.basis,
                syzygy: syzygies.generators[0]
            });
            const compositeClaim = algebraFormalCompositeZeroClaimType({
                reifier,
                left: resolution.differentials[0],
                right: resolution.differentials[1]
            });
            const elementType = affineFormalRingElementType(formalRing);
            const environment = createFormalFiniteModuleProofEnvironment([
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
            [membershipClaim, syzygyClaim, compositeClaim].forEach(claim =>
                checker.check(checker.rootContext, claim, universe)
            );
            const claims = [
                ['module membership equation', membershipClaim],
                ['Schreyer syzygy equation', syzygyClaim],
                ['adjacent differential equation', compositeClaim]
            ] as const;
            const serialized = serializeCoreLfKernelProbe({
                environment,
                externalFreeReferences: {
                    ...AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS,
                    ...AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS,
                    ...AFFINE_FORMAL_FINITE_MODULE_BINDINGS
                },
                assertions: claims.map(([label, term], index) => ({
                    label,
                    term,
                    type: universe,
                    span: sourceSpan(
                        'generated/proof-cas-finite-module.ts',
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
                        'emdash.emdash3_2_commutative_algebra_finite_modules;'
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
