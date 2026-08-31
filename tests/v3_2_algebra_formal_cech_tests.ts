/** Focused BRIDGE-CECH-5A packed degreewise formal-presentation tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { kernelFree, provenance } from '../src/v3_2/kernel';
import { serializeCoreExpression } from '../src/v3_2/core_serialization';
import { serializeKernelExpression } from '../src/v3_2/lambdapi';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import { algebraPolynomialIdeal } from '../src/v3_2/algebra_ideal';
import {
    algebraPolynomialOne,
    algebraPolynomialRing,
    algebraPolynomialSubtract,
    algebraPolynomialVariable
} from '../src/v3_2/algebra_polynomial';
import {
    algebraPolynomialQuotientRing,
    algebraQuotientElement
} from '../src/v3_2/algebra_quotient';
import { algebraPresentedAlgebra } from '../src/v3_2/algebra_presented_algebra';
import { algebraAffineScheme } from '../src/v3_2/algebra_affine_scheme';
import { algebraAffineCover } from '../src/v3_2/algebra_cech';
import { defineAffineFormalCoverRealization } from '../src/v3_2/algebra_formal_realization';
import {
    AFFINE_FORMAL_RING_BINDINGS,
    defineAffineFormalPolynomialReifier
} from '../src/v3_2/algebra_formal_reifier';
import { AFFINE_FORMAL_COVER_BINDINGS } from '../src/v3_2/algebra_formal_cover';
import {
    AFFINE_FORMAL_LOCALIZATION_BINDINGS,
    defineAffineFormalLocalizationRealization
} from '../src/v3_2/algebra_formal_localization';
import {
    AFFINE_FORMAL_OVERLAP_BINDINGS,
    buildAffineFormalCechOverlapTerms,
    defineAffineFormalCechSimplexLocalization
} from '../src/v3_2/algebra_formal_overlap';
import {
    AFFINE_FORMAL_CECH_BINDINGS,
    ALGEBRA_FORMAL_CECH_PROFILE,
    AlgebraFormalCechError,
    buildAffineFormalCechPresentation
} from '../src/v3_2/algebra_formal_cech';

const because = (detail: string) => provenance('derived', detail);

const cechError = (code: AlgebraFormalCechError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraFormalCechError);
        assert.equal(error.code, code);
        return true;
    };

const coefficientTerm = (coefficient: typeof RATIONAL_DOMAIN.zero) => kernelFree(
    `formal_coefficient_${Array.from(new TextEncoder().encode(
        RATIONAL_DOMAIN.text(coefficient)
    )).map(byte => byte.toString(16)).join('')}`,
    because('coefficient')
);

const fixture = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const quotient = algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, []));
    const algebra = algebraPresentedAlgebra(quotient);
    const cover = algebraAffineCover(algebraAffineScheme(algebra), [
        algebraQuotientElement(quotient, x),
        algebraQuotientElement(
            quotient,
            algebraPolynomialSubtract(algebraPolynomialOne(ring), x)
        )
    ], 1);
    const source = defineAffineFormalPolynomialReifier({
        algebra,
        formalRing: kernelFree('formal_R', because('formal source ring')),
        generatorTerms: [kernelFree('formal_x', because('formal x'))],
        coefficientReifier: coefficientTerm,
        status: 'explicit-data'
    });
    const formalCover = defineAffineFormalCoverRealization({
        cover,
        algebra: source.realization,
        status: 'explicit-data',
        lawTerm: kernelFree('formal_cover_law', because('cover law'))
    });
    const simplices = cover.simplices.map((simplex, index) => {
        const localization = simplex.chart.chart.localization;
        const target = defineAffineFormalPolynomialReifier({
            algebra: localization.algebra,
            formalRing: kernelFree(`formal_S_${index}`, because('target ring')),
            generatorTerms: localization.extendedRing.variables.map((_, generator) =>
                kernelFree(
                    `formal_S_${index}_generator_${generator}`,
                    because('target generator')
                )
            ),
            coefficientReifier: coefficientTerm,
            status: 'explicit-data'
        });
        return defineAffineFormalCechSimplexLocalization(
            formalCover,
            simplex,
            defineAffineFormalLocalizationRealization({
                localization,
                source: source.realization,
                target: target.realization,
                formalMap: kernelFree(`formal_map_${index}`, because('map')),
                status: 'explicit-data',
                inverseLawTerm: kernelFree(
                    `formal_inverse_law_${index}`,
                    because('inverse law')
                ),
                universalTerm: kernelFree(
                    `formal_universal_${index}`,
                    because('universal localization')
                )
            })
        );
    });
    const overlap = buildAffineFormalCechOverlapTerms(
        formalCover,
        simplices,
        cover.simplices.map((simplex, simplexIndex) => simplex.faces.map(
            (_, faceIndex) => kernelFree(
                `formal_face_unit_${simplexIndex}_${faceIndex}`,
                because('face inversion')
            )
        ))
    );
    return { ring, x, quotient, algebra, cover, source, formalCover, overlap };
};

const bindings = Object.freeze({
    ...AFFINE_FORMAL_RING_BINDINGS,
    ...AFFINE_FORMAL_COVER_BINDINGS,
    ...AFFINE_FORMAL_LOCALIZATION_BINDINGS,
    ...AFFINE_FORMAL_OVERLAP_BINDINGS,
    ...AFFINE_FORMAL_CECH_BINDINGS
});

describe('v3.2 packed degreewise formal Cech presentation', () => {
    it('retains degreewise chart and signed-factor families', () => {
        const terms = buildAffineFormalCechPresentation(fixture().overlap);
        assert.deepEqual(terms.degrees.map(degree => degree.degree), [0, 1]);
        assert.deepEqual(terms.degrees.map(degree => degree.simplices.length), [2, 1]);
        assert.deepEqual(terms.degrees.map(degree => degree.faces.length), [2, 0]);
        assert.deepEqual(
            terms.degrees[0].faces.map(face => face.face.sign),
            [1, -1]
        );
        assert.equal(ALGEBRA_FORMAL_CECH_PROFILE.claimsCosimplicialIdentities,
            false);
        assert.equal(ALGEBRA_FORMAL_CECH_PROFILE.claimsDifferential, false);
        assert.equal(ALGEBRA_FORMAL_CECH_PROFILE.claimsCohomology, false);
        assert.equal(ALGEBRA_FORMAL_CECH_PROFILE.addsCechOwner, false);
    });

    it('packs whole localization factors rather than detached restriction maps', () => {
        const terms = buildAffineFormalCechPresentation(fixture().overlap);
        const signed = serializeCoreExpression(terms.degrees[0].signedFactors.family);
        assert.match(signed, /bridge_CommRingLocalizationFactor/u);
        assert.match(signed, /bridge_comm_ring_localization_factorization_is_contr/u);
        assert.match(signed, /bridge_Struct_sigma/u);
        assert.match(signed, /bridge_bool_positive/u);
        assert.match(signed, /bridge_bool_negative/u);
        assert.ok(signed.indexOf('bridge_bool_positive') <
            signed.indexOf('bridge_bool_negative'));
    });

    it('emits one deterministic heterogeneous family of degree presentations', () => {
        const terms = buildAffineFormalCechPresentation(fixture().overlap);
        const portable = serializeCoreExpression(terms.degreePresentations.family);
        const first = serializeKernelExpression(terms.degreePresentations.family, {
            externalFreeReferences: bindings
        });
        assert.match(portable, /bridge_Sigma_grpd/u);
        assert.match(portable, /bridge_Product_pair_grpd/u);
        assert.match(portable, /bridge_finite_family_cons/u);
        assert.match(first, /@Struct_sigma/u);
        assert.match(first, /@Product_pair_grpd/u);
        assert.match(first, /@finite_family_cons/u);
        assert.match(first, /AffineSpecBigSlice_cat/u);
        assert.equal(
            first,
            serializeKernelExpression(terms.degreePresentations.family, {
                externalFreeReferences: bindings
            })
        );
    });

    it('rejects simplex order drift from the computational cochain degree', () => {
        const value = fixture();
        const forged = Object.freeze({
            ...value.overlap,
            simplices: Object.freeze([
                value.overlap.simplices[1],
                value.overlap.simplices[0],
                value.overlap.simplices[2]
            ])
        });
        assert.throws(
            () => buildAffineFormalCechPresentation(forged),
            cechError('SIMPLEX_ORDER_MISMATCH')
        );
    });

    it('rejects face order drift from the computational cochain degree', () => {
        const value = fixture();
        const forged = Object.freeze({
            ...value.overlap,
            faces: Object.freeze([
                value.overlap.faces[1],
                value.overlap.faces[0]
            ])
        });
        assert.throws(
            () => buildAffineFormalCechPresentation(forged),
            cechError('FACE_ORDER_MISMATCH')
        );
    });
});
