/** Focused BRIDGE-OVERLAP-4B product-localization and face-factor tests. */

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
    ALGEBRA_FORMAL_OVERLAP_PROFILE,
    AlgebraFormalOverlapError,
    buildAffineFormalCechOverlapTerms,
    defineAffineFormalCechSimplexLocalization
} from '../src/v3_2/algebra_formal_overlap';

const because = (detail: string) => provenance('derived', detail);

const overlapError = (code: AlgebraFormalOverlapError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraFormalOverlapError);
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
    return { ring, x, quotient, algebra, cover, source, formalCover };
};

const simplexRealization = (
    value: ReturnType<typeof fixture>,
    index: number,
    status: 'explicit-data' | 'trusted-computation' | 'checked' = 'explicit-data'
) => {
    const simplex = value.cover.simplices[index];
    const localization = simplex.chart.chart.localization;
    const target = defineAffineFormalPolynomialReifier({
        algebra: localization.algebra,
        formalRing: kernelFree(`formal_S_${index}`, because('simplex target ring')),
        generatorTerms: localization.extendedRing.variables.map((_, generator) =>
            kernelFree(
                `formal_S_${index}_generator_${generator}`,
                because('simplex target generator')
            )
        ),
        coefficientReifier: coefficientTerm,
        status
    });
    const formalLocalization = defineAffineFormalLocalizationRealization({
        localization,
        source: value.source.realization,
        target: target.realization,
        formalMap: kernelFree(`formal_simplex_map_${index}`, because('map')),
        status,
        ...(status === 'trusted-computation' ? {} : {
            inverseLawTerm: kernelFree(
                `formal_simplex_inverse_law_${index}`,
                because('inverse law')
            ),
            universalTerm: kernelFree(
                `formal_simplex_universal_${index}`,
                because('universal localization')
            )
        })
    });
    return defineAffineFormalCechSimplexLocalization(
        value.formalCover,
        simplex,
        formalLocalization
    );
};

const inversionTerms = (value: ReturnType<typeof fixture>) =>
    value.cover.simplices.map((simplex, simplexIndex) => simplex.faces.map(
        (_, faceIndex) => kernelFree(
            `formal_face_unit_${simplexIndex}_${faceIndex}`,
            because('target inverts face denominator')
        )
    ));

const bindings = Object.freeze({
    ...AFFINE_FORMAL_RING_BINDINGS,
    ...AFFINE_FORMAL_COVER_BINDINGS,
    ...AFFINE_FORMAL_LOCALIZATION_BINDINGS,
    ...AFFINE_FORMAL_OVERLAP_BINDINGS
});

describe('v3.2 formal product-localization simplices and universal face factors', () => {
    it('derives whole face maps from localization contractibility', () => {
        const value = fixture();
        const simplices = value.cover.simplices.map((_, index) =>
            simplexRealization(value, index)
        );
        const terms = buildAffineFormalCechOverlapTerms(
            value.formalCover,
            simplices,
            inversionTerms(value)
        );
        assert.deepEqual(terms.simplices.map(item => item.simplex.indices), [
            [0], [1], [0, 1]
        ]);
        assert.equal(terms.faces.length, 2);
        assert.deepEqual(terms.faces.map(item => item.face.sign), [1, -1]);
        assert.equal(
            terms.faces[0].face.restrictionMap,
            value.cover.simplices[2].faces[0].restrictionMap
        );
        const map = serializeCoreExpression(terms.faces[0].map);
        const agreement = serializeCoreExpression(terms.faces[0].agreement);
        assert.match(map, /bridge_comm_ring_localization_factor_map/u);
        assert.match(map, /bridge_is_contr_center/u);
        assert.match(map, /bridge_comm_ring_localization_factorization_is_contr/u);
        assert.match(agreement, /bridge_comm_ring_localization_factor_agreement/u);
        assert.equal(ALGEBRA_FORMAL_OVERLAP_PROFILE.handwrittenFaceMap, false);
        assert.equal(ALGEBRA_FORMAL_OVERLAP_PROFILE.handwrittenTriangle, false);
        assert.equal(ALGEBRA_FORMAL_OVERLAP_PROFILE.addsCechOwner, false);
    });

    it('emits exact active universal-factor owners deterministically', () => {
        const value = fixture();
        const terms = buildAffineFormalCechOverlapTerms(
            value.formalCover,
            value.cover.simplices.map((_, index) => simplexRealization(value, index)),
            inversionTerms(value)
        );
        const first = serializeKernelExpression(terms.faces[1].agreement, {
            externalFreeReferences: bindings
        });
        assert.match(first, /@comm_ring_localization_factor_agreement/u);
        assert.match(first, /@comm_ring_localization_factorization_is_contr/u);
        assert.match(first, /@CommRingLocalizationFactor/u);
        assert.match(first, /@is_contr_center/u);
        assert.equal(
            first,
            serializeKernelExpression(terms.faces[1].agreement, {
                externalFreeReferences: bindings
            })
        );
    });

    it('requires exact simplex order and one inversion term per face', () => {
        const value = fixture();
        const simplices = value.cover.simplices.map((_, index) =>
            simplexRealization(value, index)
        );
        assert.throws(
            () => buildAffineFormalCechOverlapTerms(
                value.formalCover,
                [simplices[1], simplices[0], simplices[2]],
                inversionTerms(value)
            ),
            overlapError('FOREIGN_SIMPLEX')
        );
        assert.throws(
            () => buildAffineFormalCechOverlapTerms(
                value.formalCover,
                simplices,
                [[], [], [kernelFree('only_one_unit', because('unit'))]]
            ),
            overlapError('FACE_EVIDENCE_ARITY_MISMATCH')
        );
    });

    it('rejects a foreign simplex or localization package', () => {
        const first = fixture();
        const second = fixture();
        const foreign = simplexRealization(second, 0);
        assert.throws(
            () => defineAffineFormalCechSimplexLocalization(
                first.formalCover,
                second.cover.simplices[0] as never,
                foreign.localization as never
            ),
            overlapError('FOREIGN_SIMPLEX')
        );
        assert.throws(
            () => defineAffineFormalCechSimplexLocalization(
                first.formalCover,
                first.cover.simplices[0],
                simplexRealization(first, 1).localization
            ),
            overlapError('SIMPLEX_LOCALIZATION_MISMATCH')
        );
    });

    it('rejects trusted product localizations before face construction', () => {
        const value = fixture();
        assert.throws(
            () => simplexRealization(value, 2, 'trusted-computation'),
            overlapError('FORMAL_SIMPLEX_LOCALIZATION_UNAVAILABLE')
        );
    });
});
