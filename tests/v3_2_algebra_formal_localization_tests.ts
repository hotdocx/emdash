/** Focused BRIDGE-LOCALIZATION-4A localization/chart Core tests. */

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
import {
    defineAffineFormalAlgebraRealization,
    defineAffineFormalCoverRealization
} from '../src/v3_2/algebra_formal_realization';
import {
    AFFINE_FORMAL_RING_BINDINGS,
    defineAffineFormalPolynomialReifier
} from '../src/v3_2/algebra_formal_reifier';
import { AFFINE_FORMAL_COVER_BINDINGS } from '../src/v3_2/algebra_formal_cover';
import {
    AFFINE_FORMAL_LOCALIZATION_BINDINGS,
    ALGEBRA_FORMAL_LOCALIZATION_PROFILE,
    AlgebraFormalLocalizationError,
    buildAffineFormalCoverLocalizationTerms,
    buildAffineFormalLocalizationTerms,
    buildAffineFormalLocalizationUnitTerms,
    defineAffineFormalLocalizationRealization
} from '../src/v3_2/algebra_formal_localization';

const because = (detail: string) => provenance('derived', detail);

const localizationError = (code: AlgebraFormalLocalizationError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraFormalLocalizationError);
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
        lawTerm: kernelFree('formal_cover_law', because('formal cover law'))
    });
    return { ring, x, quotient, algebra, cover, source, formalCover };
};

const localizationRealization = (
    value: ReturnType<typeof fixture>,
    index: number,
    options: {
        readonly status?: 'explicit-data' | 'trusted-computation' | 'checked';
        readonly withUniversal?: boolean;
    } = {}
) => {
    const localization = value.cover.charts[index].chart.localization;
    const status = options.status ?? 'explicit-data';
    const target = defineAffineFormalPolynomialReifier({
        algebra: localization.algebra,
        formalRing: kernelFree(`formal_L_${index}`, because('formal target ring')),
        generatorTerms: localization.extendedRing.variables.map((_, generator) =>
            kernelFree(
                `formal_L_${index}_generator_${generator}`,
                because('formal target generator')
            )
        ),
        coefficientReifier: coefficientTerm,
        status
    });
    return defineAffineFormalLocalizationRealization({
        localization,
        source: value.source.realization,
        target: target.realization,
        formalMap: kernelFree(`formal_iota_${index}`, because('formal map')),
        status,
        ...(status === 'trusted-computation' ? {} : {
            inverseLawTerm: kernelFree(
                `formal_inverse_law_${index}`,
                because('formal inverse law')
            ),
            ...(options.withUniversal === false ? {} : {
                universalTerm: kernelFree(
                    `formal_universal_${index}`,
                    because('formal localization universal property')
                )
            })
        })
    });
};

const bindings = Object.freeze({
    ...AFFINE_FORMAL_RING_BINDINGS,
    ...AFFINE_FORMAL_COVER_BINDINGS,
    ...AFFINE_FORMAL_LOCALIZATION_BINDINGS
});

describe('v3.2 assumption-explicit formal principal localization', () => {
    it('constructs exact unit, universal localization, and basic-open chart terms', () => {
        const realization = localizationRealization(fixture(), 0);
        const terms = buildAffineFormalLocalizationTerms(realization);
        const portable = serializeCoreExpression(terms.chart);
        const lambdapi = serializeKernelExpression(terms.chart, {
            externalFreeReferences: bindings
        });
        assert.match(portable, /bridge_affine_spec_basic_open_chart/u);
        assert.match(portable, /bridge_comm_ring_localization_intro/u);
        assert.match(portable, /bridge_comm_ring_localization_property_intro/u);
        assert.match(portable, /bridge_comm_ring_unit_intro/u);
        assert.match(portable, /bridge_comm_ring_hom_apply/u);
        assert.match(lambdapi, /@affine_spec_basic_open_chart/u);
        assert.match(lambdapi, /@comm_ring_localization_intro/u);
        assert.match(lambdapi, /@comm_ring_localization_property_intro/u);
        assert.match(lambdapi, /@comm_ring_unit_intro/u);
        assert.equal(realization.computationalInverseEquationHolds, true);
        assert.equal(realization.formalLocalizationAvailable, true);
        assert.equal(ALGEBRA_FORMAL_LOCALIZATION_PROFILE.addsCoreOwner, false);
    });

    it('keeps unit evidence useful without pretending it is a localization', () => {
        const realization = localizationRealization(fixture(), 0, {
            withUniversal: false
        });
        const unit = buildAffineFormalLocalizationUnitTerms(realization);
        assert.match(serializeCoreExpression(unit.unit), /bridge_comm_ring_unit_intro/u);
        assert.equal(realization.formalUnitAvailable, true);
        assert.equal(realization.formalLocalizationAvailable, false);
        assert.throws(
            () => buildAffineFormalLocalizationTerms(realization),
            localizationError('FORMAL_LOCALIZATION_UNAVAILABLE')
        );
    });

    it('keeps trusted computation outside formal unit and localization evidence', () => {
        const value = fixture();
        const trusted = localizationRealization(value, 0, {
            status: 'trusted-computation'
        });
        assert.equal(trusted.formalUnitAvailable, false);
        assert.equal(trusted.formalLocalizationAvailable, false);
        assert.throws(
            () => buildAffineFormalLocalizationUnitTerms(trusted),
            localizationError('FORMAL_UNIT_UNAVAILABLE')
        );
        const localization = value.cover.charts[0].chart.localization;
        const target = defineAffineFormalPolynomialReifier({
            algebra: localization.algebra,
            formalRing: kernelFree('formal_trusted_L', because('trusted target')),
            generatorTerms: localization.extendedRing.variables.map((_, index) =>
                kernelFree(`formal_trusted_generator_${index}`, because('generator'))
            ),
            coefficientReifier: coefficientTerm,
            status: 'trusted-computation'
        });
        assert.throws(
            () => defineAffineFormalLocalizationRealization({
                localization,
                source: value.source.realization,
                target: target.realization,
                formalMap: kernelFree('formal_trusted_map', because('map')),
                status: 'trusted-computation',
                inverseLawTerm: kernelFree('forbidden_law', because('law'))
            }),
            localizationError('TRUSTED_FORMAL_LOCALIZATION_EVIDENCE')
        );
    });

    it('constructs the existing dependent localization family in cover order', () => {
        const value = fixture();
        const terms = buildAffineFormalCoverLocalizationTerms(
            value.formalCover,
            [localizationRealization(value, 0), localizationRealization(value, 1)]
        );
        const portable = serializeCoreExpression(terms.coverFamily);
        const lambdapi = serializeKernelExpression(terms.coverFamily, {
            externalFreeReferences: bindings
        });
        assert.match(portable, /bridge_comm_ring_zariski_cover_family_intro/u);
        assert.equal(
            portable.match(/bridge_comm_ring_localization_family_cons/gu)?.length,
            2
        );
        assert.equal(
            portable.match(/bridge_comm_ring_localization_intro/gu)?.length,
            2
        );
        assert.ok(portable.indexOf('formal_iota_0') < portable.indexOf('formal_iota_1'));
        assert.match(lambdapi, /@comm_ring_zariski_cover_family_intro/u);
        assert.match(lambdapi, /@comm_ring_localization_family_cons/u);
        assert.equal(terms.charts.length, 2);
        assert.equal(
            lambdapi,
            serializeKernelExpression(terms.coverFamily, {
                externalFreeReferences: bindings
            })
        );
    });

    it('rejects foreign targets, wrong cover order, and mismatched formal sources', () => {
        const value = fixture();
        const localization = value.cover.charts[0].chart.localization;
        assert.throws(
            () => defineAffineFormalLocalizationRealization({
                localization,
                source: value.source.realization,
                target: value.source.realization,
                formalMap: kernelFree('foreign_target_map', because('map')),
                status: 'explicit-data',
                inverseLawTerm: kernelFree('foreign_target_law', because('law'))
            }),
            localizationError('FOREIGN_LOCALIZATION_TARGET')
        );
        const first = localizationRealization(value, 0);
        const second = localizationRealization(value, 1);
        assert.throws(
            () => buildAffineFormalCoverLocalizationTerms(
                value.formalCover,
                [second, first]
            ),
            localizationError('FOREIGN_COVER_LOCALIZATION')
        );
        const alternateSource = defineAffineFormalAlgebraRealization({
            algebra: value.algebra,
            formalRing: kernelFree('formal_R_alternate', because('alternate source')),
            status: 'explicit-data',
            reifyElement: element => value.source.reifyElement(element)
        });
        const target = defineAffineFormalPolynomialReifier({
            algebra: localization.algebra,
            formalRing: kernelFree('formal_L_alternate', because('target')),
            generatorTerms: localization.extendedRing.variables.map((_, index) =>
                kernelFree(`formal_L_alternate_${index}`, because('generator'))
            ),
            coefficientReifier: coefficientTerm,
            status: 'explicit-data'
        });
        const alternate = defineAffineFormalLocalizationRealization({
            localization,
            source: alternateSource,
            target: target.realization,
            formalMap: kernelFree('formal_iota_alternate', because('map')),
            status: 'explicit-data',
            inverseLawTerm: kernelFree('formal_law_alternate', because('law')),
            universalTerm: kernelFree('formal_universal_alternate', because('universal'))
        });
        assert.throws(
            () => buildAffineFormalCoverLocalizationTerms(
                value.formalCover,
                [alternate, second]
            ),
            localizationError('FORMAL_COVER_SOURCE_MISMATCH')
        );
    });
});
