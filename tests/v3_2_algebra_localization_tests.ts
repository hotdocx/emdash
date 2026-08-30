/** Focused AFFINE-LOCALIZATION-2A principal-localization tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import { algebraPolynomialIdeal } from '../src/v3_2/algebra_ideal';
import {
    algebraPolynomialAdd,
    algebraPolynomialOne,
    algebraPolynomialPower,
    algebraPolynomialRing,
    algebraPolynomialVariable
} from '../src/v3_2/algebra_polynomial';
import {
    algebraPolynomialQuotientRing,
    algebraQuotientElement,
    algebraQuotientEquals,
    algebraQuotientMultiply,
    algebraQuotientOne,
    algebraQuotientZero
} from '../src/v3_2/algebra_quotient';
import { algebraPresentedAlgebra, algebraPresentedAlgebraMapApply } from '../src/v3_2/algebra_presented_algebra';
import {
    ALGEBRA_LOCALIZATION_PROFILE,
    AlgebraLocalizationError,
    algebraBasicOpenChart,
    algebraPrincipalLocalization
} from '../src/v3_2/algebra_localization';
import { algebraLocalizationReferenceOperations } from '../src/v3_2/algebra_localization_reference_operations';
import {
    createAlgebraComputationGraphBuilder,
    executeAlgebraComputationGraph
} from '../src/v3_2/algebra_graph';
import { createAlgebraTypeScriptReferenceEngine } from '../src/v3_2/algebra_reference_engine';

const localizationError = (code: AlgebraLocalizationError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraLocalizationError);
        assert.equal(error.code, code);
        return true;
    };

const affineLine = (variables: readonly string[] = ['x']) => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, variables, 'lex');
    const quotient = algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, []));
    return { ring, quotient, algebra: algebraPresentedAlgebra(quotient) };
};

describe('v3.2 principal localizations and basic opens', () => {
    it('adjoins and verifies an inverse for x on the affine line', () => {
        const source = affineLine();
        const x = algebraQuotientElement(
            source.quotient,
            algebraPolynomialVariable(source.ring, 0)
        );
        const localization = algebraPrincipalLocalization(source.algebra, x);
        assert.deepEqual(localization.extendedRing.variables, ['x', 'emdash_inv']);
        assert.equal(localization.inverseVariable, 'emdash_inv');
        assert.equal(localization.inverseEquation, true);
        assert.ok(algebraQuotientEquals(
            algebraQuotientMultiply(localization.elementImage, localization.inverse),
            algebraQuotientOne(localization.algebra.quotient)
        ));
        assert.ok(algebraQuotientEquals(
            algebraPresentedAlgebraMapApply(localization.canonicalMap, x),
            localization.elementImage
        ));
        assert.equal(ALGEBRA_LOCALIZATION_PROFILE.presentation,
            'adjoin-inverse-variable-and-tf-minus-one');
        assert.ok(Object.isFrozen(localization));
    });

    it('packages the localization as a basic-open coordinate chart', () => {
        const source = affineLine();
        const x = algebraQuotientElement(
            source.quotient,
            algebraPolynomialVariable(source.ring, 0)
        );
        const chart = algebraBasicOpenChart(source.algebra, x);
        assert.equal(chart.coordinateAlgebra, chart.localization.algebra);
        assert.equal(chart.localization.inverseEquation, true);
        assert.ok(Object.isFrozen(chart));
    });

    it('localizes units without a separate isomorphism shortcut', () => {
        const source = affineLine();
        const one = algebraQuotientElement(
            source.quotient,
            algebraPolynomialOne(source.ring)
        );
        const localization = algebraPrincipalLocalization(source.algebra, one);
        assert.ok(algebraQuotientEquals(
            localization.inverse,
            algebraQuotientOne(localization.algebra.quotient)
        ));
    });

    it('computes localization at a nilpotent as the zero algebra', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
        const xPolynomial = algebraPolynomialVariable(ring, 0);
        const quotient = algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, [
            algebraPolynomialPower(xPolynomial, 2n)
        ]));
        const source = algebraPresentedAlgebra(quotient);
        const x = algebraQuotientElement(quotient, xPolynomial);
        const localization = algebraPrincipalLocalization(source, x);
        assert.ok(algebraQuotientEquals(
            algebraQuotientOne(localization.algebra.quotient),
            algebraQuotientZero(localization.algebra.quotient)
        ));
        assert.equal(localization.inverseEquation, true);
    });

    it('uses canonical source representatives and fresh inverse names', () => {
        const ring = algebraPolynomialRing(
            RATIONAL_DOMAIN,
            ['x', 'emdash_inv'],
            'lex'
        );
        const xPolynomial = algebraPolynomialVariable(ring, 0);
        const quotient = algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, [
            algebraPolynomialPower(xPolynomial, 2n)
        ]));
        const source = algebraPresentedAlgebra(quotient);
        const first = algebraPrincipalLocalization(
            source,
            algebraQuotientElement(quotient, xPolynomial)
        );
        const second = algebraPrincipalLocalization(
            source,
            algebraQuotientElement(
                quotient,
                algebraPolynomialAdd(xPolynomial, algebraPolynomialPower(xPolynomial, 2n))
            )
        );
        assert.equal(first.inverseVariable, 'emdash_inv1');
        assert.equal(first.algebra.quotient.identity.id,
            second.algebra.quotient.identity.id);
    });

    it('rejects an element from a foreign source algebra', () => {
        const source = affineLine();
        const foreign = affineLine(['y']);
        assert.throws(
            () => algebraPrincipalLocalization(
                source.algebra,
                algebraQuotientElement(
                    foreign.quotient,
                    algebraPolynomialVariable(foreign.ring, 0)
                ) as never
            ),
            localizationError('FOREIGN_LOCALIZED_ELEMENT')
        );
    });

    it('computes the whole localization in a retained graph', async () => {
        const source = affineLine();
        const x = algebraQuotientElement(
            source.quotient,
            algebraPolynomialVariable(source.ring, 0)
        );
        const operations = algebraLocalizationReferenceOperations(source.algebra);
        const builder = createAlgebraComputationGraphBuilder(
            'fixture.localization.compute',
            'v1'
        );
        const input = builder.input('element', operations.localize.input);
        const output = builder.operation('localization', operations.localize, input);
        const execution = await executeAlgebraComputationGraph({
            graph: builder.build([{ id: 'result', value: output }]),
            engine: createAlgebraTypeScriptReferenceEngine({
                implementations: operations.implementations
            }),
            inputs: [{ id: 'element', value: x }]
        });
        const localization = execution.outputs[0].value as ReturnType<
            typeof algebraPrincipalLocalization
        >;
        assert.equal(localization.inverseEquation, true);
        assert.deepEqual(localization.extendedRing.variables, ['x', 'emdash_inv']);
    });
});
