/** Focused PAM-LOCALIZATION-5A presented-module localization tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { RATIONAL_DOMAIN, algebraRational } from '../src/v3_2/algebra_exact';
import { algebraPolynomialIdeal } from '../src/v3_2/algebra_ideal';
import {
    algebraPolynomialAdd,
    algebraPolynomialConstant,
    algebraPolynomialOne,
    algebraPolynomialPower,
    algebraPolynomialRing,
    algebraPolynomialSubtract,
    algebraPolynomialVariable
} from '../src/v3_2/algebra_polynomial';
import {
    algebraPolynomialQuotientRing,
    algebraQuotientElement
} from '../src/v3_2/algebra_quotient';
import { algebraPresentedAlgebra } from '../src/v3_2/algebra_presented_algebra';
import {
    algebraPresentedAlgebraFreeModule,
    algebraPresentedAlgebraModule,
    algebraPresentedAlgebraModuleBasisVector,
    algebraPresentedAlgebraModuleElement,
    algebraPresentedAlgebraModuleElementScale,
    algebraPresentedAlgebraModuleVector
} from '../src/v3_2/algebra_presented_module';
import { algebraPresentedAlgebraModuleLinearMap } from
    '../src/v3_2/algebra_presented_module_map';
import {
    ALGEBRA_PRESENTED_MODULE_LOCALIZATION_PROFILE,
    AlgebraPresentedModuleLocalizationError,
    algebraPresentedModuleLocalization,
    algebraPresentedModuleLocalizationSchema,
    algebraPresentedModuleMapLocalization,
    serializeAlgebraPresentedModuleLocalization
} from '../src/v3_2/algebra_presented_module_localization';

const localizationError = (
    code: AlgebraPresentedModuleLocalizationError['code']
) => (error: unknown) => {
    assert.ok(error instanceof AlgebraPresentedModuleLocalizationError);
    assert.equal(error.code, code);
    return true;
};

const fixture = (
    variables: readonly string[] = ['x'],
    nilpotent = false,
    moduleRelation = true
) => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, variables, 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const quotient = algebraPolynomialQuotientRing(algebraPolynomialIdeal(
        ring,
        nilpotent ? [algebraPolynomialPower(x, 2n)] : []
    ));
    const algebra = algebraPresentedAlgebra(quotient);
    const free = algebraPresentedAlgebraFreeModule(algebra, 1);
    const module = algebraPresentedAlgebraModule(
        free,
        moduleRelation ? [algebraPresentedAlgebraModuleVector(free, [
            algebraQuotientElement(quotient, x)
        ])] : []
    );
    const basis = algebraPresentedAlgebraModuleElement(
        module,
        algebraPresentedAlgebraModuleBasisVector(free, 0)
    );
    return { ring, x, quotient, algebra, free, module, basis };
};

describe('v3.2 principal localization of presented-algebra modules', () => {
    it('kills A/(x) on D(x) and retains it on D(1-x)', () => {
        const value = fixture();
        const atX = algebraPresentedModuleLocalization(
            value.module,
            algebraQuotientElement(value.quotient, value.x)
        );
        const atOneMinusX = algebraPresentedModuleLocalization(
            value.module,
            algebraQuotientElement(
                value.quotient,
                algebraPolynomialSubtract(
                    algebraPolynomialOne(value.ring),
                    value.x
                )
            )
        );
        assert.equal(atX.isZero, true);
        assert.equal(atOneMinusX.isZero, false);
        assert.equal(atX.localization.inverseEquation, true);
        assert.equal(atOneMinusX.localization.inverseEquation, true);
        assert.equal(atX.module.freeModule.rank, 1);
    });

    it('uses the ordinary zero algebra when inverting a nilpotent', () => {
        const value = fixture(['x'], true, false);
        const localized = algebraPresentedModuleLocalization(
            value.module,
            algebraQuotientElement(value.quotient, value.x)
        );
        assert.equal(localized.isZero, true);
        assert.equal(localized.module.freeModule.algebra.quotient.basis.basis[0]
            .terms.length > 0, true);
    });

    it('identifies canonically equal denominators and module targets', () => {
        const value = fixture(['x'], true, false);
        const first = algebraPresentedModuleLocalization(
            value.module,
            algebraQuotientElement(value.quotient, value.x)
        );
        const second = algebraPresentedModuleLocalization(
            value.module,
            algebraQuotientElement(
                value.quotient,
                algebraPolynomialAdd(
                    value.x,
                    algebraPolynomialPower(value.x, 2n)
                )
            )
        );
        assert.deepEqual(
            first.localization.algebra.quotient.identity,
            second.localization.algebra.quotient.identity
        );
        assert.deepEqual(first.module.identity, second.module.identity);
    });

    it('inherits deterministic fresh inverse-variable selection', () => {
        const value = fixture(['x', 'emdash_inv'], false, false);
        const localized = algebraPresentedModuleLocalization(
            value.module,
            algebraQuotientElement(value.quotient, value.x)
        );
        assert.equal(localized.localization.inverseVariable, 'emdash_inv1');
        assert.equal(localized.isZero, false);
    });

    it('localizes linear maps through functorial base change', () => {
        const value = fixture(['x'], false, false);
        const two = algebraQuotientElement(
            value.quotient,
            algebraPolynomialConstant(value.ring, algebraRational(2n))
        );
        const double = algebraPresentedAlgebraModuleLinearMap(
            value.module,
            value.module,
            [algebraPresentedAlgebraModuleElementScale(two, value.basis)]
        );
        const localized = algebraPresentedModuleMapLocalization(
            double,
            algebraQuotientElement(value.quotient, value.x)
        );
        assert.equal(localized.baseChange.naturalityHolds, true);
        assert.equal(localized.baseChange.sourceBaseChange.target.identity.id,
            localized.baseChange.targetBaseChange.target.identity.id);
    });

    it('roundtrips schemas and deterministic serialization', () => {
        const value = fixture();
        const element = algebraQuotientElement(value.quotient, value.x);
        const localized = algebraPresentedModuleLocalization(
            value.module,
            element
        );
        const schema = algebraPresentedModuleLocalizationSchema(
            value.module,
            element
        );
        const normalized = schema.normalize(localized, 'localization');
        assert.deepEqual(normalized.module.identity, localized.module.identity);
        assert.equal(
            serializeAlgebraPresentedModuleLocalization(localized),
            serializeAlgebraPresentedModuleLocalization(localized)
        );
        assert.equal(ALGEBRA_PRESENTED_MODULE_LOCALIZATION_PROFILE.fractionSyntax,
            false);
    });

    it('rejects a denominator from a foreign scalar algebra', () => {
        const first = fixture(['x']);
        const second = fixture(['y']);
        assert.throws(
            () => algebraPresentedModuleLocalization(
                first.module,
                algebraQuotientElement(second.quotient, second.x) as never
            ),
            localizationError('FOREIGN_LOCALIZED_ELEMENT')
        );
    });
});
