/** Focused PAM-BASECHANGE-4A functorial module base-change tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { RATIONAL_DOMAIN, algebraRational } from '../src/v3_2/algebra_exact';
import { algebraPolynomialIdeal } from '../src/v3_2/algebra_ideal';
import {
    algebraPolynomialConstant,
    algebraPolynomialRing,
    algebraPolynomialVariable
} from '../src/v3_2/algebra_polynomial';
import {
    algebraPolynomialQuotientRing,
    algebraQuotientElement
} from '../src/v3_2/algebra_quotient';
import {
    algebraPresentedAlgebra,
    algebraPresentedAlgebraMap,
    algebraPresentedAlgebraMapCompose,
    algebraPresentedAlgebraMapIdentity
} from '../src/v3_2/algebra_presented_algebra';
import {
    algebraPresentedAlgebraFreeModule,
    algebraPresentedAlgebraModule,
    algebraPresentedAlgebraModuleBasisVector,
    algebraPresentedAlgebraModuleElement,
    algebraPresentedAlgebraModuleElementEquals,
    algebraPresentedAlgebraModuleElementScale,
    algebraPresentedAlgebraModuleVector
} from '../src/v3_2/algebra_presented_module';
import {
    algebraPresentedAlgebraModuleLinearMap,
    algebraPresentedAlgebraModuleSemilinearMap,
    algebraPresentedAlgebraModuleSemilinearMapApply,
    algebraPresentedAlgebraModuleSemilinearMapCompose,
    algebraPresentedAlgebraModuleSemilinearMapEquals
} from '../src/v3_2/algebra_presented_module_map';
import {
    ALGEBRA_PRESENTED_MODULE_BASE_CHANGE_PROFILE,
    AlgebraPresentedModuleBaseChangeError,
    algebraPresentedModuleBaseChange,
    algebraPresentedModuleBaseChangeElement,
    algebraPresentedModuleBaseChangeIdentityHolds,
    algebraPresentedModuleBaseChangeMap,
    algebraPresentedModuleBaseChangeSchema,
    serializeAlgebraPresentedModuleBaseChange
} from '../src/v3_2/algebra_presented_module_base_change';

const baseChangeError = (code: AlgebraPresentedModuleBaseChangeError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraPresentedModuleBaseChangeError);
        assert.equal(error.code, code);
        return true;
    };

const algebra = (variable: string) => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, [variable], 'lex');
    const generator = algebraPolynomialVariable(ring, 0);
    const quotient = algebraPolynomialQuotientRing(
        algebraPolynomialIdeal(ring, [])
    );
    return {
        ring,
        generator,
        quotient,
        algebra: algebraPresentedAlgebra(quotient)
    };
};

const algebraMap = (
    source: ReturnType<typeof algebra>,
    target: ReturnType<typeof algebra>
) => algebraPresentedAlgebraMap(source.algebra, target.algebra, [
    algebraQuotientElement(target.quotient, target.generator)
]);

const cyclicModule = (value: ReturnType<typeof algebra>, relation = true) => {
    const free = algebraPresentedAlgebraFreeModule(value.algebra, 1);
    const presented = algebraPresentedAlgebraModule(
        free,
        relation ? [algebraPresentedAlgebraModuleVector(free, [
            algebraQuotientElement(value.quotient, value.generator)
        ])] : []
    );
    const basis = algebraPresentedAlgebraModuleElement(
        presented,
        algebraPresentedAlgebraModuleBasisVector(free, 0)
    );
    return { free, presented, basis };
};

describe('v3.2 base change of presented-algebra modules', () => {
    it('transports A/(x) to B/(y) and retains its canonical unit', () => {
        const a = algebra('x');
        const b = algebra('y');
        const source = cyclicModule(a);
        const expected = cyclicModule(b);
        const changed = algebraPresentedModuleBaseChange(
            algebraMap(a, b),
            source.presented
        );
        assert.deepEqual(changed.target.identity, expected.presented.identity);
        assert.equal(changed.transportedRelations.length, 1);
        assert.ok(algebraPresentedAlgebraModuleElementEquals(
            algebraPresentedModuleBaseChangeElement(changed, source.basis),
            expected.basis
        ));
        assert.equal(changed.unit.relationImages.length, 1);
    });

    it('computes identity base change without changing module identity', () => {
        const a = algebra('x');
        const source = cyclicModule(a);
        const changed = algebraPresentedModuleBaseChange(
            algebraPresentedAlgebraMapIdentity(a.algebra),
            source.presented
        );
        assert.equal(algebraPresentedModuleBaseChangeIdentityHolds(changed), true);
        assert.deepEqual(changed.source.identity, changed.target.identity);
    });

    it('agrees under iterated and composite scalar base change', () => {
        const a = algebra('x');
        const b = algebra('y');
        const c = algebra('z');
        const source = cyclicModule(a);
        const ab = algebraMap(a, b);
        const bc = algebraMap(b, c);
        const first = algebraPresentedModuleBaseChange(ab, source.presented);
        const second = algebraPresentedModuleBaseChange(bc, first.target);
        const direct = algebraPresentedModuleBaseChange(
            algebraPresentedAlgebraMapCompose(bc, ab),
            source.presented
        );
        const compositeUnit =
            algebraPresentedAlgebraModuleSemilinearMapCompose(
                second.unit,
                first.unit
            );
        assert.deepEqual(second.target.identity, direct.target.identity);
        assert.equal(
            algebraPresentedAlgebraModuleSemilinearMapEquals(
                compositeUnit,
                direct.unit
            ),
            true
        );
    });

    it('base-changes linear maps and computes the naturality square', () => {
        const a = algebra('x');
        const b = algebra('y');
        const source = cyclicModule(a, false);
        const two = algebraQuotientElement(
            a.quotient,
            algebraPolynomialConstant(a.ring, algebraRational(2n))
        );
        const double = algebraPresentedAlgebraModuleLinearMap(
            source.presented,
            source.presented,
            [algebraPresentedAlgebraModuleElementScale(two, source.basis)]
        );
        const changed = algebraPresentedModuleBaseChangeMap(
            algebraMap(a, b),
            double
        );
        const targetBasis = algebraPresentedAlgebraModuleElement(
            changed.sourceBaseChange.target,
            algebraPresentedAlgebraModuleBasisVector(
                changed.sourceBaseChange.target.freeModule,
                0
            )
        );
        const targetTwo = algebraQuotientElement(
            b.quotient,
            algebraPolynomialConstant(b.ring, algebraRational(2n))
        );
        assert.ok(algebraPresentedAlgebraModuleElementEquals(
            algebraPresentedAlgebraModuleSemilinearMapApply(
                changed.map,
                targetBasis
            ),
            algebraPresentedAlgebraModuleElementScale(targetTwo, targetBasis)
        ));
        assert.equal(changed.naturalityHolds, true);
        assert.equal(
            algebraPresentedAlgebraModuleSemilinearMapEquals(
                changed.mapAfterUnit,
                changed.unitAfterMap
            ),
            true
        );
    });

    it('roundtrips its schema and deterministic serialization', () => {
        const a = algebra('x');
        const b = algebra('y');
        const source = cyclicModule(a);
        const scalarMap = algebraMap(a, b);
        const changed = algebraPresentedModuleBaseChange(
            scalarMap,
            source.presented
        );
        const schema = algebraPresentedModuleBaseChangeSchema(
            scalarMap,
            source.presented
        );
        const normalized = schema.normalize(changed, 'baseChange');
        assert.deepEqual(normalized.target.identity, changed.target.identity);
        assert.equal(
            serializeAlgebraPresentedModuleBaseChange(changed),
            serializeAlgebraPresentedModuleBaseChange(changed)
        );
        assert.equal(
            ALGEBRA_PRESENTED_MODULE_BASE_CHANGE_PROFILE.canonicalMap,
            'basis-to-basis-semilinear-map'
        );
    });

    it('rejects foreign scalar sources and non-linear morphism inputs', () => {
        const a = algebra('x');
        const b = algebra('y');
        const c = algebra('z');
        const ma = cyclicModule(a);
        const mb = cyclicModule(b);
        assert.throws(
            () => algebraPresentedModuleBaseChange(
                algebraMap(b, c),
                ma.presented
            ),
            baseChangeError('INVALID_ENDPOINTS')
        );
        const semilinear = algebraPresentedAlgebraModuleSemilinearMap(
            ma.presented,
            mb.presented,
            algebraMap(a, b),
            [mb.basis]
        );
        assert.throws(
            () => algebraPresentedModuleBaseChangeMap(
                algebraMap(a, b),
                semilinear
            ),
            baseChangeError('NONLINEAR_SOURCE_MAP')
        );
    });
});
