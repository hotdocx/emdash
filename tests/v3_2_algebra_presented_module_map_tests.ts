/** Focused PAM-SEMILINEAR-3A relation-checked semilinear map tests. */

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
    algebraQuotientElement
} from '../src/v3_2/algebra_quotient';
import {
    algebraPresentedAlgebra,
    algebraPresentedAlgebraMap
} from '../src/v3_2/algebra_presented_algebra';
import {
    algebraPresentedAlgebraFreeModule,
    algebraPresentedAlgebraModule,
    algebraPresentedAlgebraModuleBasisVector,
    algebraPresentedAlgebraModuleElement,
    algebraPresentedAlgebraModuleElementEquals,
    algebraPresentedAlgebraModuleElementIsZero,
    algebraPresentedAlgebraModuleElementZero,
    algebraPresentedAlgebraModuleVector
} from '../src/v3_2/algebra_presented_module';
import {
    ALGEBRA_PRESENTED_MODULE_MAP_PROFILE,
    AlgebraPresentedModuleMapError,
    algebraPresentedAlgebraModuleLinearMap,
    algebraPresentedAlgebraModuleSemilinearMap,
    algebraPresentedAlgebraModuleSemilinearMapApply,
    algebraPresentedAlgebraModuleSemilinearMapCompose,
    algebraPresentedAlgebraModuleSemilinearMapEquals,
    algebraPresentedAlgebraModuleSemilinearMapIdentity,
    algebraPresentedAlgebraModuleSemilinearMapIsZero,
    algebraPresentedAlgebraModuleSemilinearMapSchema,
    serializeAlgebraPresentedAlgebraModuleSemilinearMap
} from '../src/v3_2/algebra_presented_module_map';

const mapError = (code: AlgebraPresentedModuleMapError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraPresentedModuleMapError);
        assert.equal(error.code, code);
        return true;
    };

const algebra = (variable: string, nilpotent = false) => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, [variable], 'lex');
    const generator = algebraPolynomialVariable(ring, 0);
    const quotient = algebraPolynomialQuotientRing(algebraPolynomialIdeal(
        ring,
        nilpotent ? [algebraPolynomialPower(generator, 2n)] : []
    ));
    return {
        ring,
        generator,
        quotient,
        algebra: algebraPresentedAlgebra(quotient)
    };
};

const cyclicModule = (value: ReturnType<typeof algebra>, withRelation = true) => {
    const free = algebraPresentedAlgebraFreeModule(value.algebra, 1);
    const module = algebraPresentedAlgebraModule(
        free,
        withRelation ? [algebraPresentedAlgebraModuleVector(free, [
            algebraQuotientElement(value.quotient, value.generator)
        ])] : []
    );
    const basis = algebraPresentedAlgebraModuleElement(
        module,
        algebraPresentedAlgebraModuleBasisVector(free, 0)
    );
    return { free, module, basis };
};

describe('v3.2 semilinear maps of presented-algebra modules', () => {
    it('validates and applies a semilinear map A/(x) to B/(y)', () => {
        const sourceAlgebra = algebra('x');
        const targetAlgebra = algebra('y');
        const source = cyclicModule(sourceAlgebra);
        const target = cyclicModule(targetAlgebra);
        const scalarMap = algebraPresentedAlgebraMap(
            sourceAlgebra.algebra,
            targetAlgebra.algebra,
            [algebraQuotientElement(
                targetAlgebra.quotient,
                targetAlgebra.generator
            )]
        );
        const map = algebraPresentedAlgebraModuleSemilinearMap(
            source.module,
            target.module,
            scalarMap,
            [target.basis]
        );
        const xPlusOne = algebraPresentedAlgebraModuleElement(
            source.module,
            algebraPresentedAlgebraModuleVector(source.free, [
                algebraQuotientElement(
                    sourceAlgebra.quotient,
                    algebraPolynomialAdd(
                        sourceAlgebra.generator,
                        algebraPolynomialOne(sourceAlgebra.ring)
                    )
                )
            ])
        );
        assert.ok(algebraPresentedAlgebraModuleElementEquals(
            algebraPresentedAlgebraModuleSemilinearMapApply(map, xPlusOne),
            target.basis
        ));
        assert.equal(map.algebraActionRelationImages.length, 0);
        assert.equal(map.relationImages.length, 1);
        assert.equal(map.relationImages[0].family, 'module');
    });

    it('checks quotient-algebra action relations through the scalar map', () => {
        const sourceAlgebra = algebra('x', true);
        const targetAlgebra = algebra('y', true);
        const source = cyclicModule(sourceAlgebra, false);
        const target = cyclicModule(targetAlgebra, false);
        const scalarMap = algebraPresentedAlgebraMap(
            sourceAlgebra.algebra,
            targetAlgebra.algebra,
            [algebraQuotientElement(
                targetAlgebra.quotient,
                targetAlgebra.generator
            )]
        );
        const map = algebraPresentedAlgebraModuleSemilinearMap(
            source.module,
            target.module,
            scalarMap,
            [target.basis]
        );
        assert.equal(map.algebraActionRelationImages.length, 1);
        assert.equal(map.relationImages.length, 0);
        assert.equal(algebraPresentedAlgebraModuleElementIsZero(
            map.algebraActionRelationImages[0].image
        ), true);
    });

    it('rejects a source module relation that survives in the target', () => {
        const sourceAlgebra = algebra('x');
        const targetAlgebra = algebra('y');
        const source = cyclicModule(sourceAlgebra);
        const target = cyclicModule(targetAlgebra, false);
        const scalarMap = algebraPresentedAlgebraMap(
            sourceAlgebra.algebra,
            targetAlgebra.algebra,
            [algebraQuotientElement(
                targetAlgebra.quotient,
                targetAlgebra.generator
            )]
        );
        assert.throws(
            () => algebraPresentedAlgebraModuleSemilinearMap(
                source.module,
                target.module,
                scalarMap,
                [target.basis]
            ),
            mapError('SOURCE_RELATION_FAILED')
        );
    });

    it('constructs identity, linear zero maps, and canonical equality', () => {
        const value = algebra('x');
        const module = cyclicModule(value);
        const identity = algebraPresentedAlgebraModuleSemilinearMapIdentity(
            module.module
        );
        const linearIdentity = algebraPresentedAlgebraModuleLinearMap(
            module.module,
            module.module,
            [module.basis]
        );
        const zero = algebraPresentedAlgebraModuleLinearMap(
            module.module,
            module.module,
            [algebraPresentedAlgebraModuleElementZero(module.module)]
        );
        assert.equal(
            algebraPresentedAlgebraModuleSemilinearMapEquals(
                identity,
                linearIdentity
            ),
            true
        );
        assert.equal(algebraPresentedAlgebraModuleSemilinearMapIsZero(identity),
            false);
        assert.equal(algebraPresentedAlgebraModuleSemilinearMapIsZero(zero), true);
        assert.ok(algebraPresentedAlgebraModuleElementEquals(
            algebraPresentedAlgebraModuleSemilinearMapApply(
                identity,
                module.basis
            ),
            module.basis
        ));
    });

    it('composes scalar maps and generator images functorially', () => {
        const a = algebra('x');
        const b = algebra('y');
        const c = algebra('z');
        const ma = cyclicModule(a);
        const mb = cyclicModule(b);
        const mc = cyclicModule(c);
        const ab = algebraPresentedAlgebraMap(a.algebra, b.algebra, [
            algebraQuotientElement(b.quotient, b.generator)
        ]);
        const bc = algebraPresentedAlgebraMap(b.algebra, c.algebra, [
            algebraQuotientElement(c.quotient, c.generator)
        ]);
        const ac = algebraPresentedAlgebraMap(a.algebra, c.algebra, [
            algebraQuotientElement(c.quotient, c.generator)
        ]);
        const first = algebraPresentedAlgebraModuleSemilinearMap(
            ma.module,
            mb.module,
            ab,
            [mb.basis]
        );
        const second = algebraPresentedAlgebraModuleSemilinearMap(
            mb.module,
            mc.module,
            bc,
            [mc.basis]
        );
        const composite = algebraPresentedAlgebraModuleSemilinearMapCompose(
            second,
            first
        );
        const direct = algebraPresentedAlgebraModuleSemilinearMap(
            ma.module,
            mc.module,
            ac,
            [mc.basis]
        );
        assert.equal(
            algebraPresentedAlgebraModuleSemilinearMapEquals(composite, direct),
            true
        );
    });

    it('roundtrips its schema and deterministic serialization', () => {
        const value = algebra('x');
        const module = cyclicModule(value);
        const identity = algebraPresentedAlgebraModuleSemilinearMapIdentity(
            module.module
        );
        const schema = algebraPresentedAlgebraModuleSemilinearMapSchema(
            module.module,
            module.module,
            identity.scalarMap
        );
        const normalized = schema.normalize(identity, 'identity');
        assert.equal(
            algebraPresentedAlgebraModuleSemilinearMapEquals(
                normalized,
                identity
            ),
            true
        );
        assert.equal(
            serializeAlgebraPresentedAlgebraModuleSemilinearMap(identity),
            serializeAlgebraPresentedAlgebraModuleSemilinearMap(identity)
        );
        assert.equal(
            ALGEBRA_PRESENTED_MODULE_MAP_PROFILE.ordinaryLinearSpecialization,
            'identity-algebra-map'
        );
    });

    it('rejects endpoint, arity, image, application, and composition drift', () => {
        const a = algebra('x');
        const b = algebra('y');
        const ma = cyclicModule(a);
        const mb = cyclicModule(b);
        const ab = algebraPresentedAlgebraMap(a.algebra, b.algebra, [
            algebraQuotientElement(b.quotient, b.generator)
        ]);
        assert.throws(
            () => algebraPresentedAlgebraModuleSemilinearMap(
                mb.module,
                ma.module,
                ab,
                [ma.basis]
            ),
            mapError('INVALID_ENDPOINTS')
        );
        assert.throws(
            () => algebraPresentedAlgebraModuleSemilinearMap(
                ma.module,
                mb.module,
                ab,
                []
            ),
            mapError('INVALID_GENERATOR_IMAGES')
        );
        assert.throws(
            () => algebraPresentedAlgebraModuleSemilinearMap(
                ma.module,
                mb.module,
                ab,
                [ma.basis as never]
            ),
            mapError('FOREIGN_TARGET_ELEMENT')
        );
        const map = algebraPresentedAlgebraModuleSemilinearMap(
            ma.module,
            mb.module,
            ab,
            [mb.basis]
        );
        assert.throws(
            () => algebraPresentedAlgebraModuleSemilinearMapApply(
                map,
                mb.basis as never
            ),
            mapError('FOREIGN_SOURCE_ELEMENT')
        );
        assert.throws(
            () => algebraPresentedAlgebraModuleSemilinearMapCompose(map, map),
            mapError('NON_COMPOSABLE_MAPS')
        );
        assert.throws(
            () => algebraPresentedAlgebraModuleLinearMap(
                ma.module,
                mb.module,
                [mb.basis]
            ),
            mapError('INVALID_ENDPOINTS')
        );
    });
});
