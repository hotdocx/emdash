/**
 * @file tests/emdash2_homd_curry_alias_tests.ts
 * @description Stress-tests declaration/elaboration of homd_curry-shaped alias symbols.
 */

import { describe, it, beforeEach } from 'node:test';
import assert from 'node:assert';
import {
    App, BinderMode, CatTerm, HomTerm, Icit, Lam, LamMode, ObjTerm, PiMode, Term, Var, Hole
} from '../src/types';
import { defineGlobal } from '../src/globals';
import { check, elaborate } from '../src/elaboration';
import { resetMyLambdaPi_Emdash } from '../src/stdlib';
import { areEqual } from '../src/equality';
import { emptyCtx, globalDefs, printTerm } from '../src/state';

const catdOf = (Z: Term): Term => App(Var('Catd'), Z, Icit.Expl);
const fibreOf = (Z: Term, E: Term, z: Term): Term =>
    App(App(App(Var('Fibre'), Z, Icit.Expl), E, Icit.Expl), z, Icit.Expl);
const catConstCatdOf = (Z: Term): Term => App(Var('CatConst_catd'), Z, Icit.Expl);
const functorCatdOf = (Z: Term, E: Term, D: Term): Term =>
    App(App(App(Var('Functor_catd'), Z, Icit.Expl), E, Icit.Expl), D, Icit.Expl);
const catAtOf = (Z: Term, z: Term): Term => ObjTerm(fibreOf(Z, catConstCatdOf(Z), z));
const homdTypeWithModes = (Z: Term, E: Term): Term =>
    PiMode('b0', Icit.Expl, ObjTerm(Z), b0 =>
    PiMode('e0', Icit.Expl, ObjTerm(fibreOf(Z, E, b0)), _e0 =>
    PiMode('b1', Icit.Expl, ObjTerm(Z), b1 =>
    PiMode('f', Icit.Expl, HomTerm(Z, b0, b1), _f =>
    PiMode('e1', Icit.Expl, ObjTerm(fibreOf(Z, E, b1)), _e1 =>
        catAtOf(Z, b1),
        { mode: BinderMode.Natural, controllerCat: Z }
    ), { mode: BinderMode.Natural, controllerCat: Z }
    ), { mode: BinderMode.Functorial, controllerCat: Z }
    ), { mode: BinderMode.Natural, controllerCat: Z }
    ), { mode: BinderMode.Functorial, controllerCat: Z });

const homdCatTypeWithModes = (Z: Term, E: Term): Term =>
    PiMode('b0', Icit.Expl, ObjTerm(Z), b0 =>
    PiMode('e0', Icit.Expl, ObjTerm(fibreOf(Z, E, b0)), _e0 =>
    PiMode('b1', Icit.Expl, ObjTerm(Z), b1 =>
    PiMode('f', Icit.Expl, HomTerm(Z, b0, b1), _f =>
    PiMode('e1', Icit.Expl, ObjTerm(fibreOf(Z, E, b1)), _e1 =>
        ObjTerm(fibreOf(Z, functorCatdOf(Z, E, catConstCatdOf(Z)), b1)),
        { mode: BinderMode.Natural, controllerCat: Z }
    ), { mode: BinderMode.Natural, controllerCat: Z }
    ), { mode: BinderMode.Functorial, controllerCat: Z }
    ), { mode: BinderMode.Natural, controllerCat: Z }
    ), { mode: BinderMode.Functorial, controllerCat: Z });

function mkHomdApp(head: string, Z: Term, E: Term, b0: Term, e0: Term, b1: Term, f: Term, e1: Term): Term {
    return App(
        App(
            App(
                App(
                    App(
                        App(
                            App(Var(head), Z, Icit.Expl),
                            E, Icit.Expl
                        ),
                        b0, Icit.Expl
                    ),
                    e0, Icit.Expl
                ),
                b1, Icit.Expl
            ),
            f, Icit.Expl
        ),
        e1, Icit.Expl
    );
}

function mkHomdCatApp(head: string, Z: Term, E: Term, b0: Term, e0: Term, b1: Term, f: Term, e1: Term): Term {
    return mkHomdApp(head, Z, E, b0, e0, b1, f, e1);
}

describe('Emdash2 homd_curry alias declaration', () => {
    beforeEach(() => {
        resetMyLambdaPi_Emdash();
    });

    it('declares alias_homd_ with type equal to homd_curry', () => {
        const homd = globalDefs.get('homd_curry');
        const alias = globalDefs.get('alias_homd_');
        const etaCopy = globalDefs.get('homd_curry_eta_copy');

        assert.ok(homd?.type, 'homd_curry must be declared in stdlib');
        assert.ok(alias?.type, 'alias_homd_ must be declared in stdlib');
        assert.ok(etaCopy?.type, 'homd_curry_eta_copy must be declared in stdlib');
        assert.ok(
            areEqual(homd!.type, alias!.type, emptyCtx),
            `alias_homd_ type must match homd_curry.\nhomd_curry: ${printTerm(homd!.type)}\nalias_homd_: ${printTerm(alias!.type)}`
        );
        assert.ok(
            areEqual(homd!.type, etaCopy!.type, emptyCtx),
            `homd_curry_eta_copy type must match homd_curry.\nhomd_curry: ${printTerm(homd!.type)}\neta_copy: ${printTerm(etaCopy!.type)}`
        );
    });

    it('types homd_curry, alias_homd_, and eta-copy applications to CatAt codomain', () => {
        defineGlobal('Z', CatTerm());
        const Z = Var('Z');

        const CatdZ = catdOf(Z);
        defineGlobal('E', CatdZ);
        const E = Var('E');

        defineGlobal('b0', ObjTerm(Z));
        defineGlobal('b1', ObjTerm(Z));
        const b0 = Var('b0');
        const b1 = Var('b1');

        const FibreEb0 = fibreOf(Z, E, b0);
        const FibreEb1 = fibreOf(Z, E, b1);
        defineGlobal('e0', ObjTerm(FibreEb0));
        defineGlobal('e1', ObjTerm(FibreEb1));
        const e0 = Var('e0');
        const e1 = Var('e1');

        defineGlobal('f', HomTerm(Z, b0, b1));
        const f = Var('f');

        const homdApp = mkHomdApp('homd_curry', Z, E, b0, e0, b1, f, e1);
        const aliasApp = mkHomdApp('alias_homd_', Z, E, b0, e0, b1, f, e1);
        const etaCopyApp = mkHomdApp('homd_curry_eta_copy', Z, E, b0, e0, b1, f, e1);

        const homdRes = elaborate(homdApp);
        const aliasRes = elaborate(aliasApp);
        const etaCopyRes = elaborate(etaCopyApp);
        const expectedType = catAtOf(Z, b1);

        assert.ok(
            areEqual(homdRes.type, expectedType, emptyCtx),
            `Expected homd_curry application type ${printTerm(expectedType)}, got ${printTerm(homdRes.type)}`
        );
        assert.ok(
            areEqual(aliasRes.type, expectedType, emptyCtx),
            `Expected alias_homd_ application type ${printTerm(expectedType)}, got ${printTerm(aliasRes.type)}`
        );
        assert.ok(
            areEqual(etaCopyRes.type, expectedType, emptyCtx),
            `Expected homd_curry_eta_copy application type ${printTerm(expectedType)}, got ${printTerm(etaCopyRes.type)}`
        );
        assert.ok(
            areEqual(etaCopyRes.term, homdRes.term, emptyCtx),
            `Expected eta-copy application to be convertible with homd_curry application.\neta-copy: ${printTerm(etaCopyRes.term)}\nhomd_curry: ${printTerm(homdRes.term)}`
        );
    });

    it('accepts lambda skeleton for alias_homd_ binder chain', () => {
        defineGlobal('Z', CatTerm());
        const Z = Var('Z');
        const CatdZ = catdOf(Z);
        defineGlobal('E', CatdZ);
        const E = Var('E');

        const aliasZE = App(App(Var('alias_homd_'), Z, Icit.Expl), E, Icit.Expl);

        const skeleton = Lam('b0', Icit.Expl, ObjTerm(Z), b0 =>
            Lam('e0', Icit.Expl, ObjTerm(fibreOf(Z, E, b0)), _e0 =>
            Lam('b1', Icit.Expl, ObjTerm(Z), b1 =>
            Lam('f', Icit.Expl, HomTerm(Z, b0, b1), _f =>
            Lam('e1', Icit.Expl, ObjTerm(fibreOf(Z, E, b1)), _e1 =>
                Hole('alias_homd_body')
            )))));

        const checked = check(emptyCtx, skeleton, aliasZE);
        assert.equal(checked.tag, 'Lam', 'expected elaborated lambda skeleton');
    });

    it('accepts mode-annotated lambda skeleton against explicit mode-aware Pi type', () => {
        defineGlobal('Z', CatTerm());
        const Z = Var('Z');
        const CatdZ = catdOf(Z);
        defineGlobal('E', CatdZ);
        const E = Var('E');

        const expectedModeType = homdTypeWithModes(Z, E);
        const skeleton = LamMode('b0', Icit.Expl, ObjTerm(Z), b0 =>
            LamMode('e0', Icit.Expl, ObjTerm(fibreOf(Z, E, b0)), _e0 =>
            LamMode('b1', Icit.Expl, ObjTerm(Z), b1 =>
            LamMode('f', Icit.Expl, HomTerm(Z, b0, b1), _f =>
            LamMode('e1', Icit.Expl, ObjTerm(fibreOf(Z, E, b1)), _e1 =>
                Hole('alias_homd_mode_body')
            , { mode: BinderMode.Natural, controllerCat: Z })
            , { mode: BinderMode.Natural, controllerCat: Z })
            , { mode: BinderMode.Functorial, controllerCat: Z })
            , { mode: BinderMode.Natural, controllerCat: Z })
            , { mode: BinderMode.Functorial, controllerCat: Z });

        const checked = check(emptyCtx, skeleton, expectedModeType);
        assert.equal(checked.tag, 'Lam', 'expected mode-annotated lambda skeleton to type-check');
    });

    it('rejects alias_homd_ when base arrow comes from wrong category', () => {
        defineGlobal('Z', CatTerm());
        defineGlobal('Z_bad', CatTerm());
        const Z = Var('Z');
        const Zbad = Var('Z_bad');

        const CatdZ = catdOf(Z);
        defineGlobal('E', CatdZ);
        const E = Var('E');

        defineGlobal('b0', ObjTerm(Z));
        defineGlobal('b1', ObjTerm(Z));
        const b0 = Var('b0');
        const b1 = Var('b1');

        defineGlobal('e0', ObjTerm(fibreOf(Z, E, b0)));
        defineGlobal('e1', ObjTerm(fibreOf(Z, E, b1)));
        const e0 = Var('e0');
        const e1 = Var('e1');

        defineGlobal('x_bad', ObjTerm(Zbad));
        defineGlobal('y_bad', ObjTerm(Zbad));
        const xBad = Var('x_bad');
        const yBad = Var('y_bad');
        defineGlobal('f_bad', HomTerm(Zbad, xBad, yBad));
        const fBad = Var('f_bad');

        assert.throws(
            () => elaborate(mkHomdApp('alias_homd_', Z, E, b0, e0, b1, fBad, e1)),
            /Type error|Could not solve constraints|expectedType/,
            'Expected alias_homd_ elaboration to fail for wrong arrow category'
        );
    });

    it('rejects lambda mode mismatch against expected Pi modes (b0 must be :^f)', () => {
        defineGlobal('Z', CatTerm());
        const Z = Var('Z');
        const CatdZ = catdOf(Z);
        defineGlobal('E', CatdZ);
        const E = Var('E');

        const expectedModeType = homdTypeWithModes(Z, E);
        const badSkeleton = LamMode(
            'b0',
            Icit.Expl,
            ObjTerm(Z),
            b0 => Lam('e0', Icit.Expl, ObjTerm(fibreOf(Z, E, b0)), _e0 =>
                Lam('b1', Icit.Expl, ObjTerm(Z), b1 =>
                    Lam('f', Icit.Expl, HomTerm(Z, b0, b1), _f =>
                        Lam('e1', Icit.Expl, ObjTerm(fibreOf(Z, E, b1)), _e1 =>
                            Hole('alias_homd_body_bad_mode')
                        )
                    )
                )
            ),
            { mode: BinderMode.ObjectOnly, controllerCat: Z }
        );

        assert.throws(
            () => check(emptyCtx, badSkeleton, expectedModeType),
            /Mode error/,
            'Expected lambda binder mode mismatch to be rejected'
        );
    });

    it('rejects lambda mode mismatch against expected Pi modes (e0 must be :^n)', () => {
        defineGlobal('Z', CatTerm());
        const Z = Var('Z');
        const CatdZ = catdOf(Z);
        defineGlobal('E', CatdZ);
        const E = Var('E');

        const expectedModeType = homdTypeWithModes(Z, E);
        const badSkeleton = LamMode(
            'b0',
            Icit.Expl,
            ObjTerm(Z),
            b0 => LamMode('e0', Icit.Expl, ObjTerm(fibreOf(Z, E, b0)), _e0 =>
                Lam('b1', Icit.Expl, ObjTerm(Z), b1 =>
                    Lam('f', Icit.Expl, HomTerm(Z, b0, b1), _f =>
                        Lam('e1', Icit.Expl, ObjTerm(fibreOf(Z, E, b1)), _e1 =>
                            Hole('alias_homd_body_bad_mode_e0')
                        )
                    )
                ),
                { mode: BinderMode.Functorial, controllerCat: Z }
            ),
            { mode: BinderMode.Functorial, controllerCat: Z }
        );

        assert.throws(
            () => check(emptyCtx, badSkeleton, expectedModeType),
            /Mode error/,
            'Expected natural binder mismatch to be rejected'
        );
    });

    it('rejects Hom binders whose endpoints are object-only in arrow-indexed contexts', () => {
        defineGlobal('Z', CatTerm());
        const Z = Var('Z');

        const stressType = PiMode('b0', Icit.Expl, ObjTerm(Z), b0 =>
            PiMode('b1', Icit.Expl, ObjTerm(Z), b1 =>
            PiMode('f', Icit.Expl, HomTerm(Z, b0, b1), _f =>
                CatTerm(),
                { mode: BinderMode.Natural, controllerCat: Z }
            ),
            { mode: BinderMode.ObjectOnly, controllerCat: Z }
            ),
            { mode: BinderMode.ObjectOnly, controllerCat: Z }
        );

        const stressTerm = LamMode('b0', Icit.Expl, ObjTerm(Z), b0 =>
            LamMode('b1', Icit.Expl, ObjTerm(Z), b1 =>
            LamMode('f', Icit.Expl, HomTerm(Z, b0, b1), _f =>
                CatTerm(),
                { mode: BinderMode.Natural, controllerCat: Z }
            ),
            { mode: BinderMode.ObjectOnly, controllerCat: Z }
            ),
            { mode: BinderMode.ObjectOnly, controllerCat: Z }
        );

        assert.throws(
            () => check(emptyCtx, stressTerm, stressType),
            /Mode error/,
            'Expected object-only endpoints to be rejected for Hom binders'
        );
    });

    it('declares categorical alias_homd_curry_cat with Functor_catd-nested codomain', () => {
        const cat = globalDefs.get('homd_curry_cat');
        const alias = globalDefs.get('alias_homd_curry_cat');
        const etaCopy = globalDefs.get('homd_curry_cat_eta_copy');

        assert.ok(cat?.type, 'homd_curry_cat must be declared in stdlib');
        assert.ok(alias?.type, 'alias_homd_curry_cat must be declared in stdlib');
        assert.ok(etaCopy?.type, 'homd_curry_cat_eta_copy must be declared in stdlib');
        assert.ok(
            areEqual(cat!.type, alias!.type, emptyCtx),
            `alias_homd_curry_cat type must match homd_curry_cat.\nhomd_curry_cat: ${printTerm(cat!.type)}\nalias_homd_curry_cat: ${printTerm(alias!.type)}`
        );
        assert.ok(
            areEqual(cat!.type, etaCopy!.type, emptyCtx),
            `homd_curry_cat_eta_copy type must match homd_curry_cat.\nhomd_curry_cat: ${printTerm(cat!.type)}\neta_copy: ${printTerm(etaCopy!.type)}`
        );
    });

    it('types categorical homd_curry_cat applications and eta-copy to Functor_catd fibre codomain', () => {
        defineGlobal('Z', CatTerm());
        const Z = Var('Z');

        defineGlobal('E', catdOf(Z));
        const E = Var('E');

        defineGlobal('b0', ObjTerm(Z));
        defineGlobal('b1', ObjTerm(Z));
        const b0 = Var('b0');
        const b1 = Var('b1');

        defineGlobal('e0', ObjTerm(fibreOf(Z, E, b0)));
        defineGlobal('e1', ObjTerm(fibreOf(Z, E, b1)));
        const e0 = Var('e0');
        const e1 = Var('e1');

        defineGlobal('f', HomTerm(Z, b0, b1));
        const f = Var('f');

        const catApp = mkHomdCatApp('homd_curry_cat', Z, E, b0, e0, b1, f, e1);
        const aliasApp = mkHomdCatApp('alias_homd_curry_cat', Z, E, b0, e0, b1, f, e1);
        const etaCopyApp = mkHomdCatApp('homd_curry_cat_eta_copy', Z, E, b0, e0, b1, f, e1);

        const catRes = elaborate(catApp);
        const aliasRes = elaborate(aliasApp);
        const etaCopyRes = elaborate(etaCopyApp);
        const expectedType = ObjTerm(fibreOf(Z, functorCatdOf(Z, E, catConstCatdOf(Z)), b1));

        assert.ok(
            areEqual(catRes.type, expectedType, emptyCtx),
            `Expected homd_curry_cat application type ${printTerm(expectedType)}, got ${printTerm(catRes.type)}`
        );
        assert.ok(
            areEqual(aliasRes.type, expectedType, emptyCtx),
            `Expected alias_homd_curry_cat application type ${printTerm(expectedType)}, got ${printTerm(aliasRes.type)}`
        );
        assert.ok(
            areEqual(etaCopyRes.type, expectedType, emptyCtx),
            `Expected homd_curry_cat_eta_copy application type ${printTerm(expectedType)}, got ${printTerm(etaCopyRes.type)}`
        );
        assert.ok(
            areEqual(etaCopyRes.term, catRes.term, emptyCtx),
            `Expected categorical eta-copy application to be convertible with homd_curry_cat.\neta-copy: ${printTerm(etaCopyRes.term)}\nhomd_curry_cat: ${printTerm(catRes.term)}`
        );
    });

    it('accepts mode-annotated categorical eta skeleton against explicit Functor_catd-based Pi type', () => {
        defineGlobal('Z', CatTerm());
        const Z = Var('Z');
        defineGlobal('E', catdOf(Z));
        const E = Var('E');

        const expectedModeType = homdCatTypeWithModes(Z, E);
        const skeleton = LamMode('b0', Icit.Expl, ObjTerm(Z), b0 =>
            LamMode('e0', Icit.Expl, ObjTerm(fibreOf(Z, E, b0)), _e0 =>
            LamMode('b1', Icit.Expl, ObjTerm(Z), b1 =>
            LamMode('f', Icit.Expl, HomTerm(Z, b0, b1), _f =>
            LamMode('e1', Icit.Expl, ObjTerm(fibreOf(Z, E, b1)), _e1 =>
                Hole('alias_homd_cat_mode_body')
            , { mode: BinderMode.Natural, controllerCat: Z })
            , { mode: BinderMode.Natural, controllerCat: Z })
            , { mode: BinderMode.Functorial, controllerCat: Z })
            , { mode: BinderMode.Natural, controllerCat: Z })
            , { mode: BinderMode.Functorial, controllerCat: Z });

        const checked = check(emptyCtx, skeleton, expectedModeType);
        assert.equal(checked.tag, 'Lam', 'expected mode-annotated categorical lambda skeleton to type-check');
    });
});
