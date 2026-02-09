/**
 * @file tests/emdash2_internalized_category_layer_tests.ts
 * @description Internalized category-layer tests (Cat_cat/Catd_cat/Functord_cat/Transf_cat/Transfd_cat).
 */

import { describe, it, beforeEach } from 'node:test';
import assert from 'node:assert';
import {
    App, BinderMode, CatTerm, FMap0Term, HomTerm, Icit, LamMode, ObjTerm, PiMode, TDApp1Term, TApp1FApp0Term, Term, Var
} from '../src/types';
import { defineGlobal } from '../src/globals';
import { elaborate, check } from '../src/elaboration';
import { resetMyLambdaPi_Emdash } from '../src/stdlib';
import { areEqual } from '../src/equality';
import { emptyCtx, globalDefs, printTerm } from '../src/state';
import { normalize } from '../src/reduction';

const catdOf = (Z: Term): Term => App(Var('Catd'), Z, Icit.Expl);
const catdCatOf = (Z: Term): Term => App(Var('Catd_cat'), Z, Icit.Expl);
const functorCatOf = (A: Term, B: Term): Term => App(App(Var('Functor_cat'), A, Icit.Expl), B, Icit.Expl);
const functordCatOf = (Z: Term, E: Term, D: Term): Term =>
    App(App(App(Var('Functord_cat'), Z, Icit.Expl), E, Icit.Expl), D, Icit.Expl);
const transfCatOf = (A: Term, B: Term, F: Term, G: Term): Term =>
    App(App(App(App(Var('Transf_cat'), A, Icit.Expl), B, Icit.Expl), F, Icit.Expl), G, Icit.Expl);
const transfdCatOf = (Z: Term, E: Term, D: Term, FF: Term, GG: Term): Term =>
    App(App(App(App(App(Var('Transfd_cat'), Z, Icit.Expl), E, Icit.Expl), D, Icit.Expl), FF, Icit.Expl), GG, Icit.Expl);
const fibreOf = (Z: Term, E: Term, z: Term): Term =>
    App(App(App(Var('Fibre'), Z, Icit.Expl), E, Icit.Expl), z, Icit.Expl);
const fdapp0Of = (Z: Term, E: Term, D: Term, FF: Term, z: Term, e: Term): Term =>
    App(App(App(App(App(App(Var('fdapp0'), Z, Icit.Expl), E, Icit.Expl), D, Icit.Expl), FF, Icit.Expl), z, Icit.Expl), e, Icit.Expl);
const homdCurryOf = (Z: Term, E: Term, b0: Term, e0: Term, b1: Term, f: Term, e1: Term): Term =>
    App(
        App(
            App(
                App(
                    App(
                        App(
                            App(Var('homd_curry'), Z, Icit.Expl),
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

describe('Emdash2 internalized category layer', () => {
    beforeEach(() => {
        resetMyLambdaPi_Emdash();
    });

    it('declares internalized category objects and reduces Obj as expected', () => {
        for (const name of ['Cat_cat', 'Catd_cat', 'Functord_cat', 'Transf_cat', 'Transfd_cat']) {
            assert.ok(globalDefs.get(name), `Missing stdlib global: ${name}`);
        }

        const objCat = normalize(ObjTerm(Var('Cat_cat')), emptyCtx);
        assert.ok(
            areEqual(objCat, CatTerm(), emptyCtx),
            `Expected Obj(Cat_cat) ≡ Cat, got ${printTerm(objCat)}`
        );

        defineGlobal('Z', ObjTerm(Var('Cat_cat')));
        const Z = Var('Z');
        const objCatd = normalize(ObjTerm(catdCatOf(Z)), emptyCtx);
        const expectedObjCatd = catdOf(Z);
        assert.ok(
            areEqual(objCatd, expectedObjCatd, emptyCtx),
            `Expected Obj(Catd_cat Z) ≡ Catd Z, got ${printTerm(objCatd)}`
        );
    });

    it('supports ordinary internalized context A,B,F,G,eps and elaborates eps_(f)', () => {
        defineGlobal('A', ObjTerm(Var('Cat_cat')));
        defineGlobal('B', ObjTerm(Var('Cat_cat')));
        const A = Var('A');
        const B = Var('B');

        defineGlobal('F', ObjTerm(functorCatOf(A, B)));
        defineGlobal('G', ObjTerm(functorCatOf(A, B)));
        const F = Var('F');
        const G = Var('G');

        defineGlobal('eps', ObjTerm(transfCatOf(A, B, F, G)));
        const eps = Var('eps');

        defineGlobal('X', ObjTerm(A));
        defineGlobal('Y', ObjTerm(A));
        const X = Var('X');
        const Y = Var('Y');

        defineGlobal('f', HomTerm(A, X, Y));
        const f = Var('f');

        const term = TApp1FApp0Term(eps, f, A, B, F, G, X, Y);
        const res = elaborate(term);
        const expectedType = HomTerm(B, FMap0Term(F, X, A, B), FMap0Term(G, Y, A, B));
        assert.ok(
            areEqual(res.type, expectedType, emptyCtx),
            `Expected ${printTerm(expectedType)}, got ${printTerm(res.type)}`
        );
    });

    it('supports displayed internalized context and elaborates eps_(sigma)', () => {
        defineGlobal('Z', ObjTerm(Var('Cat_cat')));
        const Z = Var('Z');

        defineGlobal('E', ObjTerm(catdCatOf(Z)));
        defineGlobal('D', ObjTerm(catdCatOf(Z)));
        const E = Var('E');
        const D = Var('D');

        defineGlobal('FF', ObjTerm(functordCatOf(Z, E, D)));
        defineGlobal('GG', ObjTerm(functordCatOf(Z, E, D)));
        const FF = Var('FF');
        const GG = Var('GG');

        defineGlobal('epsd', ObjTerm(transfdCatOf(Z, E, D, FF, GG)));
        const epsd = Var('epsd');

        defineGlobal('z', ObjTerm(Z));
        defineGlobal('z_prime', ObjTerm(Z));
        const z = Var('z');
        const zPrime = Var('z_prime');

        defineGlobal('f', HomTerm(Z, z, zPrime));
        const f = Var('f');

        defineGlobal('e', ObjTerm(fibreOf(Z, E, z)));
        defineGlobal('e_prime', ObjTerm(fibreOf(Z, E, zPrime)));
        const e = Var('e');
        const ePrime = Var('e_prime');

        defineGlobal('sigma', ObjTerm(homdCurryOf(Z, E, z, e, zPrime, f, ePrime)));
        const sigma = Var('sigma');

        const term = TDApp1Term(epsd, sigma, Z, E, D, FF, GG, z, e, zPrime, f, ePrime);
        const res = elaborate(term);
        const expectedType = ObjTerm(
            homdCurryOf(
                Z, D,
                z,
                fdapp0Of(Z, E, D, FF, z, e),
                zPrime,
                f,
                fdapp0Of(Z, E, D, GG, zPrime, ePrime)
            )
        );

        assert.ok(
            areEqual(res.type, expectedType, emptyCtx),
            `Expected ${printTerm(expectedType)}, got ${printTerm(res.type)}`
        );
    });

    it('accepts plain/object-level binder for F_BA in hom_int-style contexts', () => {
        defineGlobal('A', ObjTerm(Var('Cat_cat')));
        defineGlobal('B', ObjTerm(Var('Cat_cat')));
        const A = Var('A');
        const B = Var('B');

        const F_BA_Type = ObjTerm(functorCatOf(B, A));
        const expectedType = PiMode(
            'F_BA',
            Icit.Expl,
            F_BA_Type,
            _F_BA => CatTerm(),
            { mode: BinderMode.ObjectOnly }
        );
        const term = LamMode(
            'F_BA',
            Icit.Expl,
            F_BA_Type,
            _F_BA => CatTerm(),
            { mode: BinderMode.ObjectOnly }
        );

        const checked = check(emptyCtx, term, expectedType);
        assert.equal(checked.tag, 'Lam');
    });
});
