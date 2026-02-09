/**
 * @file tests/emdash2_functor_transfor_tests.ts
 * @description emdash2-oriented functor/transfor elaboration tests (ordinary + minimal displayed shell).
 */

import {
    Term, Var, Icit, CatTerm, ObjTerm, HomTerm, FunctorTypeTerm, NatTransTypeTerm, FMap0Term, TApp1FApp0Term, App, BinderMode
} from '../src/types';
import { describe, it, beforeEach } from 'node:test';
import assert from 'node:assert';
import { defineGlobal } from '../src/globals';
import { resetMyLambdaPi_Emdash } from '../src/stdlib';
import { elaborate } from '../src/elaboration';
import { areEqual } from '../src/equality';
import { emptyCtx, extendCtx, lookupCtx, printTerm } from '../src/state';

describe('Emdash2 Functor/Transfor Elaboration', () => {
    beforeEach(() => {
        resetMyLambdaPi_Emdash();
    });

    it('stores binder mode/controller metadata in context bindings', () => {
        defineGlobal('A_meta', CatTerm());
        const A = Var('A_meta');

        defineGlobal('x_meta', ObjTerm(A));
        const x = Var('x_meta');

        const ctx = extendCtx(emptyCtx, 'x_meta', ObjTerm(A), Icit.Expl, x, BinderMode.Functorial, A);
        const b = lookupCtx(ctx, 'x_meta');
        assert.ok(b, 'binding should exist');
        assert.equal(b!.mode, BinderMode.Functorial);
        assert.ok(b!.controllerCat && areEqual(b!.controllerCat, A, emptyCtx));
    });

    it('types tapp1_fapp0 (ordinary off-diagonal transfor component)', () => {
        defineGlobal('A', CatTerm());
        defineGlobal('B', CatTerm());
        const A = Var('A');
        const B = Var('B');

        defineGlobal('X', ObjTerm(A));
        defineGlobal('Y', ObjTerm(A));
        const X = Var('X');
        const Y = Var('Y');

        defineGlobal('F', FunctorTypeTerm(A, B));
        defineGlobal('G', FunctorTypeTerm(A, B));
        const F = Var('F');
        const G = Var('G');

        defineGlobal('a', HomTerm(A, X, Y));
        const a = Var('a');

        defineGlobal('eps', NatTransTypeTerm(A, B, F, G));
        const eps = Var('eps');

        const term = TApp1FApp0Term(eps, a);
        const result = elaborate(term);

        const expectedType = HomTerm(B, FMap0Term(F, X, A, B), FMap0Term(G, Y, A, B));
        assert.ok(
            areEqual(result.type, expectedType, emptyCtx),
            `Expected type ${printTerm(expectedType)} but got ${printTerm(result.type)}`
        );
    });

    it('rejects tapp1_fapp0 when morphism is in the wrong source category', () => {
        defineGlobal('A', CatTerm());
        defineGlobal('B', CatTerm());
        const A = Var('A');
        const B = Var('B');

        defineGlobal('X', ObjTerm(A));
        defineGlobal('Y', ObjTerm(A));
        defineGlobal('BX', ObjTerm(B));
        defineGlobal('BY', ObjTerm(B));
        const BX = Var('BX');
        const BY = Var('BY');

        defineGlobal('F', FunctorTypeTerm(A, B));
        defineGlobal('G', FunctorTypeTerm(A, B));
        const F = Var('F');
        const G = Var('G');

        defineGlobal('b_arrow', HomTerm(B, BX, BY));
        const bArrow = Var('b_arrow');

        defineGlobal('eps', NatTransTypeTerm(A, B, F, G));
        const eps = Var('eps');

        assert.throws(
            () => elaborate(TApp1FApp0Term(eps, bArrow)),
            /Type error|Could not solve constraints|expectedType/,
            'Expected tapp1_fapp0 elaboration to fail with wrong morphism category'
        );
    });

    it('types minimal displayed shell: fdapp0 and tdapp0_fapp0', () => {
        defineGlobal('Z', CatTerm());
        const Z = Var('Z');

        const CatdZ = App(Var('Catd'), Z, Icit.Expl);
        defineGlobal('E', CatdZ);
        defineGlobal('D', CatdZ);
        const E = Var('E');
        const D = Var('D');

        defineGlobal('z', ObjTerm(Z));
        const z = Var('z');

        const FibreEz = App(App(App(Var('Fibre'), Z, Icit.Expl), E, Icit.Expl), z, Icit.Expl);
        const FibreDz = App(App(App(Var('Fibre'), Z, Icit.Expl), D, Icit.Expl), z, Icit.Expl);
        defineGlobal('e', ObjTerm(FibreEz));
        const e = Var('e');

        const FunctordED = App(App(App(Var('Functord'), Z, Icit.Expl), E, Icit.Expl), D, Icit.Expl);
        defineGlobal('FF', FunctordED);
        defineGlobal('GG', FunctordED);
        const FF = Var('FF');
        const GG = Var('GG');

        const fdapp0FFze = App(App(App(App(App(App(Var('fdapp0'), Z, Icit.Expl), E, Icit.Expl), D, Icit.Expl), FF, Icit.Expl), z, Icit.Expl), e, Icit.Expl);
        const fdapp0GGze = App(App(App(App(App(App(Var('fdapp0'), Z, Icit.Expl), E, Icit.Expl), D, Icit.Expl), GG, Icit.Expl), z, Icit.Expl), e, Icit.Expl);

        const fdapp0Res = elaborate(fdapp0FFze);
        assert.ok(
            areEqual(fdapp0Res.type, ObjTerm(FibreDz), emptyCtx),
            `Expected fdapp0 type Obj(Fibre Z D z), got ${printTerm(fdapp0Res.type)}`
        );

        const TransfdED = App(App(App(App(App(Var('Transfd'), Z, Icit.Expl), E, Icit.Expl), D, Icit.Expl), FF, Icit.Expl), GG, Icit.Expl);
        defineGlobal('epsd', TransfdED);
        const epsd = Var('epsd');

        const tdapp0 = App(
            App(
                App(
                    App(
                        App(
                            App(
                                App(Var('tdapp0_fapp0'), Z, Icit.Expl),
                                E, Icit.Expl
                            ),
                            D, Icit.Expl
                        ),
                        FF, Icit.Expl
                    ),
                    GG, Icit.Expl
                ),
                z, Icit.Expl
            ),
            e, Icit.Expl
        );
        const tdapp0Term = App(tdapp0, epsd, Icit.Expl);

        const tdapp0Res = elaborate(tdapp0Term);
        const expectedTdType = HomTerm(FibreDz, fdapp0FFze, fdapp0GGze);
        assert.ok(
            areEqual(tdapp0Res.type, expectedTdType, emptyCtx),
            `Expected tdapp0_fapp0 type ${printTerm(expectedTdType)}, got ${printTerm(tdapp0Res.type)}`
        );
    });
});

