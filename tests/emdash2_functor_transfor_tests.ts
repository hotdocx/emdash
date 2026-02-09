/**
 * @file tests/emdash2_functor_transfor_tests.ts
 * @description emdash2-oriented functor/transfor elaboration tests (ordinary + minimal displayed shell).
 */

import {
    Term, Var, Icit, CatTerm, ObjTerm, HomTerm, FunctorTypeTerm, NatTransTypeTerm, FMap0Term, FMap1Term, TApp1FApp0Term, App, BinderMode, FDApp1Term, TDApp1Term, LamMode, PiMode
} from '../src/types';
import { describe, it, beforeEach } from 'node:test';
import assert from 'node:assert';
import { defineGlobal } from '../src/globals';
import { resetMyLambdaPi_Emdash } from '../src/stdlib';
import { elaborate } from '../src/elaboration';
import { areEqual } from '../src/equality';
import { emptyCtx, extendCtx, lookupCtx, printTerm } from '../src/state';
import { check } from '../src/elaboration';
import { normalize } from '../src/reduction';

const catdOf = (Z: Term): Term => App(Var('Catd'), Z, Icit.Expl);
const fibreOf = (Z: Term, E: Term, z: Term): Term =>
    App(App(App(Var('Fibre'), Z, Icit.Expl), E, Icit.Expl), z, Icit.Expl);
const functordOf = (Z: Term, E: Term, D: Term): Term =>
    App(App(App(Var('Functord'), Z, Icit.Expl), E, Icit.Expl), D, Icit.Expl);
const functordCatOf = (Z: Term, E: Term, D: Term): Term =>
    App(App(App(Var('Functord_cat'), Z, Icit.Expl), E, Icit.Expl), D, Icit.Expl);
const transfdOf = (Z: Term, E: Term, D: Term, FF: Term, GG: Term): Term =>
    App(App(App(App(App(Var('Transfd'), Z, Icit.Expl), E, Icit.Expl), D, Icit.Expl), FF, Icit.Expl), GG, Icit.Expl);
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
const fdapp0Of = (Z: Term, E: Term, D: Term, FF: Term, z: Term, e: Term): Term =>
    App(App(App(App(App(App(Var('fdapp0'), Z, Icit.Expl), E, Icit.Expl), D, Icit.Expl), FF, Icit.Expl), z, Icit.Expl), e, Icit.Expl);
const composeOf = (C: Term, X: Term, Y: Term, Z: Term, g: Term, f: Term): Term =>
    App(
        App(
            App(
                App(
                    App(
                        App(Var('compose_morph'), C, Icit.Impl),
                        X, Icit.Impl
                    ),
                    Y, Icit.Impl
                ),
                Z, Icit.Impl
            ),
            g, Icit.Expl
        ),
        f, Icit.Expl
    );

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

    it('reduces strict functoriality composition: F(f) ∘ F(g) ↪ F(f ∘ g)', () => {
        defineGlobal('A', CatTerm());
        defineGlobal('B', CatTerm());
        const A = Var('A');
        const B = Var('B');

        defineGlobal('W', ObjTerm(A));
        defineGlobal('X', ObjTerm(A));
        defineGlobal('Y', ObjTerm(A));
        const W = Var('W');
        const X = Var('X');
        const Y = Var('Y');

        defineGlobal('F', FunctorTypeTerm(A, B));
        const F = Var('F');

        defineGlobal('g', HomTerm(A, W, X));
        defineGlobal('f', HomTerm(A, X, Y));
        const g = Var('g');
        const f = Var('f');

        const FW = FMap0Term(F, W, A, B);
        const FX = FMap0Term(F, X, A, B);
        const FY = FMap0Term(F, Y, A, B);
        const FgArrow = FMap1Term(F, g, A, B, W, X);
        const FfArrow = FMap1Term(F, f, A, B, X, Y);

        const lhs = composeOf(B, FW, FX, FY, FfArrow, FgArrow);
        const fg = composeOf(A, W, X, Y, f, g);
        const rhs = FMap1Term(F, fg, A, B, W, Y);

        const lhsElab = elaborate(lhs);
        const rhsElab = elaborate(rhs);
        const lhsNf = normalize(lhsElab.term, emptyCtx);
        const rhsNf = normalize(rhsElab.term, emptyCtx);

        assert.ok(
            areEqual(lhsNf, rhsNf, emptyCtx),
            `Expected strict functoriality reduction.\nLHS_nf: ${printTerm(lhsNf)}\nRHS_nf: ${printTerm(rhsNf)}`
        );
    });

    it('reduces strict accumulation (postcomposition): G(g) ∘ ϵ_(f) ↪ ϵ_(g ∘ f)', () => {
        defineGlobal('A', CatTerm());
        defineGlobal('B', CatTerm());
        const A = Var('A');
        const B = Var('B');

        defineGlobal('X', ObjTerm(A));
        defineGlobal('Y', ObjTerm(A));
        defineGlobal('Z', ObjTerm(A));
        const X = Var('X');
        const Y = Var('Y');
        const Z = Var('Z');

        defineGlobal('F', FunctorTypeTerm(A, B));
        defineGlobal('G', FunctorTypeTerm(A, B));
        const F = Var('F');
        const G = Var('G');

        defineGlobal('eps', NatTransTypeTerm(A, B, F, G));
        const eps = Var('eps');

        defineGlobal('f', HomTerm(A, X, Y));
        defineGlobal('g', HomTerm(A, Y, Z));
        const f = Var('f');
        const g = Var('g');

        const FX = FMap0Term(F, X, A, B);
        const GY = FMap0Term(G, Y, A, B);
        const GZ = FMap0Term(G, Z, A, B);
        const eps_f = TApp1FApp0Term(eps, f, A, B, F, G, X, Y);
        const Gg = FMap1Term(G, g, A, B, Y, Z);

        const lhs = composeOf(B, FX, GY, GZ, Gg, eps_f);
        const gf = composeOf(A, X, Y, Z, g, f);
        const rhs = TApp1FApp0Term(eps, gf, A, B, F, G, X, Z);

        const lhsElab = elaborate(lhs);
        const rhsElab = elaborate(rhs);
        const lhsNf = normalize(lhsElab.term, emptyCtx);
        const rhsNf = normalize(rhsElab.term, emptyCtx);

        assert.ok(
            areEqual(lhsNf, rhsNf, emptyCtx),
            `Expected postcomposition accumulation reduction.\nLHS_nf: ${printTerm(lhsNf)}\nRHS_nf: ${printTerm(rhsNf)}`
        );
    });

    it('reduces strict accumulation (precomposition): ϵ_(f) ∘ F(g) ↪ ϵ_(f ∘ g)', () => {
        defineGlobal('A', CatTerm());
        defineGlobal('B', CatTerm());
        const A = Var('A');
        const B = Var('B');

        defineGlobal('W', ObjTerm(A));
        defineGlobal('X', ObjTerm(A));
        defineGlobal('Y', ObjTerm(A));
        const W = Var('W');
        const X = Var('X');
        const Y = Var('Y');

        defineGlobal('F', FunctorTypeTerm(A, B));
        defineGlobal('G', FunctorTypeTerm(A, B));
        const F = Var('F');
        const G = Var('G');

        defineGlobal('eps', NatTransTypeTerm(A, B, F, G));
        const eps = Var('eps');

        defineGlobal('g', HomTerm(A, W, X));
        defineGlobal('f', HomTerm(A, X, Y));
        const g = Var('g');
        const f = Var('f');

        const FW = FMap0Term(F, W, A, B);
        const FX = FMap0Term(F, X, A, B);
        const GY = FMap0Term(G, Y, A, B);
        const eps_f = TApp1FApp0Term(eps, f, A, B, F, G, X, Y);
        const Fg = FMap1Term(F, g, A, B, W, X);

        const lhs = composeOf(B, FW, FX, GY, eps_f, Fg);
        const fg = composeOf(A, W, X, Y, f, g);
        const rhs = TApp1FApp0Term(eps, fg, A, B, F, G, W, Y);

        const lhsElab = elaborate(lhs);
        const rhsElab = elaborate(rhs);
        const lhsNf = normalize(lhsElab.term, emptyCtx);
        const rhsNf = normalize(rhsElab.term, emptyCtx);

        assert.ok(
            areEqual(lhsNf, rhsNf, emptyCtx),
            `Expected precomposition accumulation reduction.\nLHS_nf: ${printTerm(lhsNf)}\nRHS_nf: ${printTerm(rhsNf)}`
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

    it('types displayed off-diagonal functor action fdapp1_fapp0 (FF1[sigma])', () => {
        defineGlobal('Z', CatTerm());
        const Z = Var('Z');

        const CatdZ = catdOf(Z);
        defineGlobal('E', CatdZ);
        defineGlobal('D', CatdZ);
        const E = Var('E');
        const D = Var('D');

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

        defineGlobal('FF', functordOf(Z, E, D));
        const FF = Var('FF');

        const term = FDApp1Term(FF, sigma, Z, E, D, z, e, zPrime, f, ePrime);
        const result = elaborate(term);

        const ffAtZE = fdapp0Of(Z, E, D, FF, z, e);
        const ffAtZPrimeEPrime = fdapp0Of(Z, E, D, FF, zPrime, ePrime);
        const expectedType = ObjTerm(homdCurryOf(Z, D, z, ffAtZE, zPrime, f, ffAtZPrimeEPrime));
        const expectedHead = App(
            App(
                App(
                    App(
                        App(
                            App(
                                App(
                                    App(
                                        App(Var('fdapp1_fapp0'), Z, Icit.Expl),
                                        E, Icit.Expl
                                    ),
                                    D, Icit.Expl
                                ),
                                FF, Icit.Expl
                            ),
                            z, Icit.Expl
                        ),
                        e, Icit.Expl
                    ),
                    zPrime, Icit.Expl
                ),
                f, Icit.Expl
            ),
            ePrime, Icit.Expl
        );
        const expectedTerm = App(expectedHead, sigma, Icit.Expl);

        assert.ok(
            areEqual(result.type, expectedType, emptyCtx),
            `Expected fdapp1_fapp0 type ${printTerm(expectedType)}, got ${printTerm(result.type)}`
        );
        assert.ok(
            areEqual(result.term, expectedTerm, emptyCtx),
            `Expected fdapp1_fapp0 elaboration to canonical head.\nExpected: ${printTerm(expectedTerm)}\nGot: ${printTerm(result.term)}`
        );
    });

    it('types displayed off-diagonal transfor component tdapp1_fapp0 (eps_(sigma))', () => {
        defineGlobal('Z', CatTerm());
        const Z = Var('Z');

        const CatdZ = catdOf(Z);
        defineGlobal('E', CatdZ);
        defineGlobal('D', CatdZ);
        const E = Var('E');
        const D = Var('D');

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

        defineGlobal('FF', functordOf(Z, E, D));
        defineGlobal('GG', functordOf(Z, E, D));
        const FF = Var('FF');
        const GG = Var('GG');

        defineGlobal('epsd', transfdOf(Z, E, D, FF, GG));
        const epsd = Var('epsd');

        const term = TDApp1Term(epsd, sigma, Z, E, D, FF, GG, z, e, zPrime, f, ePrime);
        const result = elaborate(term);

        const ffAtZE = fdapp0Of(Z, E, D, FF, z, e);
        const ggAtZPrimeEPrime = fdapp0Of(Z, E, D, GG, zPrime, ePrime);
        const expectedType = ObjTerm(homdCurryOf(Z, D, z, ffAtZE, zPrime, f, ggAtZPrimeEPrime));

        assert.ok(
            areEqual(result.type, expectedType, emptyCtx),
            `Expected tdapp1_fapp0 type ${printTerm(expectedType)}, got ${printTerm(result.type)}`
        );
    });

    it('reduces displayed strict vertical composition: (η ∘ ϵ)_(Y,V) ↪ η_(Y,V) ∘ ϵ_(Y,V)', () => {
        defineGlobal('Z', CatTerm());
        const Z = Var('Z');

        const CatdZ = catdOf(Z);
        defineGlobal('E', CatdZ);
        defineGlobal('D', CatdZ);
        const E = Var('E');
        const D = Var('D');

        defineGlobal('Y', ObjTerm(Z));
        const Y = Var('Y');
        defineGlobal('V', ObjTerm(fibreOf(Z, E, Y)));
        const V = Var('V');

        defineGlobal('FF', functordOf(Z, E, D));
        defineGlobal('GG', functordOf(Z, E, D));
        defineGlobal('HH', functordOf(Z, E, D));
        const FF = Var('FF');
        const GG = Var('GG');
        const HH = Var('HH');

        defineGlobal('epsd', transfdOf(Z, E, D, FF, GG));
        defineGlobal('etad', transfdOf(Z, E, D, GG, HH));
        const epsd = Var('epsd');
        const etad = Var('etad');

        const functordCat = functordCatOf(Z, E, D);
        const compEtaEps = composeOf(functordCat, FF, GG, HH, etad, epsd);

        const tdHeadFFHH = App(
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
                    HH, Icit.Expl
                ),
                Y, Icit.Expl
            ),
            V, Icit.Expl
        );
        const tdHeadGGHH = App(
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
                        GG, Icit.Expl
                    ),
                    HH, Icit.Expl
                ),
                Y, Icit.Expl
            ),
            V, Icit.Expl
        );
        const tdHeadFFGG = App(
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
                Y, Icit.Expl
            ),
            V, Icit.Expl
        );

        const lhs = App(tdHeadFFHH, compEtaEps, Icit.Expl);

        const fdFF = fdapp0Of(Z, E, D, FF, Y, V);
        const fdGG = fdapp0Of(Z, E, D, GG, Y, V);
        const fdHH = fdapp0Of(Z, E, D, HH, Y, V);
        const rhs = composeOf(
            fibreOf(Z, D, Y),
            fdFF,
            fdGG,
            fdHH,
            App(tdHeadGGHH, etad, Icit.Expl),
            App(tdHeadFFGG, epsd, Icit.Expl)
        );

        const lhsElab = elaborate(lhs);
        const rhsElab = elaborate(rhs);
        const lhsNf = normalize(lhsElab.term, emptyCtx);
        const rhsNf = normalize(rhsElab.term, emptyCtx);

        assert.ok(
            areEqual(lhsNf, rhsNf, emptyCtx),
            `Expected displayed strict vertical reduction.\nLHS_nf: ${printTerm(lhsNf)}\nRHS_nf: ${printTerm(rhsNf)}`
        );
    });

    it('rejects fdapp1_fapp0 when the base arrow is in the wrong category', () => {
        defineGlobal('Z', CatTerm());
        defineGlobal('Z_bad', CatTerm());
        const Z = Var('Z');
        const Zbad = Var('Z_bad');

        const CatdZ = catdOf(Z);
        defineGlobal('E', CatdZ);
        defineGlobal('D', CatdZ);
        const E = Var('E');
        const D = Var('D');

        defineGlobal('z', ObjTerm(Z));
        defineGlobal('z_prime', ObjTerm(Z));
        const z = Var('z');
        const zPrime = Var('z_prime');

        defineGlobal('e', ObjTerm(fibreOf(Z, E, z)));
        defineGlobal('e_prime', ObjTerm(fibreOf(Z, E, zPrime)));
        const e = Var('e');
        const ePrime = Var('e_prime');

        defineGlobal('f_ok', HomTerm(Z, z, zPrime));
        const fOk = Var('f_ok');
        defineGlobal('sigma', ObjTerm(homdCurryOf(Z, E, z, e, zPrime, fOk, ePrime)));
        const sigma = Var('sigma');

        defineGlobal('x_bad', ObjTerm(Zbad));
        defineGlobal('y_bad', ObjTerm(Zbad));
        const xBad = Var('x_bad');
        const yBad = Var('y_bad');
        defineGlobal('f_bad', HomTerm(Zbad, xBad, yBad));
        const fBad = Var('f_bad');

        defineGlobal('FF', functordOf(Z, E, D));
        const FF = Var('FF');

        assert.throws(
            () => elaborate(FDApp1Term(FF, sigma, Z, E, D, z, e, zPrime, fBad, ePrime)),
            /Type error|Could not solve constraints|Mode error|expectedType/,
            'Expected fdapp1_fapp0 elaboration to fail when base arrow category mismatches'
        );
    });

    it('enforces functorial base-object mode for fdapp1_fapp0 context', () => {
        defineGlobal('Z', CatTerm());
        const Z = Var('Z');
        const CatdZ = catdOf(Z);
        defineGlobal('E', CatdZ);
        defineGlobal('D', CatdZ);
        const E = Var('E');
        const D = Var('D');

        defineGlobal('FF', functordOf(Z, E, D));
        const FF = Var('FF');

        const expectedType = PiMode('z', Icit.Expl, ObjTerm(Z), z =>
            PiMode('e', Icit.Expl, ObjTerm(fibreOf(Z, E, z)), e =>
            PiMode('z_prime', Icit.Expl, ObjTerm(Z), zPrime =>
            PiMode('f', Icit.Expl, HomTerm(Z, z, zPrime), f =>
            PiMode('e_prime', Icit.Expl, ObjTerm(fibreOf(Z, E, zPrime)), ePrime =>
            PiMode('sigma', Icit.Expl, ObjTerm(homdCurryOf(Z, E, z, e, zPrime, f, ePrime)), _sigma =>
                ObjTerm(homdCurryOf(Z, D, z, fdapp0Of(Z, E, D, FF, z, e), zPrime, f, fdapp0Of(Z, E, D, FF, zPrime, ePrime))),
                { mode: BinderMode.Functorial, controllerCat: homdCurryOf(Z, E, z, e, zPrime, f, ePrime) }
            ), { mode: BinderMode.Natural, controllerCat: Z }
            ), { mode: BinderMode.Natural, controllerCat: Z }
            ), { mode: BinderMode.Natural, controllerCat: Z }
            ), { mode: BinderMode.Functorial, controllerCat: Z }
            ), { mode: BinderMode.ObjectOnly, controllerCat: Z }
        );

        const badTerm = LamMode('z', Icit.Expl, ObjTerm(Z), z =>
            LamMode('e', Icit.Expl, ObjTerm(fibreOf(Z, E, z)), e =>
            LamMode('z_prime', Icit.Expl, ObjTerm(Z), zPrime =>
            LamMode('f', Icit.Expl, HomTerm(Z, z, zPrime), f =>
            LamMode('e_prime', Icit.Expl, ObjTerm(fibreOf(Z, E, zPrime)), ePrime =>
            LamMode('sigma', Icit.Expl, ObjTerm(homdCurryOf(Z, E, z, e, zPrime, f, ePrime)), sigma =>
                FDApp1Term(FF, sigma, Z, E, D, z, e, zPrime, f, ePrime),
                { mode: BinderMode.Functorial, controllerCat: homdCurryOf(Z, E, z, e, zPrime, f, ePrime) }
            ), { mode: BinderMode.Natural, controllerCat: Z }
            ), { mode: BinderMode.Natural, controllerCat: Z }
            ), { mode: BinderMode.Natural, controllerCat: Z }
            ), { mode: BinderMode.Functorial, controllerCat: Z }
            ), { mode: BinderMode.ObjectOnly, controllerCat: Z }
        );

        assert.throws(
            () => check(emptyCtx, badTerm, expectedType),
            /Mode error/,
            'Expected fdapp1_fapp0 elaboration to reject object-only z in arrow-indexed context'
        );
    });
});
