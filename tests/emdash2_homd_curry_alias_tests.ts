/**
 * @file tests/emdash2_homd_curry_alias_tests.ts
 * @description Stress-tests declaration/elaboration of homd_curry-shaped alias symbols.
 */

import { describe, it, beforeEach } from 'node:test';
import assert from 'node:assert';
import {
    App, CatTerm, HomTerm, Icit, Lam, ObjTerm, Term, Var, Hole
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
const catAtOf = (Z: Term, z: Term): Term => ObjTerm(fibreOf(Z, catConstCatdOf(Z), z));

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

describe('Emdash2 homd_curry alias declaration', () => {
    beforeEach(() => {
        resetMyLambdaPi_Emdash();
    });

    it('declares alias_homd_ with type equal to homd_curry', () => {
        const homd = globalDefs.get('homd_curry');
        const alias = globalDefs.get('alias_homd_');

        assert.ok(homd?.type, 'homd_curry must be declared in stdlib');
        assert.ok(alias?.type, 'alias_homd_ must be declared in stdlib');
        assert.ok(
            areEqual(homd!.type, alias!.type, emptyCtx),
            `alias_homd_ type must match homd_curry.\nhomd_curry: ${printTerm(homd!.type)}\nalias_homd_: ${printTerm(alias!.type)}`
        );
    });

    it('types homd_curry and alias_homd_ applications to CatAt codomain', () => {
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

        const homdRes = elaborate(homdApp);
        const aliasRes = elaborate(aliasApp);
        const expectedType = catAtOf(Z, b1);

        assert.ok(
            areEqual(homdRes.type, expectedType, emptyCtx),
            `Expected homd_curry application type ${printTerm(expectedType)}, got ${printTerm(homdRes.type)}`
        );
        assert.ok(
            areEqual(aliasRes.type, expectedType, emptyCtx),
            `Expected alias_homd_ application type ${printTerm(expectedType)}, got ${printTerm(aliasRes.type)}`
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
});
