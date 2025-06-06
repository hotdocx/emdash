/**
 * @file tests/equality_tests.ts
 * @description Tests for term equality (areEqual), covering alpha, beta, and eta conversion.
 */
import {
    Term, Context, Icit,
    Type, Var, Lam, App, Pi, Hole
} from '../src/types';
import { emptyCtx, getTermRef, setFlag } from '../src/state';
import { defineGlobal } from '../src/globals';
import { resetMyLambdaPi } from '../src/stdlib';
import { areEqual } from '../src/equality';
import { normalize } from '../src/reduction';
import { assert } from './utils';
import { describe, it, beforeEach } from 'node:test';

describe("Equality Tests", () => {
    let ctx: Context;

    beforeEach(() => {
        resetMyLambdaPi();
        ctx = emptyCtx;
        defineGlobal("MyType", Type());
        defineGlobal("AnotherType", Type());
        defineGlobal("f", Pi("arg", Icit.Expl, Var("MyType"), _ => Var("MyType")));
        defineGlobal("g", Pi("arg", Icit.Expl, Var("MyType"), _ => Var("AnotherType")));
        defineGlobal("a", Var("MyType"));
        defineGlobal("b", Var("MyType"));
    });

    describe("Alpha Equivalence", () => {
        it("α-equivalence of Lam: (λx:MyType. x) === (λy:MyType. y)", () => {
            const term1 = Lam("x", Icit.Expl, Var("MyType"), x => x);
            const term2 = Lam("y", Icit.Expl, Var("MyType"), y => y);
            assert(areEqual(term1, term2, ctx), "λx.x should be α-equal to λy.y");
        });

        it("α-equivalence of Pi: (Πx:MyType. MyType) === (Πy:MyType. MyType)", () => {
            const term1 = Pi("x", Icit.Expl, Var("MyType"), _ => Var("MyType"));
            const term2 = Pi("y", Icit.Expl, Var("MyType"), _ => Var("MyType"));
            assert(areEqual(term1, term2, ctx), "Πx:T.T should be α-equal to Πy:T.T");
        });

        it("Nested α-equivalence: (λx. λy. x y) === (λa. λb. a b)", () => {
            // Assuming appropriate types for x and y for simplicity of testing equality logic
            const typeOfX = Pi("z", Icit.Expl, Var("AnotherType"), _ => Var("MyType"));
            const term1 = Lam("x", Icit.Expl, typeOfX, x => Lam("y", Icit.Expl, Var("AnotherType"), y => App(x, y, Icit.Expl)));
            const term2 = Lam("a", Icit.Expl, typeOfX, a => Lam("b", Icit.Expl, Var("AnotherType"), b => App(a, b, Icit.Expl)));
            assert(areEqual(term1, term2, ctx), "Nested lambdas should be α-equivalent");
        });

        it("Non α-equivalent due to free variable: (λx. x a) !== (λy. y b)", () => {
            const term1 = Lam("x", Icit.Expl, Var("MyType"), x => App(Var("f"), x, Icit.Expl)); // λx. f x
            const term2 = Lam("y", Icit.Expl, Var("MyType"), y => App(Var("g"), y, Icit.Expl)); // λy. g y
             assert(!areEqual(term1, term2, ctx), "λx.f x should NOT be α-equal to λy.g y");
        });
    });

    describe("Beta Reduction Equivalence", () => {
        it("β-equivalence: ((λx:MyType. f x) a) === f a", () => {
            const term1 = App(Lam("x", Icit.Expl, Var("MyType"), x => App(Var("f"), x, Icit.Expl)), Var("a"), Icit.Expl);
            const term2 = App(Var("f"), Var("a"), Icit.Expl);
            assert(areEqual(term1, term2, ctx), "((λx. f x) a) should be β-equal to (f a)");
        });

        it("β-equivalence with identity: ((λx:MyType. x) a) === a", () => {
            const term1 = App(Lam("x", Icit.Expl, Var("MyType"), x => x), Var("a"), Icit.Expl);
            const term2 = Var("a");
            assert(areEqual(term1, term2, ctx), "((λx. x) a) should be β-equal to a");
        });

        it("β-equivalence with const function: ((λx:MyType. b) a) === b", () => {
            const term1 = App(Lam("x", Icit.Expl, Var("MyType"), _ => Var("b")), Var("a"), Icit.Expl);
            const term2 = Var("b");
            assert(areEqual(term1, term2, ctx), "((λx. b) a) should be β-equal to b");
        });
    });

    describe("Eta Conversion Equivalence", () => {
        it("Non η-equivalent by default: (λx:MyType. f x) !== f", () => {
            const term1 = Lam("x", Icit.Expl, Var("MyType"), x => App(Var("f"), x, Icit.Expl));
            const term2 = Var("f");
            // By default, etaEquality flag is off.
            assert(!areEqual(term1, term2, ctx), "λx. f x should NOT be η-equal to f by default");
        });

        it("η-equivalence when flag is on: (λx:MyType. f x) === f", () => {
            setFlag('etaEquality', true);
            const term1 = Lam("x", Icit.Expl, Var("MyType"), x => App(Var("f"), x, Icit.Expl));
            const term2 = Var("f");
            assert(areEqual(term1, term2, ctx), "λx. f x should be η-equal to f when etaEquality flag is on");
        });

        it("Non η-equivalent: (λx:MyType. f a) !== f", () => {
            setFlag('etaEquality', true); // Set flag to ensure failure is not due to flag being off
            const term1 = Lam("x", Icit.Expl, Var("MyType"), _ => App(Var("f"), Var("a"), Icit.Expl));
            const term2 = Var("f");
            assert(!areEqual(term1, term2, ctx), "λx. f a should NOT be η-equal to f");
        });
    });

    describe("General Equality", () => {
        it("Reflexivity: a === a", () => {
            assert(areEqual(Var("a"), Var("a"), ctx), "Reflexivity: a === a");
        });

        it("Non-equality: a !== b", () => {
            assert(!areEqual(Var("a"), Var("b"), ctx), "Non-equality: a !== b");
        });

        it("Equality of complex terms after reduction", () => {
            const term1 = App(Lam("x", Icit.Expl, Var("MyType"), x => App(Var("f"), x, Icit.Expl)), Var("a"), Icit.Expl); // (λx.f x) a
            const term2 = App(Var("f"), Var("a"), Icit.Expl); // f a
            assert(areEqual(term1, term2, ctx), "Complex terms should be equal after reduction");
        });
    });
}); 