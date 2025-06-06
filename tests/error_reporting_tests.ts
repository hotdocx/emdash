/**
 * @file tests/error_reporting_tests.ts
 * @description Tests for error reporting during elaboration.
 */
import {
    Term, Context, Icit, Type, Var, Lam, App, Pi, Hole,
} from '../src/types';
import {
    emptyCtx, getTermRef, globalDefs, printTerm
} from '../src/state';
import {
    defineGlobal
} from '../src/globals';
import {
    resetMyLambdaPi
} from '../src/stdlib';
import {
    elaborate
} from '../src/elaboration';
import { assert } from './utils';
import { describe, it, beforeEach } from 'node:test';

describe("Error Reporting Tests", () => {

    beforeEach(() => {
        resetMyLambdaPi();
        defineGlobal("MyType", Type());
        defineGlobal("MyOtherType", Type());
        defineGlobal("f", Pi("arg", Icit.Expl, Var("MyType"), _ => Var("MyOtherType")));
        defineGlobal("c", Var("MyType"));
    });

    it("should throw an error for unbound variables", () => {
        const term = Var("unboundVar");
        try {
            elaborate(term);
            assert(false, "Elaboration should have failed for unbound variable");
        } catch (e) {
            const err = e as Error;
            assert(err.message.includes("Unbound variable: unboundVar"), `Expected 'Unbound variable' error, but got: ${err.message}`);
        }
    });

    it("should throw a type mismatch error in application", () => {
        // Applying 'f' to an argument of the wrong type.
        // f expects MyType, but we provide MyOtherType.
        defineGlobal("wrongArg", Var("MyOtherType"));
        const term = App(Var("f"), Var("wrongArg"), Icit.Expl);

        try {
            elaborate(term);
            assert(false, "Elaboration should have failed for type mismatch");
        } catch (e) {
            const err = e as Error;
            assert(err.message.includes("Could not solve constraints"), `Expected 'Could not solve constraints' error, but got: ${err.message}`);
        }
    });

    it("should throw an error when applying a non-function", () => {
        // 'c' has type MyType, which is not a function type.
        const term = App(Var("c"), Var("c"), Icit.Expl);
        try {
            elaborate(term);
            assert(false, "Elaboration should have failed for applying a non-function");
        } catch (e) {
            const err = e as Error;
            // The error will likely be a constraint failure, trying to unify MyType with a Pi type.
            assert(err.message.includes("Could not solve constraints"), `Expected constraint error for applying non-function, but got: ${err.message}`);
        }
    });

    it("should throw an occurs check error", () => {
        // A simple way to trigger an occurs check is to unify a hole with
        // a term containing that same hole.
        // We can create this situation by checking `λx. x x`.
        // The type of `x` would be inferred as `?a`, and then we check `x : ?a`
        // and `x : ?a -> ?b`. This leads to `?a === ?a -> ?b`.
        const selfApp = Lam("x", Icit.Expl, x => App(x, x, Icit.Expl));

        try {
            elaborate(selfApp);
            assert(false, "Elaboration of self-application should have failed for occurs check");
        } catch (e) {
            const err = e as Error;
            assert(err.message.includes("Could not solve constraints") || err.message.includes("occurs check"), `Expected occurs check error, but got: ${err.message}`);
        }
    });
}); 