/**
 * @file tests/parser_logic_tests.ts
 * @description Tests for the parser logic in `src/parser-logic.ts`.
 */

import { parseToSyntaxTree } from '../src/parser';
import { Term, Type, Var } from '../src/types';
import { describe, it } from 'node:test';
import assert from 'node:assert';

describe('Parser Logic: `parseToSyntaxTree`', () => {
    describe('Primitives and Variables', () => {
        it('should parse Type', () => {
            const parsedTerm: Term = parseToSyntaxTree('Type');
            const manualTerm: Term = Type();
            assert.deepStrictEqual(parsedTerm, manualTerm, '`Type` should parse to Type()');
        });

        it('should parse a simple variable', () => {
            const parsedTerm: Term = parseToSyntaxTree('Nat');
            const manualTerm: Term = Var("Nat");
            assert.deepStrictEqual(parsedTerm, manualTerm, '`Nat` should parse to Var("Nat")');
        });
    });
});
// /**
//  * @file tests/parser_tests.ts
//  * @description Tests for the compile-time parser macro (`$term`).
//  */

// import { $term } from '../src/macro';
// import { Term, Icit, Type, Var, Lam, App, Pi } from '../src/types';
// import { emptyCtx, globalDefs } from '../src/state';
// import { defineGlobal } from '../src/globals';
// import { resetMyLambdaPi } from '../src/stdlib';
// import { areEqual } from '../src/equality';
// // import assert from 'node:assert';
// import { describe, it, beforeEach } from 'node:test';
// import { assert } from './utils';

// describe('Parser Macro: `$term`', () => {

//     beforeEach(() => {
//         resetMyLambdaPi();
//         // Define some basic globals that will be used across tests.
//         // The parser doesn't need them, but areEqual does for elaboration.
//         defineGlobal("Nat", Type());
//         defineGlobal("Bool", Type());
//         defineGlobal("f", Pi("_", Icit.Expl, Var("Nat"), _ => Var("Nat")));
//         defineGlobal("g", Pi("_", Icit.Impl, Type(), _ => Var("Nat")));
//         defineGlobal("x", Var("Nat"));
//         defineGlobal("A", Type());
//         defineGlobal("B", Type());
//     });

//     describe('Primitives and Variables', () => {
//         it('should parse Type', () => {
//             const parsedTerm: Term = $term!('Type');
//             const manualTerm: Term = Type();
//             assert(areEqual(parsedTerm, manualTerm, emptyCtx), '`Type` should parse to Type()');
//         });

//         it('should parse a simple variable', () => {
//             const parsedTerm: Term = $term!('Nat');
//             const manualTerm: Term = Var("Nat");
//             assert(areEqual(parsedTerm, manualTerm, emptyCtx), '`Nat` should parse to Var("Nat")');
//         });
//     });

//     // describe('Lambdas and Pi Types', () => {
//     //     it('should parse a typed lambda: λ (x : Nat). x', () => {
//     //         const parsedTerm: Term = $term('λ (x : Nat). x');
//     //         const manualTerm: Term = Lam("x", Icit.Expl, Var("Nat"), (v) => v);
//     //         assert(areEqual(parsedTerm, manualTerm, emptyCtx));
//     //     });

//     //     it('should parse an untyped lambda: λ x. x', () => {
//     //         // Note: Elaboration will later infer the type of 'x' as a hole.
//     //         const parsedTerm: Term = $term('λ x. x');
//     //         const manualTerm: Term = Lam("x", Icit.Expl, (v) => v);
//     //         assert(areEqual(parsedTerm, manualTerm, emptyCtx));
//     //     });

//     //     it('should parse multiple binders: λ (x : Nat) y. y', () => {
//     //         const parsedTerm: Term = $term('λ (x : Nat) y. y');
//     //         const manualTerm: Term = Lam("x", Icit.Expl, Var("Nat"), _ => Lam("y", Icit.Expl, v => v));
//     //         assert(areEqual(parsedTerm, manualTerm, emptyCtx));
//     //     });

//     //     it('should parse an implicit lambda binder: λ {A : Type}. A', () => {
//     //         const parsedTerm: Term = $term('λ {A : Type}. A');
//     //         const manualTerm: Term = Lam("A", Icit.Impl, Type(), v => v);
//     //         assert(areEqual(parsedTerm, manualTerm, emptyCtx));
//     //     });

//     //     it('should parse a Pi type: Π (x : Nat). Nat', () => {
//     //         const parsedTerm: Term = $term('Π (x : Nat). Nat');
//     //         const manualTerm: Term = Pi("x", Icit.Expl, Var("Nat"), _ => Var("Nat"));
//     //         assert(areEqual(parsedTerm, manualTerm, emptyCtx));
//     //     });

//     //     it('should parse a non-dependent Pi as an arrow: Nat -> Bool', () => {
//     //         const parsedTerm: Term = $term('Nat -> Bool');
//     //         const manualTerm: Term = Pi("_", Icit.Expl, Var("Nat"), _ => Var("Bool"));
//     //         assert(areEqual(parsedTerm, manualTerm, emptyCtx));
//     //     });

//     //     it('should handle right-associativity of arrows: A -> B -> Nat', () => {
//     //         const parsedTerm: Term = $term('A -> B -> Nat');
//     //         const manualTerm: Term = Pi("_", Icit.Expl, Var("A"), _ => Pi("_", Icit.Expl, Var("B"), _ => Var("Nat")));
//     //         assert(areEqual(parsedTerm, manualTerm, emptyCtx));
//     //     });

//     //     it('should parse an implicit Pi binder: Π {A : Type}. A -> A', () => {
//     //         const parsedTerm: Term = $term('Π {A : Type}. A -> A');
//     //         const manualTerm: Term = Pi("A", Icit.Impl, Type(), A_ => Pi("_", Icit.Expl, A_, _ => A_));
//     //         assert(areEqual(parsedTerm, manualTerm, emptyCtx));
//     //     });
//     // });

//     // describe('Application and Precedence', () => {
//     //     it('should parse simple application: f x', () => {
//     //         const parsedTerm: Term = $term('f x');
//     //         const manualTerm: Term = App(Var("f"), Var("x"), Icit.Expl);
//     //         assert(areEqual(parsedTerm, manualTerm, emptyCtx));
//     //     });

//     //     it('should handle left-associativity of application: f x Nat', () => {
//     //         const parsedTerm: Term = $term('f x Nat');
//     //         const manualTerm: Term = App(App(Var("f"), Var("x"), Icit.Expl), Var("Nat"), Icit.Expl);
//     //         assert(areEqual(parsedTerm, manualTerm, emptyCtx));
//     //     });

//     //     it('should parse implicit application: g {Nat}', () => {
//     //         const parsedTerm: Term = $term('g {Nat}');
//     //         const manualTerm: Term = App(Var("g"), Var("Nat"), Icit.Impl);
//     //         assert(areEqual(parsedTerm, manualTerm, emptyCtx));
//     //     });

//     //     it('should respect parentheses: f (g {A})', () => {
//     //         const parsedTerm: Term = $term('f (g {A})');
//     //         const manualTerm: Term = App(Var("f"), App(Var("g"), Var("A"), Icit.Impl), Icit.Expl);
//     //         assert(areEqual(parsedTerm, manualTerm, emptyCtx));
//     //     });

//     //     it('should give application higher precedence than arrows: f x -> g {A}', () => {
//     //         const parsedTerm: Term = $term('f x -> g {A}');

//     //         // This should parse as (f x) -> (g {A})
//     //         const manualTerm: Term = Pi("_", Icit.Expl,
//     //             App(Var("f"), Var("x"), Icit.Expl),
//     //             _ => App(Var("g"), Var("A"), Icit.Impl)
//     //         );
//     //         assert(areEqual(parsedTerm, manualTerm, emptyCtx));
//     //     });
//     // });

//     // describe('Complex Examples', () => {
//     //     it('should parse a complex nested term correctly', () => {
//     //         const source = "λ (f : Nat -> Nat) (x : Nat). f (f x)";
//     //         const parsedTerm: Term = $term(source);

//     //         const manualTerm: Term = Lam("f", Icit.Expl,
//     //             Pi("_", Icit.Expl, Var("Nat"), _ => Var("Nat")),
//     //             (f_var) => Lam("x", Icit.Expl, Var("Nat"),
//     //                 (x_var) => App(
//     //                     f_var,
//     //                     App(f_var, x_var, Icit.Expl),
//     //                     Icit.Expl
//     //                 )
//     //             )
//     //         );

//     //         assert(areEqual(parsedTerm, manualTerm, emptyCtx), 'Complex term did not parse as expected.');
//     //     });

//     //     it('should parse the type of the `const` function', () => {
//     //         const source = "Π {A : Type} {B : Type}. A -> B -> A";
//     //         const parsedTerm: Term = $term(source);

//     //         const manualTerm: Term = Pi("A", Icit.Impl, Type(), (A_var) =>
//     //             Pi("B", Icit.Impl, Type(), (_B_var) =>
//     //                 Pi("_", Icit.Expl, A_var, _ =>
//     //                     Pi("_", Icit.Expl, _B_var, _ => A_var)
//     //                 )
//     //             )
//     //         );

//     //         assert(areEqual(parsedTerm, manualTerm, emptyCtx));
//     //     });
//     // });
// });