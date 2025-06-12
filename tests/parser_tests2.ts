/**
 * @file tests/parser_tests2.ts
 * @description Tests for the new parser logic in `src/parser2.ts`.
 */
import { Term, Icit, Type, Var, Lam, App, Pi, Let, Hole } from '../src/types';
import { emptyCtx, globalDefs, resetHoleId } from '../src/state';
import { defineGlobal } from '../src/globals';
import { resetMyLambdaPi } from '../src/stdlib';
import { areEqual } from '../src/equality';
import { parseToSyntaxTree2 } from '../src/parser2';
import { describe, it, beforeEach } from 'node:test';
import assert from 'node:assert';

describe('Parser 2: New Syntax (`parseToSyntaxTree2`)', () => {

    beforeEach(() => {
        resetMyLambdaPi();
        resetHoleId(); // Reset hole counter for predictable hole names in tests
        // Define some basic globals that will be used across tests.
        defineGlobal("Nat", Type());
        defineGlobal("Bool", Type());
        defineGlobal("f", Pi("_", Icit.Expl, Var("Nat"), _ => Var("Nat")));
        defineGlobal("g", Pi("_", Icit.Impl, Type(), _ => Var("Nat")));
        defineGlobal("x", Var("Nat"));
        defineGlobal("A", Type());
        defineGlobal("B", Type());
    });

    describe('Primitives and Variables', () => {
        it('should parse Type', () => {
            const parsed = parseToSyntaxTree2('Type');
            const manual = Type();
            assert(areEqual(parsed, manual, emptyCtx), '`Type` should parse to Type()');
        });

        it('should parse a simple variable', () => {
            const parsed = parseToSyntaxTree2('Nat');
            const manual = Var("Nat");
            assert(areEqual(parsed, manual, emptyCtx), '`Nat` should parse to Var("Nat")');
        });

        it('should parse _ as a hole', () => {
            const parsed = parseToSyntaxTree2('_');
            // The exact hole name doesn't matter, just that it's a hole.
            assert.strictEqual(parsed.tag, 'Hole', "Parsed term should be a Hole");
        });
    });

    describe('Lambdas (\\ or fun)', () => {
        it('should parse a typed lambda with \\ keyword : \\ (x : Nat). x', () => {
            const parsed = parseToSyntaxTree2('\\ (x : Nat). x');
            const manual = Lam("x", Icit.Expl, Var("Nat"), (v) => v);
            assert(areEqual(parsed, manual, emptyCtx));
        });

        it('should parse a typed lambda with fun keyword: fun (x : Nat). x', () => {
            const parsed = parseToSyntaxTree2('fun (x : Nat). x');
            const manual = Lam("x", Icit.Expl, Var("Nat"), (v) => v);
            assert(areEqual(parsed, manual, emptyCtx));
        });

        it('should parse an untyped lambda: fun x. x', () => {
            const parsed = parseToSyntaxTree2('fun x. x');
            const manual = Lam("x", Icit.Expl, (v) => v);
            assert(areEqual(parsed, manual, emptyCtx));
        });

        it('should parse multiple binders: fun (x : Nat) y. y', () => {
            const parsed = parseToSyntaxTree2('fun (x : Nat) y. y');
            const manual = Lam("x", Icit.Expl, Var("Nat"), _ => Lam("y", Icit.Expl, v => v));
            assert(areEqual(parsed, manual, emptyCtx));
        });

        it('should parse grouped explicit binders: fun (x y : Nat). y', () => {
            const parsed = parseToSyntaxTree2('fun (x y : Nat). y');
            const manual = Lam("x", Icit.Expl, Var("Nat"), _ => Lam("y", Icit.Expl, Var("Nat"), v => v));
            assert(areEqual(parsed, manual, emptyCtx));
        });

        it('should parse an implicit lambda binder: fun {A : Type}. A', () => {
            const parsed = parseToSyntaxTree2('fun {A : Type}. A');
            const manual = Lam("A", Icit.Impl, Type(), v => v);
            assert(areEqual(parsed, manual, emptyCtx));
        });

        it('should parse grouped implicit binders: fun {A B : Type}. A', () => {
            const parsed = parseToSyntaxTree2('fun {A B : Type}. A');
            const manual = Lam("A", Icit.Impl, Type(), vA => Lam("B", Icit.Impl, Type(), _ => vA));
            assert(areEqual(parsed, manual, emptyCtx));
        });

        it('should parse untyped implicit binders with \\ keyword: \\ {A B}. A', () => {
            const parsed = parseToSyntaxTree2('\\ {A B}. A');
            const manual = Lam("A", Icit.Impl, vA => Lam("B", Icit.Impl, _ => vA));
            assert(areEqual(parsed, manual, emptyCtx));
        });
        it('should parse untyped implicit binders with fun keyword: fun {A B}. A', () => {
            const parsed = parseToSyntaxTree2('fun {A B}. A');
            const manual = Lam("A", Icit.Impl, vA => Lam("B", Icit.Impl, _ => vA));
            assert(areEqual(parsed, manual, emptyCtx));
        });
    });

    describe('Pi Types and Arrows (->)', () => {
        it('should parse a non-dependent Pi as an arrow: Nat -> Bool', () => {
            const parsed = parseToSyntaxTree2('Nat -> Bool');
            const manual = Pi("_", Icit.Expl, Var("Nat"), _ => Var("Bool"));
            assert(areEqual(parsed, manual, emptyCtx));
        });

        it('should handle right-associativity of arrows: A -> B -> Nat', () => {
            const parsed = parseToSyntaxTree2('A -> B -> Nat');
            const manual = Pi("_", Icit.Expl, Var("A"), _ => Pi("_", Icit.Expl, Var("B"), _ => Var("Nat")));
            assert(areEqual(parsed, manual, emptyCtx));
        });

        it('should parse a dependent Pi type: (x : Nat) -> Nat', () => {
            const parsed = parseToSyntaxTree2('(x : Nat) -> Nat');
            const manual = Pi("x", Icit.Expl, Var("Nat"), _ => Var("Nat"));
            assert(areEqual(parsed, manual, emptyCtx));
        });

        it('should parse grouped dependent Pi binders: (x y : Nat) -> Nat', () => {
            const parsed = parseToSyntaxTree2('(x y : Nat) -> Nat');
            const manual = Pi("x", Icit.Expl, Var("Nat"), _ => Pi("y", Icit.Expl, Var("Nat"), _ => Var("Nat")));
            assert(areEqual(parsed, manual, emptyCtx));
        });

        it('should parse an implicit Pi binder: {A : Type} -> A -> A', () => {
            const parsed = parseToSyntaxTree2('{A : Type} -> A -> A');
            const manual = Pi("A", Icit.Impl, Type(), A_ => Pi("_", Icit.Expl, A_, _ => A_));
            assert(areEqual(parsed, manual, emptyCtx));
        });

        it('should parse mixed grouped binders: {A B : Type} (x : A) -> B', () => {
            const parsed = parseToSyntaxTree2('{A B : Type} (x : A) -> B');
            const manual = Pi("A", Icit.Impl, Type(), _ => Pi("B", Icit.Impl, Type(), B_ => Pi("x", Icit.Expl, _, _ => B_)));
            assert(areEqual(parsed, manual, emptyCtx));
        });
    });

    describe('Application and Precedence', () => {
        it('should parse simple application: f x', () => {
            const parsed = parseToSyntaxTree2('f x');
            const manual = App(Var("f"), Var("x"), Icit.Expl);
            assert(areEqual(parsed, manual, emptyCtx));
        });

        it('should handle left-associativity of application: f x Nat', () => {
            const parsed = parseToSyntaxTree2('f x Nat');
            const manual = App(App(Var("f"), Var("x"), Icit.Expl), Var("Nat"), Icit.Expl);
            assert(areEqual(parsed, manual, emptyCtx));
        });

        it('should parse implicit application: g {Nat}', () => {
            const parsed = parseToSyntaxTree2('g {Nat}');
            const manual = App(Var("g"), Var("Nat"), Icit.Impl);
            assert(areEqual(parsed, manual, emptyCtx));
        });

        it('should respect parentheses: f (g {A})', () => {
            const parsed = parseToSyntaxTree2('f (g {A})');
            const manual = App(Var("f"), App(Var("g"), Var("A"), Icit.Impl), Icit.Expl);
            assert(areEqual(parsed, manual, emptyCtx));
        });

        it('should give application higher precedence than arrows: f x -> g {A}', () => {
            const parsed = parseToSyntaxTree2('f x -> g {A}');
            const manual = Pi("_", Icit.Expl,
                App(Var("f"), Var("x"), Icit.Expl),
                _ => App(Var("g"), Var("A"), Icit.Impl)
            );
            assert(areEqual(parsed, manual, emptyCtx));
        });

        it('should handle parentheses in arrow types: (A -> B) -> Nat', () => {
            const parsed = parseToSyntaxTree2('(A -> B) -> Nat');
            const manual = Pi("_", Icit.Expl,
                Pi("_", Icit.Expl, Var("A"), _ => Var("B")),
                _ => Var("Nat")
            );
            assert(areEqual(parsed, manual, emptyCtx));
        });
    });

    describe('Let Expressions', () => {
        it('should parse a simple typed let expression', () => {
            const source = "let x : Nat = Nat in x";
            const parsed = parseToSyntaxTree2(source);
            const manual = Let("x", Var("Nat"), Var("Nat"), (v) => v);
            assert(areEqual(parsed, manual, emptyCtx));
        });

        it('should parse a simple untyped let expression', () => {
            const source = "let x = Nat in x";
            const parsed = parseToSyntaxTree2(source);
            const manual = Let("x", Var("Nat"), (v) => v);
            assert(areEqual(parsed, manual, emptyCtx));
        });

        it('should parse nested let expressions', () => {
            const source = "let A = Type in let x : A = Nat in x";
            const parsed = parseToSyntaxTree2(source);
            const manual = Let("A", Type(), (A_var) =>
                Let("x", A_var, Var("Nat"), (x_var) => x_var)
            );
            assert(areEqual(parsed, manual, emptyCtx));
        });

        it('should parse let with a lambda body', () => {
            const source = "let id = \\ (y:Nat). y in id x";
            const parsed = parseToSyntaxTree2(source);
            const manual = Let("id",
                Lam("y", Icit.Expl, Var("Nat"), (y_var) => y_var),
                (id_var) => App(id_var, Var("x"), Icit.Expl)
            );
            assert(areEqual(parsed, manual, emptyCtx));
        });
    });

    describe('Complex Examples', () => {
        it('should parse a complex nested term correctly', () => {
            const source = "\\ (f : Nat -> Nat) (x : Nat). f (f x)";
            const parsed = parseToSyntaxTree2(source);

            const manual = Lam("f", Icit.Expl,
                Pi("_", Icit.Expl, Var("Nat"), _ => Var("Nat")),
                (f_var) => Lam("x", Icit.Expl, Var("Nat"),
                    (x_var) => App(
                        f_var,
                        App(f_var, x_var, Icit.Expl),
                        Icit.Expl
                    )
                )
            );
            assert(areEqual(parsed, manual, emptyCtx), 'Complex term did not parse as expected.');
        });

        it('should parse the type of the `const` function', () => {
            const source = "{A : Type} -> {B : Type} -> A -> B -> A";
            const parsed = parseToSyntaxTree2(source);

            const manual = Pi("A", Icit.Impl, Type(), (A_var) =>
                Pi("B", Icit.Impl, Type(), (B_var) =>
                    Pi("_", Icit.Expl, A_var, _ =>
                        Pi("_", Icit.Expl, B_var, _ => A_var)
                    )
                )
            );

            assert(areEqual(parsed, manual, emptyCtx));
        });

        it('should parse complex grouped binders', () => {
            const source = "{A B : Type} (x y : A) -> {z : B} -> A";
             const parsed = parseToSyntaxTree2(source);

            const manual = Pi("A", Icit.Impl, Type(), A_ =>
                Pi("B", Icit.Impl, Type(), B_ =>
                    Pi("x", Icit.Expl, A_, _ =>
                        Pi("y", Icit.Expl, A_, _ =>
                            Pi("z", Icit.Impl, B_, _ => A_)
                        )
                    )
                )
            );
            assert(areEqual(parsed, manual, emptyCtx));
        });
    });
}); 