/**
 * @file tests/inductive_types.ts
 * @description Tests for defining and using inductive types, their constructors, eliminators, and functions defined over them.
 */
import {
    Term, Icit, Type, Var, Lam, App, Pi
} from '../src/types';
import {
    emptyCtx, printTerm
} from '../src/state';
import {
    defineGlobal, addRewriteRule
} from '../src/globals';
import {
    resetMyLambdaPi
} from '../src/stdlib';
import {
    elaborate
} from '../src/elaboration';
import assert from 'node:assert';
import { describe, it, beforeEach } from 'node:test';
import { areEqual } from '../src/equality';
import { normalize } from '../src/reduction';

describe("Inductive Types Tests", () => {
    beforeEach(() => {
        resetMyLambdaPi();
    });

    describe("Natural Numbers (Nat)", () => {
        let Nat: Term, z: Term, s: Term;
        let one: Term, two: Term, three: Term;

        beforeEach(() => {
            defineGlobal("Nat", Type(), undefined, true, true);
            Nat = Var("Nat");

            defineGlobal("z", Nat, undefined, true, true);
            z = Var("z");

            defineGlobal("s", Pi("n", Icit.Expl, Nat, _ => Nat), undefined, true, true);
            s = Var("s");

            one = App(s, z, Icit.Expl);
            two = App(s, one, Icit.Expl);
            three = App(s, two, Icit.Expl);
            defineGlobal("one", Nat, one);
            defineGlobal("two", Nat, two);
            defineGlobal("three", Nat, three);
        });

        describe("Induction via Eliminator", () => {
            beforeEach(() => {
                const Nat_elim_type =
                    Pi("P", Icit.Expl, Pi("_", Icit.Expl, Nat, _ => Type()), P =>
                        Pi("pz", Icit.Expl, App(P, z, Icit.Expl), _ =>
                            Pi("ps", Icit.Expl,
                                Pi("n", Icit.Expl, Nat, n =>
                                    Pi("rec", Icit.Expl, App(P, n, Icit.Expl), _ =>
                                        App(P, App(s, n, Icit.Expl), Icit.Expl)
                                    )
                                ), _ =>
                                Pi("m", Icit.Expl, Nat, m => App(P, m, Icit.Expl))
                            )
                        )
                    );
                defineGlobal("Nat_elim", Nat_elim_type);

                addRewriteRule(
                    "Nat_elim_z",
                    ["$P", "$pz", "$ps"],
                    App(App(App(App(Var("Nat_elim"), Var("$P"), Icit.Expl), Var("$pz"), Icit.Expl), Var("$ps"), Icit.Expl), z, Icit.Expl),
                    Var("$pz"),
                    emptyCtx
                );

                const elimOnS = App(App(App(App(Var("Nat_elim"), Var("$P"), Icit.Expl), Var("$pz"), Icit.Expl), Var("$ps"), Icit.Expl), App(s, Var("$n"), Icit.Expl), Icit.Expl);
                const succStep = App(
                    App(Var("$ps"), Var("$n"), Icit.Expl),
                    App(App(App(App(Var("Nat_elim"), Var("$P"), Icit.Expl), Var("$pz"), Icit.Expl), Var("$ps"), Icit.Expl), Var("$n"), Icit.Expl), Icit.Expl
                );
                addRewriteRule("Nat_elim_s", ["$P", "$pz", "$ps", "$n"], elimOnS, succStep, emptyCtx);
            });

            it("should define addition using Nat_elim and compute correctly", () => {
                const add_elim_type = Pi("n", Icit.Expl, Nat, _ => Pi("m", Icit.Expl, Nat, _ => Nat));
                const add_elim_val = Lam("n", Icit.Expl, Nat, n_val =>
                    Lam("m", Icit.Expl, Nat, m_val =>
                        App(
                            App(
                                App(
                                    App(Var("Nat_elim"), Lam("_", Icit.Expl, Nat, _ => Nat), Icit.Expl),
                                    m_val, Icit.Expl
                                ),
                                Lam("k_unused", Icit.Expl, Nat, _ =>
                                    Lam("rec", Icit.Expl, Nat, rec_val =>
                                        App(s, rec_val, Icit.Expl)
                                    )
                                ), Icit.Expl
                            ),
                            n_val, Icit.Expl
                        )
                    )
                );
                defineGlobal("add_elim", add_elim_type, add_elim_val);

                const term_to_eval = App(App(Var("add_elim"), Var("one"), Icit.Expl), Var("two"), Icit.Expl);
                const result = elaborate(term_to_eval);

                assert.ok(areEqual(result.type, Nat, emptyCtx), `add_elim 1 2 should have type Nat. Got ${printTerm(result.type)}`);
                assert.ok(areEqual(result.term, Var("three"), emptyCtx), `add_elim 1 2 should be 3. Got ${printTerm(result.term)}`);

                const term_zero = App(App(Var("add_elim"), z, Icit.Expl), Var("three"), Icit.Expl);
                const result_zero = elaborate(term_zero);
                assert.ok(areEqual(result_zero.term, Var("three"), emptyCtx), `add_elim 0 3 should be 3. Got ${printTerm(result_zero.term)}`);
            });
        });

        describe("Induction via Rewrite Rules", () => {
             beforeEach(() => {
                defineGlobal("add_rw", Pi("n", Icit.Expl, Nat, _ => Pi("m", Icit.Expl, Nat, _ => Nat)));
                addRewriteRule("add_rw_z", ["$m"], App(App(Var("add_rw"), z, Icit.Expl), Var("$m"), Icit.Expl), Var("$m"), emptyCtx);
                const succ_rhs = App(s, App(App(Var("add_rw"), Var("$n"), Icit.Expl), Var("$m"), Icit.Expl), Icit.Expl);
                addRewriteRule("add_rw_s", ["$n", "$m"], App(App(Var("add_rw"), App(s, Var("$n"), Icit.Expl), Icit.Expl), Var("$m"), Icit.Expl), succ_rhs, emptyCtx);
             });

             it("should define addition using rewrite rules and compute correctly", () => {
                const term_to_eval = App(App(Var("add_rw"), Var("one"), Icit.Expl), Var("two"), Icit.Expl);
                const result = elaborate(term_to_eval);

                assert.ok(areEqual(result.type, Nat, emptyCtx), `add_rw 1 2 should have type Nat. Got ${printTerm(result.type)}`);
                assert.ok(areEqual(result.term, Var("three"), emptyCtx), `add_rw 1 2 should be 3. Got ${printTerm(result.term)}`);
             });
        });
    });

    describe("Booleans (Bool)", () => {
        let Bool: Term, btrue: Term, bfalse: Term;

        beforeEach(() => {
            defineGlobal("Bool", Type(), undefined, true, true);
            Bool = Var("Bool");
            defineGlobal("true", Bool, undefined, true, true);
            btrue = Var("true");
            defineGlobal("false", Bool, undefined, true, true);
            bfalse = Var("false");
        });
        
        it("should define Bool eliminator and a `not` function", () => {
            const Bool_elim_type = Pi("P", Icit.Expl, Pi("_", Icit.Expl, Bool, _ => Type()), P => Pi("pt", Icit.Expl, App(P, btrue, Icit.Expl), _ => Pi("pf", Icit.Expl, App(P, bfalse, Icit.Expl), _ => Pi("b", Icit.Expl, Bool, b => App(P, b, Icit.Expl)))));
            defineGlobal("Bool_elim", Bool_elim_type);

            addRewriteRule("Bool_elim_true", ["$P", "$pt", "$pf"], App(App(App(App(Var("Bool_elim"), Var("$P"), Icit.Expl), Var("$pt"), Icit.Expl), Var("$pf"), Icit.Expl), btrue, Icit.Expl), Var("$pt"), emptyCtx);
            addRewriteRule("Bool_elim_false", ["$P", "$pt", "$pf"], App(App(App(App(Var("Bool_elim"), Var("$P"), Icit.Expl), Var("$pt"), Icit.Expl), Var("$pf"), Icit.Expl), bfalse, Icit.Expl), Var("$pf"), emptyCtx);

            const not_elim_val = Lam("b", Icit.Expl, Bool, b_val => App(App(App(App(Var("Bool_elim"), Lam("_", Icit.Expl, Bool, _ => Bool), Icit.Expl), bfalse, Icit.Expl), btrue, Icit.Expl), b_val, Icit.Expl));
            defineGlobal("not_elim", Pi("_", Icit.Expl, Bool, _ => Bool), not_elim_val);
            
            const term1 = App(Var("not_elim"), btrue, Icit.Expl);
            const res1 = elaborate(term1);
            assert.ok(areEqual(res1.term, bfalse, emptyCtx), `not_elim true should be false, got ${printTerm(res1.term)}`);

            const term2 = App(Var("not_elim"), bfalse, Icit.Expl);
            const res2 = elaborate(term2);
            assert.ok(areEqual(res2.term, btrue, emptyCtx), `not_elim false should be true, got ${printTerm(res2.term)}`);
        });

        it("should define a `not` function with direct rewrite rules", () => {
            defineGlobal("not_rw", Pi("_", Icit.Expl, Bool, _ => Bool));
            addRewriteRule("not_rw_true", [], App(Var("not_rw"), btrue, Icit.Expl), bfalse, emptyCtx);
            addRewriteRule("not_rw_false", [], App(Var("not_rw"), bfalse, Icit.Expl), btrue, emptyCtx);

            const term1 = App(Var("not_rw"), btrue, Icit.Expl);
            const res1 = elaborate(term1);
            assert.ok(areEqual(res1.term, bfalse, emptyCtx), `not_rw true should be false, got ${printTerm(res1.term)}`);
        });
    });
}); 