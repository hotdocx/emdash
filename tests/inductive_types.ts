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

    describe("Polymorphic Lists (List A)", () => {
        let ListType: Term, nilTerm: Term, consTerm: Term;
        let Nat: Term, Bool: Term, z: Term, s: Term, one: Term, two: Term, three: Term;
        let list12_nat: Term, list23_nat: Term, list123_nat: Term;

        beforeEach(() => {
            // Pre-define Nat and some numbers for testing with List Nat
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

            defineGlobal("Bool", Type(), undefined, true, true);
            Bool = Var("Bool");

            // List :: Type -> Type
            defineGlobal("List", Pi("A", Icit.Expl, Type(), _ => Type()), undefined, true, true);
            ListType = Var("List");

            // nil :: Π {A:Type}. List A
            defineGlobal("nil", Pi("A", Icit.Impl, Type(), A => App(ListType, A, Icit.Expl)), undefined, true, true);
            nilTerm = Var("nil");

            // cons :: Π {A:Type}. A -> List A -> List A
            defineGlobal("cons", Pi("A", Icit.Impl, Type(), A => Pi("h", Icit.Expl, A, _ => Pi("t", Icit.Expl, App(ListType, A, Icit.Expl), _ => App(ListType, A, Icit.Expl)))), undefined, true, true);
            consTerm = Var("cons");

            // Helper to create a cons cell
            const mkCons = (A: Term, h: Term, t: Term) => App(App(App(consTerm, A, Icit.Impl), h, Icit.Expl), t, Icit.Expl);
            const nilNat = App(nilTerm, Nat, Icit.Impl);
            
            // Sample list: [1, 2]
            list12_nat = mkCons(Nat, Var("one"), mkCons(Nat, Var("two"), nilNat));
            defineGlobal("list12_nat", App(ListType, Nat, Icit.Expl), list12_nat);
            
            // Sample list: [2, 3]
            const list23_nat_val = mkCons(Nat, Var("two"), mkCons(Nat, Var("three"), nilNat));
            list23_nat = Var("list23_nat");
            defineGlobal("list23_nat", App(ListType, Nat, Icit.Expl), list23_nat_val);

            // Sample list: [1, 2, 3]
            const list123_nat_val = mkCons(Nat, Var("one"), mkCons(Nat, Var("two"), mkCons(Nat, Var("three"), nilNat)));
            list123_nat = Var("list123_nat");
            defineGlobal("list123_nat", App(ListType, Nat, Icit.Expl), list123_nat_val);
        });

        describe("Induction via Eliminator", () => {
            beforeEach(() => {
                const List_elim_type =
                    Pi("A", Icit.Impl, Type(), A =>
                    Pi("P", Icit.Expl, Pi("_", Icit.Expl, App(ListType, A, Icit.Expl), _ => Type()), P =>
                        Pi("p_nil", Icit.Expl, App(P, App(nilTerm, A, Icit.Impl), Icit.Expl), _ =>
                            Pi("p_cons", Icit.Expl,
                                Pi("h", Icit.Expl, A, h =>
                                Pi("t", Icit.Expl, App(ListType, A, Icit.Expl), t =>
                                Pi("rec", Icit.Expl, App(P, t, Icit.Expl), _ =>
                                    App(P, App(App(App(consTerm, A, Icit.Impl), h, Icit.Expl), t, Icit.Expl), Icit.Expl)
                                ))), _ =>
                            Pi("l", Icit.Expl, App(ListType, A, Icit.Expl), l => App(P, l, Icit.Expl))
                        ))
                    ));
                defineGlobal("List_elim", List_elim_type);

                // Add rewrite rule for nil case
                addRewriteRule("List_elim_nil", ["$A", "$P", "$p_nil", "$p_cons"],
                    App(App(App(App(App(Var("List_elim"), Var("$A"), Icit.Impl), Var("$P"), Icit.Expl), Var("$p_nil"), Icit.Expl), Var("$p_cons"), Icit.Expl), App(nilTerm, Var("$A"), Icit.Impl), Icit.Expl),
                    Var("$p_nil"),
                    emptyCtx
                );

                // Add rewrite rule for cons case
                const elimOnCons = App(App(App(App(App(Var("List_elim"), Var("$A"), Icit.Impl), Var("$P"), Icit.Expl), Var("$p_nil"), Icit.Expl), Var("$p_cons"), Icit.Expl), App(App(App(consTerm, Var("$A"), Icit.Impl), Var("$h"), Icit.Expl), Var("$t"), Icit.Expl), Icit.Expl);
                const consStep = App(
                    App(App(Var("$p_cons"), Var("$h"), Icit.Expl), Var("$t"), Icit.Expl),
                    // recursive call: (List_elim A P p_nil p_cons t)
                    App(App(App(App(App(Var("List_elim"), Var("$A"), Icit.Impl), Var("$P"), Icit.Expl), Var("$p_nil"), Icit.Expl), Var("$p_cons"), Icit.Expl), Var("$t"), Icit.Expl),
                    Icit.Expl
                );
                addRewriteRule("List_elim_cons", ["$A", "$P", "$p_nil", "$p_cons", "$h", "$t"], elimOnCons, consStep, emptyCtx);
            });

            it("should define a map function using List_elim and compute correctly", () => {
                const map_elim_type =
                    Pi("A", Icit.Impl, Type(), A =>
                    Pi("B", Icit.Impl, Type(), B =>
                        Pi("f", Icit.Expl, Pi("_", Icit.Expl, A, _ => B), _ =>
                        Pi("l", Icit.Expl, App(ListType, A, Icit.Expl), _ => App(ListType, B, Icit.Expl))
                    )));

                const map_elim_val =
                    Lam("A", Icit.Impl, Type(), A =>
                    Lam("B", Icit.Impl, Type(), B =>
                    Lam("f", Icit.Expl, Pi("_", Icit.Expl, A, _ => B), f_val =>
                    Lam("l", Icit.Expl, App(ListType, A, Icit.Expl), l_val =>
                        App(
                            App(App(App(App(Var("List_elim"), A, Icit.Impl),
                                Lam("_", Icit.Expl, App(ListType, A, Icit.Expl), _ => App(ListType, B, Icit.Expl)), // P, the motive
                                Icit.Expl),
                                App(nilTerm, B, Icit.Impl), Icit.Expl), // nil case
                                Lam("h", Icit.Expl, A, h_val => // cons case
                                Lam("t", Icit.Expl, App(ListType, A, Icit.Expl), _ =>
                                Lam("rec", Icit.Expl, App(ListType, B, Icit.Expl), rec_val =>
                                    App(App(App(consTerm, B, Icit.Impl), App(f_val, h_val, Icit.Expl), Icit.Expl), rec_val, Icit.Expl) // cons B (f h) rec
                                ))), Icit.Expl
                            ),
                            l_val, Icit.Expl
                        )
                    ))));
                defineGlobal("map_elim", map_elim_type, map_elim_val);
                
                // test map s [1,2] -> [2,3]
                const term_to_eval = App(App(App(App(Var("map_elim"), Nat, Icit.Impl), Nat, Icit.Impl), s, Icit.Expl), list12_nat, Icit.Expl);
                const result = elaborate(term_to_eval);
                
                const expected_type = App(ListType, Nat, Icit.Expl);
                assert.ok(areEqual(result.type, expected_type, emptyCtx), `map_elim s [1,2] should have type List Nat. Got ${printTerm(result.type)}`);
                assert.ok(areEqual(result.term, list23_nat, emptyCtx), `map_elim s [1,2] should be [2,3]. Got ${printTerm(result.term)}`);
            });
        });

        describe("Induction via Rewrite Rules", () => {
            beforeEach(() => {
                const append_type = Pi("A", Icit.Impl, Type(), A => Pi("l1", Icit.Expl, App(ListType, A, Icit.Expl), _ => Pi("l2", Icit.Expl, App(ListType, A, Icit.Expl), _ => App(ListType, A, Icit.Expl))));
                defineGlobal("append_rw", append_type);

                // append nil l2 = l2
                addRewriteRule("append_rw_nil", ["$A", "$l2"],
                    App(App(App(Var("append_rw"), Var("$A"), Icit.Impl), App(nilTerm, Var("$A"), Icit.Impl), Icit.Expl), Var("$l2"), Icit.Expl),
                    Var("$l2"),
                    emptyCtx
                );

                // append (cons h t) l2 = cons h (append t l2)
                const append_cons_lhs = App(App(App(Var("append_rw"), Var("$A"), Icit.Impl), App(App(App(consTerm, Var("$A"), Icit.Impl), Var("$h"), Icit.Expl), Var("$t"), Icit.Expl), Icit.Expl), Var("$l2"), Icit.Expl);
                const append_cons_rhs = App(App(App(consTerm, Var("$A"), Icit.Impl), Var("$h"), Icit.Expl), App(App(App(Var("append_rw"), Var("$A"), Icit.Impl), Var("$t"), Icit.Expl), Var("$l2"), Icit.Expl), Icit.Expl);
                addRewriteRule("append_rw_cons", ["$A", "$h", "$t", "$l2"], append_cons_lhs, append_cons_rhs, emptyCtx);
            });

            it("should define append using rewrite rules and compute correctly", () => {
                const list1_val = App(App(App(consTerm, Nat, Icit.Impl), Var("one"), Icit.Expl), App(nilTerm, Nat, Icit.Impl), Icit.Expl);
                const list1 = Var("list1");
                defineGlobal("list1", App(ListType, Nat, Icit.Expl), list1_val);

                const term_to_eval = App(App(App(Var("append_rw"), Nat, Icit.Impl), list1, Icit.Expl), list23_nat, Icit.Expl);
                const result = elaborate(term_to_eval);

                assert.ok(areEqual(result.term, list123_nat, emptyCtx), `append [1] [2,3] should be [1,2,3]. Got ${printTerm(result.term)}`);
            });
        });
    });
}); 