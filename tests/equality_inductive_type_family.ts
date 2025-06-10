/**
 * @file tests/equality_inductive_type_family.ts
 * @description Tests for the indexed inductive type family of equality (Eq).
 * This includes defining Eq, its constructor `refl`, and its eliminator `Eq_elim` (J),
 * and using them to prove standard properties like symmetry, transitivity, and congruence.
 */
import {
    Term, Icit, Type, Var, Lam, App, Pi, Hole
} from '../src/types';
import {
    emptyCtx, printTerm,
    setDebugVerbose
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
setDebugVerbose(true);

describe("Equality Inductive Type Family (Eq)", () => {
    beforeEach(() => {
        resetMyLambdaPi();
    });

    // We'll use Nat for concrete examples
    let Nat: Term, z: Term, s: Term;
    let one: Term, two: Term;
    let Eq: Term, refl: Term;

    beforeEach(() => {
        // Define Nat
        defineGlobal("Nat", Type(), undefined, true, true);
        Nat = Var("Nat");
        defineGlobal("z", Nat, undefined, true, true);
        z = Var("z");
        defineGlobal("s", Pi("n", Icit.Expl, Nat, _ => Nat), undefined, true, true);
        s = Var("s");
        one = App(s, z, Icit.Expl);
        two = App(s, one, Icit.Expl);
        defineGlobal("one", Nat, one);
        defineGlobal("two", Nat, two);

        // Define Eq {A} (x: A) (y: A) : Type
        defineGlobal("Eq",
            Pi("A", Icit.Impl, Type(), A =>
            Pi("x", Icit.Expl, A, _ =>
            Pi("y", Icit.Expl, A, _ => Type()))),
            undefined, true, true
        );
        Eq = Var("Eq");

        // Define refl : Π {A} {x}. Eq {A} x x
        defineGlobal("refl",
            Pi("A", Icit.Impl, Type(), A =>
            Pi("x", Icit.Impl, A, x =>
                App(App(App(Eq, A, Icit.Impl), x, Icit.Expl), x, Icit.Expl))),
            undefined, true, true
        );
        refl = Var("refl");
    });

    const EqNat = (x: Term, y: Term) => App(App(App(Eq, Nat, Icit.Impl), x, Icit.Expl), y, Icit.Expl);
    const reflNat = (x: Term) => App(App(refl, Nat, Icit.Impl), x, Icit.Impl);

    describe("Induction via Eliminator (J)", () => {
        beforeEach(() => {
            // J / Eq_elim
            const Eq_elim_type =
                Pi("A", Icit.Impl, Type(), A =>
                Pi("x", Icit.Impl, A, x =>
                Pi("P", Icit.Expl, Pi("y", Icit.Expl, A, y => Pi("p", Icit.Expl, App(App(App(Eq, A, Icit.Impl), x, Icit.Expl), y, Icit.Expl), _ => Type())), P =>
                Pi("p_refl", Icit.Expl, App(App(P, x, Icit.Expl), App(App(refl, A, Icit.Impl), x, Icit.Impl), Icit.Expl), _ =>
                Pi("y", Icit.Impl, A, y =>
                Pi("p", Icit.Expl, App(App(App(Eq, A, Icit.Impl), x, Icit.Expl), y, Icit.Expl), p_term =>
                    App(App(P, y, Icit.Expl), p_term, Icit.Expl)
                ))))));
            defineGlobal("Eq_elim", Eq_elim_type);

            // Rewrite rule for J: J applied to refl reduces to the provided refl-case proof
            addRewriteRule("Eq_elim_refl", ["$A", "$x", "$P", "$p_refl"],
                App(
                    App(
                        App(
                            App(
                                App(App(Var("Eq_elim"), Var("$A"), Icit.Impl), Var("$x"), Icit.Impl),
                                Var("$P"), Icit.Expl
                            ),
                            Var("$p_refl"), Icit.Expl
                        ),
                        Var("$x"), Icit.Impl
                    ),
                    App(App(refl, Var("$A"), Icit.Impl), Var("$x"), Icit.Impl), Icit.Expl
                ),
                Var("$p_refl"),
                emptyCtx
            );
        });

        it("should define symmetry (symm) using Eq_elim", () => {
            // symm : Π {A} {x y} (p: Eq x y) -> Eq y x
            const symm_type = Pi("A", Icit.Impl, Type(), A =>
                Pi("x", Icit.Impl, A, x =>
                Pi("y", Icit.Impl, A, y =>
                Pi("p", Icit.Expl, App(App(App(Eq, A, Icit.Impl), x, Icit.Expl), y, Icit.Expl), _ =>
                    App(App(App(Eq, A, Icit.Impl), y, Icit.Expl), x, Icit.Expl)
                ))));

            const symm_val =
                Lam("A", Icit.Impl, Type(), A =>
                Lam("x", Icit.Impl, A, x =>
                Lam("y", Icit.Impl, A, y =>
                Lam("p", Icit.Expl, App(App(App(Eq, A, Icit.Impl), x, Icit.Expl), y, Icit.Expl), p_val =>
                    App(
                        App(
                            App(
                                App(
                                    App(App(Var("Eq_elim"), A, Icit.Impl), x, Icit.Impl),
                                    // Motive P is: λ (y':A) (p': Eq x y') -> Eq y' x
                                    Lam("y_prime", Icit.Expl, A, y_prime =>
                                    Lam("p_prime", Icit.Expl, App(App(App(Eq, A, Icit.Impl), x, Icit.Expl), y_prime, Icit.Expl), _ =>
                                        App(App(App(Eq, A, Icit.Impl), y_prime, Icit.Expl), x, Icit.Expl)
                                    )), Icit.Expl
                                ),
                                // Proof for refl case: P x (refl x) -> Eq x x, which is refl x
                                App(App(refl, A, Icit.Impl), x, Icit.Impl), Icit.Expl
                            ),
                            y, Icit.Impl
                        ),
                        p_val, Icit.Expl
                    )
                ))));

            defineGlobal("symm_elim", symm_type, symm_val);

            // Test: symm (refl 1) ==> refl 1
            const term_to_eval = App(
                App(App(App(Var("symm_elim"), Nat, Icit.Impl), Var("one"), Icit.Impl), Var("one"), Icit.Impl),
                reflNat(Var("one")), Icit.Expl
            );
            const result = elaborate(term_to_eval);

            assert.ok(areEqual(result.type, EqNat(Var("one"), Var("one")), emptyCtx), `symm_elim (refl 1) should have type Eq 1 1. Got ${printTerm(result.type)}`);
            assert.ok(areEqual(result.term, reflNat(Var("one")), emptyCtx), `symm_elim (refl 1) should be refl 1. Got ${printTerm(result.term)}`);
        });

        it("should define transitivity (trans) using Eq_elim", () => {
            // trans : Π {A} {x y z} (p: Eq x y) (q: Eq y z) -> Eq x z
            const trans_type =
                Pi("A", Icit.Impl, Type(), A =>
                Pi("x", Icit.Impl, A, x =>
                Pi("y", Icit.Impl, A, y =>
                Pi("z", Icit.Impl, A, z =>
                Pi("p", Icit.Expl, App(App(App(Eq, A, Icit.Impl), x, Icit.Expl), y, Icit.Expl), _ =>
                Pi("q", Icit.Expl, App(App(App(Eq, A, Icit.Impl), y, Icit.Expl), z, Icit.Expl), _ =>
                    App(App(App(Eq, A, Icit.Impl), x, Icit.Expl), z, Icit.Expl)
                ))))));

            const trans_val =
                Lam("A", Icit.Impl, Type(), A =>
                Lam("x", Icit.Impl, A, x =>
                Lam("y", Icit.Impl, A, y =>
                Lam("z", Icit.Impl, A, z =>
                Lam("p", Icit.Expl, App(App(App(Eq, A, Icit.Impl), x, Icit.Expl), y, Icit.Expl), p_val =>
                Lam("q", Icit.Expl, App(App(App(Eq, A, Icit.Impl), y, Icit.Expl), z, Icit.Expl), q_val =>
                                   App(
                                       App(
                                           App(
                                               App(
                                    App(App(Var("Eq_elim"), A, Icit.Impl), y, Icit.Impl),
                                    // Motive P for induction on `q`: λ (z':A) (q': Eq y z') -> Eq x z'
                                    Lam("z_prime", Icit.Expl, A, z_prime =>
                                    Lam("q_prime", Icit.Expl, App(App(App(Eq, A, Icit.Impl), y, Icit.Expl), z_prime, Icit.Expl), _ =>
                                        App(App(App(Eq, A, Icit.Impl), x, Icit.Expl), z_prime, Icit.Expl)
                                    )), Icit.Expl
                                ),
                                // Proof for refl case: P y (refl y) -> Eq x y. We have `p` for this.
                                p_val, Icit.Expl
                            ),
                            z, Icit.Impl
                        ),
                        q_val, Icit.Expl
                    )
                ))))));

            defineGlobal("trans_elim", trans_type, trans_val);

            // Test: trans (refl 1) (refl 1) ==> refl 1
            const term_to_eval = App(App(
                App(App(App(App(Var("trans_elim"), Nat, Icit.Impl), Var("one"), Icit.Impl), Var("one"), Icit.Impl), Var("one"), Icit.Impl),
                reflNat(Var("one")), Icit.Expl
            ), reflNat(Var("one")), Icit.Expl);
            setDebugVerbose(true);
            const result = elaborate(term_to_eval);
            console.log("printTerm(result.term)", printTerm(result.term));
            assert.ok(areEqual(result.type, EqNat(Var("one"), Var("one")), emptyCtx));
            assert.ok(areEqual(result.term, reflNat(Var("one")), emptyCtx), `trans_elim (refl 1) (refl 1) should be (refl 1). Got ${printTerm(result.term)}`);
        });
    });

    describe("Induction via Rewrite Rules", () => {
        it("should define symmetry (symm) using rewrite rules", () => {
            const symm_type = Pi("A", Icit.Impl, Type(), A =>
                Pi("x", Icit.Impl, A, x =>
                Pi("y", Icit.Impl, A, y =>
                Pi("p", Icit.Expl, App(App(App(Eq, A, Icit.Impl), x, Icit.Expl), y, Icit.Expl), _ =>
                    App(App(App(Eq, A, Icit.Impl), y, Icit.Expl), x, Icit.Expl)
                ))));
            defineGlobal("symm_rw", symm_type);

            // symm (refl x) = refl x
            addRewriteRule("symm_rw_refl", ["$A", "$x"],
                App(
                    App(App(App(Var("symm_rw"), Var("$A"), Icit.Impl), Var("$x"), Icit.Impl), Var("$x"), Icit.Impl),
                    App(App(refl, Var("$A"), Icit.Impl), Var("$x"), Icit.Impl), Icit.Expl
                ),
                App(App(refl, Var("$A"), Icit.Impl), Var("$x"), Icit.Impl),
                emptyCtx
            );

            const term_to_eval = App(
                App(App(App(Var("symm_rw"), Nat, Icit.Impl), Var("one"), Icit.Impl), Var("one"), Icit.Impl),
                reflNat(Var("one")), Icit.Expl
            );
            const result = elaborate(term_to_eval);

            assert.ok(areEqual(result.term, reflNat(Var("one")), emptyCtx));
        });

        it("should define transitivity (trans) using rewrite rules", () => {
            const trans_type =
                Pi("A", Icit.Impl, Type(), A =>
                Pi("x", Icit.Impl, A, x =>
                Pi("y", Icit.Impl, A, y =>
                Pi("z", Icit.Impl, A, z =>
                Pi("p", Icit.Expl, App(App(App(Eq, A, Icit.Impl), x, Icit.Expl), y, Icit.Expl), _ =>
                Pi("q", Icit.Expl, App(App(App(Eq, A, Icit.Impl), y, Icit.Expl), z, Icit.Expl), _ =>
                    App(App(App(Eq, A, Icit.Impl), x, Icit.Expl), z, Icit.Expl)
                ))))));
            defineGlobal("trans_rw", trans_type);

            // trans (refl x) q = q
            addRewriteRule("trans_rw_refl", ["$A", "$x", "$z", "$q"],
                                                   App(
                                                       App(
                        App(App(App(App(Var("trans_rw"), Var("$A"), Icit.Impl), Var("$x"), Icit.Impl), Var("$x"), Icit.Impl), Var("$z"), Icit.Impl),
                        App(App(refl, Var("$A"), Icit.Impl), Var("$x"), Icit.Impl), Icit.Expl
                    ),
                    Var("$q"), Icit.Expl
                ),
                Var("$q"),
                emptyCtx
            );

            const term_to_eval = App(App(
                App(App(App(App(Var("trans_rw"), Nat, Icit.Impl), Var("one"), Icit.Impl), Var("one"), Icit.Impl), Var("one"), Icit.Impl),
                reflNat(Var("one")), Icit.Expl
            ), reflNat(Var("one")), Icit.Expl);
            const result = elaborate(term_to_eval);
            assert.ok(areEqual(result.term, reflNat(Var("one")), emptyCtx));
        });

        it("should define congruence (cong) using rewrite rules", () => {
            // cong : Π {A B} (f : A -> B) {x y} (p : Eq x y) -> Eq (f x) (f y)
            const cong_type =
                Pi("A", Icit.Impl, Type(), A =>
                Pi("B", Icit.Impl, Type(), B =>
                Pi("f", Icit.Expl, Pi("_", Icit.Expl, A, _ => B), f =>
                Pi("x", Icit.Impl, A, x =>
                Pi("y", Icit.Impl, A, y =>
                Pi("p", Icit.Expl, App(App(App(Eq, A, Icit.Impl), x, Icit.Expl), y, Icit.Expl), _ =>
                    App(
                        App(App(Eq, B, Icit.Impl), App(f, x, Icit.Expl), Icit.Expl),
                        App(f, y, Icit.Expl), Icit.Expl
                    )
                ))))));
            defineGlobal("cong_rw", cong_type);
            
            // cong f (refl x) = refl (f x)
            const f_var = Var("$f");
            const x_var = Var("$x");
            const A_var = Var("$A");
            const B_var = Var("$B");

            addRewriteRule("cong_rw_refl", ["$A", "$B", "$f", "$x"],
                App(
                    App(App(App(App(App(Var("cong_rw"), A_var, Icit.Impl), B_var, Icit.Impl), f_var, Icit.Expl), x_var, Icit.Impl), x_var, Icit.Impl),
                    App(App(refl, A_var, Icit.Impl), x_var, Icit.Impl), Icit.Expl
                ),
                App(
                    App(refl, B_var, Icit.Impl),
                    App(f_var, x_var, Icit.Expl), Icit.Impl
                ),
                emptyCtx
            );

            // test with `s : Nat -> Nat`
            const term_to_eval = App(
                App(App(App(App(App(Var("cong_rw"), Nat, Icit.Impl), Nat, Icit.Impl), s, Icit.Expl), Var("one"), Icit.Impl), Var("one"), Icit.Impl),
                reflNat(Var("one")), Icit.Expl
            );

            const result = elaborate(term_to_eval);
            
            // Expected result is `refl (s one)`, which is `refl two`.
            const expected_term = reflNat(Var("two"));

            assert.ok(areEqual(result.term, expected_term, emptyCtx), `cong s (refl 1) should be (refl 2), but got ${printTerm(result.term)}`);
        });
    });
}); 