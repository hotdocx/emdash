/**
 * @file tests/church_encoding_tests.ts
 * @description Tests for Church encodings of various data types.
 */
import {
    Term, Context, ElaborationResult, Icit,
    Type, Var, Lam, App, Pi, Hole
} from '../src/types';
import {
    emptyCtx, getTermRef, globalDefs, printTerm, FH
} from '../src/state';
import {
    defineGlobal
} from '../src/globals';
import {
    resetMyLambdaPi_Emdash
} from '../src/stdlib';
import {
    areEqual
} from '../src/equality';
import {
    elaborate, check
} from '../src/elaboration';
import { assert } from './utils';

import { describe, it } from 'node:test'; // Added for node:test
import { resetMyLambdaPi } from '../src/stdlib';

describe("Church Encoding Tests", () => {

    it("Test 1: Church encoding", () => {
        console.log("\n--- Running Church Encoding Tests ---");
        const baseCtx = emptyCtx;
        let elabRes: ElaborationResult;
    
        resetMyLambdaPi();
    
        // let id : (A : _) -> A -> A = \A x. x;
        const id_func_type_original = Pi("A_id_param", Icit.Expl, FH(), A_id_term => Pi("x_id_param", Icit.Expl, A_id_term, _x_id_term => A_id_term));
        const id_func_val = Lam("A_id_val", Icit.Expl, A_id_val_term => Lam("x_id_val", Icit.Expl, x_id_val_actual_term => x_id_val_actual_term));
        defineGlobal("id_func", id_func_type_original, id_func_val);
        elabRes = elaborate(Var("id_func"), undefined, baseCtx);
        const id_func_type_expected = Pi("A_id_param", Icit.Expl, Type(), A_id_term => Pi("x_id_param", Icit.Expl, A_id_term, _x_term => A_id_term));
        assert(areEqual(elabRes.type, id_func_type_expected, baseCtx), "Church Test 1.1: id_func type check");
    
        // let List : U -> U = \A. (L : _) -> (A -> L -> L) -> L -> L;
        const List_type_type = Pi("A_List_type_param", Icit.Expl, Type(), _A_List_type_term => Type());
        const List_type_val = Lam("A_List_val", Icit.Expl, A_List_val_term =>
            Pi("L_List_param", Icit.Expl, Type(), L_List_val_term =>
                Pi("cons_List_param", Icit.Expl, Pi("elem_type_in_cons", Icit.Expl, A_List_val_term, _ => Pi("list_type_in_cons", Icit.Expl, L_List_val_term, _ => L_List_val_term)), _cons_func_term =>
                    Pi("nil_List_param", Icit.Expl, L_List_val_term, _nil_actual_term => L_List_val_term)
                )
            )
        );
        defineGlobal("List_type", List_type_type, List_type_val);
        elabRes = elaborate(Var("List_type"), undefined, baseCtx);
        assert(areEqual(elabRes.type, List_type_type, baseCtx), "Church Test 2.1: List_type type check");
    
        // let nil : (A : _) -> List A = \A L cons nil_val. nil_val;
        const nil_func_type_original = Pi("A_nil_param", Icit.Expl, FH(), A_nil_term => App(Var("List_type"), A_nil_term, Icit.Expl));
        const nil_func_val = Lam("A_nil_val", Icit.Expl, A_nil_val_term =>
            Lam("L_nil_param", Icit.Expl, L_nil_val_term =>
                Lam("cons_nil_param", Icit.Expl, cons_func_term =>
                    Lam("nil_actual_val_param", Icit.Expl, nil_actual_val_term => nil_actual_val_term)
                )
            )
        );
        defineGlobal("nil_func", nil_func_type_original, nil_func_val);
        elabRes = elaborate(Var("nil_func"), undefined, baseCtx);
        const nil_func_type_expected = Pi("A_nil_param", Icit.Expl, Type(), A_nil_term => App(Var("List_type"), A_nil_term, Icit.Expl));
        assert(areEqual(elabRes.type, nil_func_type_expected, baseCtx), "Church Test 3.1: nil_func type check");
    
        // let cons : (A : _) -> A -> List A -> List A = \A x xs L cons_fn nil_fn. cons_fn x (xs _ cons_fn nil_fn);
        const cons_func_type_original = Pi("A_cons_param", Icit.Expl, FH(), A_cons_term =>
            Pi("x_cons_param", Icit.Expl, A_cons_term, _x_term =>
                Pi("xs_cons_param", Icit.Expl, App(Var("List_type"), A_cons_term, Icit.Expl), _xs_term =>
                    App(Var("List_type"), A_cons_term, Icit.Expl)
                )
            )
        );
        const cons_func_val = Lam("A_cons_val", Icit.Expl, A_cons_val_term =>
            Lam("x_cons_val", Icit.Expl, x_cons_actual_term =>
                Lam("xs_cons_val", Icit.Expl, xs_cons_actual_term =>
                    Lam("L_cons_param", Icit.Expl, L_cons_val_term =>
                        Lam("cons_fn_cons_param", Icit.Expl, cons_fn_actual_term =>
                            Lam("nil_fn_cons_param", Icit.Expl, nil_fn_actual_term =>
                                App(App(cons_fn_actual_term, x_cons_actual_term, Icit.Expl),
                                    App(App(App(xs_cons_actual_term, FH(), Icit.Expl), cons_fn_actual_term, Icit.Expl), nil_fn_actual_term, Icit.Expl),
                                    Icit.Expl
                                )
                            )
                        )
                    )
                )
            )
        );
        defineGlobal("cons_func", cons_func_type_original, cons_func_val);
        elabRes = elaborate(Var("cons_func"), undefined, baseCtx);
        const cons_func_type_expected = Pi("A_cons_param", Icit.Expl, Type(), A_cons_term =>
            Pi("x_cons_param", Icit.Expl, A_cons_term, _x_term =>
                Pi("xs_cons_param", Icit.Expl, App(Var("List_type"), A_cons_term, Icit.Expl), _xs_term =>
                    App(Var("List_type"), A_cons_term, Icit.Expl)
                )
            )
        );
        assert(areEqual(elabRes.type, cons_func_type_expected, baseCtx), "Church Test 4.1: cons_func type check");
    
        // let Bool : U = (B : _) -> B -> B -> B;
        const Bool_type_val_original_with_FH = Pi("B_Bool_param", Icit.Expl, FH(), B_Bool_term =>
            Pi("t_Bool_param", Icit.Expl, B_Bool_term, _t_term =>
                Pi("f_Bool_param", Icit.Expl, B_Bool_term, _f_term => B_Bool_term)
            )
        );
        defineGlobal("Bool_type", Type(), Bool_type_val_original_with_FH);
        elabRes = elaborate(Var("Bool_type"), undefined, baseCtx);
        assert(areEqual(elabRes.type, Type(), baseCtx), "Church Test 5.1: Bool_type type check");
    
        // let true : Bool = \B t f. t;
        const true_val_val = Lam("B_true_param", Icit.Expl, B_true_term =>
            Lam("t_true_param", Icit.Expl, t_true_actual_term =>
                Lam("f_true_param", Icit.Expl, _f_actual_term => t_true_actual_term)
            )
        );
        defineGlobal("true_val", Var("Bool_type"), true_val_val);
        elabRes = elaborate(Var("true_val"), undefined, baseCtx);
        assert(areEqual(elabRes.type, Var("Bool_type"), baseCtx), "Church Test 6.1: true_val type check");
    
        // let false : Bool = \B t f. f;
        const false_val_val = Lam("B_false_param", Icit.Expl, B_false_term =>
            Lam("t_false_param", Icit.Expl, _t_actual_term =>
                Lam("f_false_param", Icit.Expl, f_false_actual_term => f_false_actual_term)
            )
        );
        defineGlobal("false_val", Var("Bool_type"), false_val_val);
        elabRes = elaborate(Var("false_val"), undefined, baseCtx);
        assert(areEqual(elabRes.type, Var("Bool_type"), baseCtx), "Church Test 7.1: false_val type check");
    
        // let not : Bool -> Bool = \b B t f. b B f t;
        const not_func_type = Pi("b_not_param", Icit.Expl, Var("Bool_type"), _b_term => Var("Bool_type"));
        const not_func_val = Lam("b_not_val", Icit.Expl, b_not_actual_term =>
            Lam("B_not", Icit.Expl, Type(), B_not_term =>
                Lam("t_not", Icit.Expl, B_not_term, t_not_actual_term =>
                    Lam("f_not", Icit.Expl, B_not_term, f_not_actual_term =>
                        App(App(App(b_not_actual_term, B_not_term, Icit.Expl), f_not_actual_term, Icit.Expl), t_not_actual_term, Icit.Expl)
                    )
                )
            )
        );
        defineGlobal("not_func", not_func_type, not_func_val);
        elabRes = elaborate(Var("not_func"), undefined, baseCtx);
        assert(areEqual(elabRes.type, not_func_type, baseCtx), "Church Test 8.1: not_func type check");
        console.log(printTerm(elabRes.term));
        console.log(printTerm(check(baseCtx, not_func_val, not_func_type)));
        assert(areEqual(elabRes.term, check(baseCtx, not_func_val, not_func_type), baseCtx), "Church Test 8.2: not_func value check");
    
        // let list1 : List Bool = cons _ (id _ true) (nil _);
        const list1_val_type = App(Var("List_type"), Var("Bool_type"), Icit.Expl);
        const list1_val_val = App(
            App(App(Var("cons_func"), FH(), Icit.Expl), 
                App(App(Var("id_func"), FH(), Icit.Expl), Var("true_val"), Icit.Expl), 
                Icit.Expl
            ),
            App(Var("nil_func"), FH(), Icit.Expl), 
            Icit.Expl
        );
        defineGlobal("list1_val", list1_val_type, list1_val_val);
        elabRes = elaborate(Var("list1_val"), undefined, baseCtx);
        assert(areEqual(elabRes.type, list1_val_type, baseCtx), "Church Test 9.1: list1_val type check");
    
        // let Eq : (A : _) -> A -> A -> U = \A x y. (P : A -> U) -> P x -> P y;
        const Eq_type_type_original = Pi("A_Eq_param", Icit.Expl, FH(), A_Eq_term =>
            Pi("x_Eq_param", Icit.Expl, A_Eq_term, _x_term =>
                Pi("y_Eq_param", Icit.Expl, A_Eq_term, _y_term => Type())
            )
        );
        const Eq_type_val = Lam("A_Eq_val", Icit.Expl, A_Eq_val_term =>
            Lam("x_Eq_val", Icit.Expl, x_Eq_actual_term =>
                Lam("y_Eq_val", Icit.Expl, y_Eq_actual_term =>
                    Pi("P_Eq_param", Icit.Expl, Pi("ignored_P_arg", Icit.Expl, A_Eq_val_term, _ => Type()), P_Eq_val_term =>
                        Pi("Px_Eq_param", Icit.Expl, App(P_Eq_val_term, x_Eq_actual_term, Icit.Expl), _Px_val_term =>
                            App(P_Eq_val_term, y_Eq_actual_term, Icit.Expl)
                        )
                    )
                )
            )
        );
        defineGlobal("Eq_type", Eq_type_type_original, Eq_type_val);
        elabRes = elaborate(Var("Eq_type"), undefined, baseCtx);
        const Eq_type_type_expected = Pi("A_Eq_param", Icit.Expl, Type(), A_Eq_term =>
            Pi("x_Eq_param", Icit.Expl, A_Eq_term, _x_term =>
                Pi("y_Eq_param", Icit.Expl, A_Eq_term, _y_term => Type())
            )
        );
        assert(areEqual(elabRes.type, Eq_type_type_expected, baseCtx), "Church Test 10.1: Eq_type type check");
    
        // let refl : (A : _)(x : A) -> Eq A x x = \A x P px. px;
        const refl_func_type_original = Pi("A_refl_param", Icit.Expl, FH(), A_refl_term =>
            Pi("x_refl_param", Icit.Expl, A_refl_term, x_refl_term =>
                App(App(App(Var("Eq_type"), A_refl_term, Icit.Expl), x_refl_term, Icit.Expl), x_refl_term, Icit.Expl)
            )
        );
        const refl_func_val = Lam("A_refl_val", Icit.Expl, A_refl_val_term =>
            Lam("x_refl_val", Icit.Expl, x_refl_actual_term =>
                Lam("P_refl_param", Icit.Expl, _P_val_term =>
                    Lam("Px_refl_param", Icit.Expl, Px_refl_actual_term =>
                        Px_refl_actual_term
                    )
                )
            )
        );
        defineGlobal("refl_func", refl_func_type_original, refl_func_val);
        elabRes = elaborate(Var("refl_func"), undefined, baseCtx);
        const refl_func_type_expected = Pi("A_refl_param", Icit.Expl, Type(), A_refl_term =>
            Pi("x_refl_param", Icit.Expl, A_refl_term, x_refl_term =>
                App(App(App(Var("Eq_type"), A_refl_term, Icit.Expl), x_refl_term, Icit.Expl), x_refl_term, Icit.Expl)
            )
        );
        assert(areEqual(elabRes.type, refl_func_type_expected, baseCtx), "Church Test 11.1: refl_func type check");
    
        // let list1_v2 : List Bool = cons _ true (cons _ false (nil _)); (renamed list1 to list1_v2)
        const list1_v2_val_type = App(Var("List_type"), Var("Bool_type"), Icit.Expl);
        const list1_v2_val_val = App(
            App(App(Var("cons_func"), FH(), Icit.Expl), Var("true_val"), Icit.Expl),
            App(
                App(App(Var("cons_func"), FH(), Icit.Expl), Var("false_val"), Icit.Expl),
                App(Var("nil_func"), FH(), Icit.Expl),
                Icit.Expl
            ),
            Icit.Expl
        );
        defineGlobal("list1_v2_val", list1_v2_val_type, list1_v2_val_val);
        elabRes = elaborate(Var("list1_v2_val"), undefined, baseCtx);
        assert(areEqual(elabRes.type, list1_v2_val_type, baseCtx), "Church Test 12.1: list1_v2_val type check");
    
        // let Nat  : U = (N : U) -> (N -> N) -> N -> N;
        const Nat_type_val = Pi("N_Nat_param", Icit.Expl, Type(), N_Nat_term =>
            Pi("s_Nat_param", Icit.Expl, Pi("arg_s_Nat", Icit.Expl, N_Nat_term, _ => N_Nat_term), _s_term =>
                Pi("z_Nat_param", Icit.Expl, N_Nat_term, _z_term => N_Nat_term)
            )
        );
        defineGlobal("Nat_type", Type(), Nat_type_val);
        elabRes = elaborate(Var("Nat_type"), undefined, baseCtx);
        assert(areEqual(elabRes.type, Type(), baseCtx), "Church Test 13.1: Nat_type type check");
    
        // let five : Nat = \N s z. s (s (s (s (s z))));
        const five_val_val = Lam("N_five_param", Icit.Expl, N_five_term =>
            Lam("s_five_param", Icit.Expl, s_five_actual_term =>
                Lam("z_five_param", Icit.Expl, z_five_actual_term =>
                    App(s_five_actual_term, App(s_five_actual_term, App(s_five_actual_term, App(s_five_actual_term, App(s_five_actual_term, z_five_actual_term, Icit.Expl), Icit.Expl), Icit.Expl), Icit.Expl), Icit.Expl)
                )
            )
        );
        defineGlobal("five_val", Var("Nat_type"), five_val_val);
        elabRes = elaborate(Var("five_val"), undefined, baseCtx);
        assert(areEqual(elabRes.type, Var("Nat_type"), baseCtx), "Church Test 14.1: five_val type check");
    
        // let add  : Nat -> Nat -> Nat = \a b N s z. a N s (b N s z);
        const add_func_type = Pi("a_add_param", Icit.Expl, Var("Nat_type"), _a_term =>
            Pi("b_add_param", Icit.Expl, Var("Nat_type"), _b_term => Var("Nat_type"))
        );
        const add_func_val = Lam("a_add_val", Icit.Expl, a_add_actual_term =>
            Lam("b_add_val", Icit.Expl, b_add_actual_term =>
                Lam("N_add_param", Icit.Expl, N_add_term =>
                    Lam("s_add_param", Icit.Expl, s_add_actual_term =>
                        Lam("z_add_param", Icit.Expl, z_add_actual_term =>
                            App(App(App(a_add_actual_term, N_add_term, Icit.Expl), s_add_actual_term, Icit.Expl),
                                App(App(App(b_add_actual_term, N_add_term, Icit.Expl), s_add_actual_term, Icit.Expl), z_add_actual_term, Icit.Expl),
                                Icit.Expl
                            )
                        )
                    )
                )
            )
        );
        defineGlobal("add_func", add_func_type, add_func_val);
        elabRes = elaborate(Var("add_func"), undefined, baseCtx);
        assert(areEqual(elabRes.type, add_func_type, baseCtx), "Church Test 15.1: add_func type check");
    
        // let mul  : Nat -> Nat -> Nat = \a b N s z. a N (b N s) z;
        const mul_func_type = Pi("a_mul_param", Icit.Expl, Var("Nat_type"), _a_term =>
            Pi("b_mul_param", Icit.Expl, Var("Nat_type"), _b_term => Var("Nat_type"))
        );
        const mul_func_val = Lam("a_mul_val", Icit.Expl, a_mul_actual_term =>
            Lam("b_mul_val", Icit.Expl, b_mul_actual_term =>
                Lam("N_mul_param", Icit.Expl, N_mul_term =>
                    Lam("s_mul_param", Icit.Expl, s_mul_actual_term =>
                        Lam("z_mul_param", Icit.Expl, z_mul_actual_term =>
                            App(App(App(a_mul_actual_term, N_mul_term, Icit.Expl),
                                    App(App(b_mul_actual_term, N_mul_term, Icit.Expl), s_mul_actual_term, Icit.Expl),
                                    Icit.Expl
                                ),
                                z_mul_actual_term,
                                Icit.Expl
                            )
                        )
                    )
                )
            )
        );
        defineGlobal("mul_func", mul_func_type, mul_func_val);
        elabRes = elaborate(Var("mul_func"), undefined, baseCtx);
        assert(areEqual(elabRes.type, mul_func_type, baseCtx), "Church Test 16.1: mul_func type check");
    
        // let ten : Nat = add five five;
        const ten_val_val = App(App(Var("add_func"), Var("five_val"), Icit.Expl), Var("five_val"), Icit.Expl);
        defineGlobal("ten_val", Var("Nat_type"), ten_val_val);
        elabRes = elaborate(Var("ten_val"), undefined, baseCtx);
        assert(areEqual(elabRes.type, Var("Nat_type"), baseCtx), "Church Test 17.1: ten_val type check");
    
        // let hundred : Nat = mul ten ten;
        const hundred_val_val = App(App(Var("mul_func"), Var("ten_val"), Icit.Expl), Var("ten_val"), Icit.Expl);
        defineGlobal("hundred_val", Var("Nat_type"), hundred_val_val);
        elabRes = elaborate(Var("hundred_val"), undefined, baseCtx);
        assert(areEqual(elabRes.type, Var("Nat_type"), baseCtx), "Church Test 17.2: hundred_val type check");
    
        // let thousand : Nat = mul ten hundred;
        const thousand_val_val = App(App(Var("mul_func"), Var("ten_val"), Icit.Expl), Var("hundred_val"), Icit.Expl);
        defineGlobal("thousand_val", Var("Nat_type"), thousand_val_val);
        elabRes = elaborate(Var("thousand_val"), undefined, baseCtx);
        assert(areEqual(elabRes.type, Var("Nat_type"), baseCtx), "Church Test 17.3: thousand_val type check");
    
        // [TODO] uncomment later
        // // let eqTest : Eq _ hundred hundred = refl _ _;
        const eqTest_val_type_original = App(App(App(Var("Eq_type"), Var("Nat_type"), Icit.Expl), Var("hundred_val"), Icit.Expl), Var("hundred_val"), Icit.Expl);
        const eqTest_val_val = App(App(Var("refl_func"), Var("Nat_type"), Icit.Expl), FH(), Icit.Expl);
        // SLOW ~ 100s, uncomment later
        defineGlobal("eqTest_val", eqTest_val_type_original, eqTest_val_val);
        elabRes = elaborate(Var("eqTest_val"), undefined, baseCtx);
    
        // const eqTest_val_term = Var("eqTest_val");
        // const eqTest_val_type_expected = App(App(App(Var("Eq_type"), Var("Nat_type"), Icit.Expl), Var("hundred_val"), Icit.Expl), Var("hundred_val"), Icit.Expl);
        // const gdef = globalDefs.get("eqTest_val");
        // console.log(`[DEBUG TEST 18.1] gdef type: ${printTerm(gdef.type)}`);
        // console.log(`[DEBUG TEST 18.1] gdef value: ${printTerm(gdef.value)}`);
        // console.log(`[DEBUG TEST 18.1] eqTest_val_term: ${printTerm(normalize(Var("eqTest_val"), baseCtx))}`);
        // console.log(`[DEBUG TEST 18.1] elabRes.type: ${printTerm(elabRes.type)}`);
        // console.log(`[DEBUG TEST 18.1] eqTest_val_type_expected: ${printTerm(eqTest_val_type_expected)}`);
        // const n1_debug_18_1 = whnf(elabRes.type, baseCtx);
        // const n2_debug_18_1 = whnf(eqTest_val_type_expected, baseCtx);
        // console.log(`[DEBUG TEST 18.1] whnf(elabRes.type): ${printTerm(n1_debug_18_1)}`);
        // console.log(`[DEBUG TEST 18.1] whnf(eqTest_val_type_expected): ${printTerm(n2_debug_18_1)}`);
        // const isEqualDebug_18_1 = areEqual(elabRes.type, eqTest_val_type_expected, baseCtx);
        // console.log(`[DEBUG TEST 18.1] areEqual result: ${isEqualDebug_18_1}`);
    
        assert(areEqual(elabRes.type, eqTest_val_type_original, baseCtx), "Church Test 18.1: eqTest_val type check");
    
        // U
        elabRes = elaborate(Type(), undefined, baseCtx);
        assert(elabRes.type.tag === 'Type', "Church Test 19.1: U (Type) elaborates to type Type");
        assert(elabRes.term.tag === 'Type', "Church Test 19.2: U (Type) elaborates to term Type");
    
    
        console.log("\n--- Test: FH() in Pi type resolves correctly (Church Test 20) ---");
        // Test: Π A_type : Type. Π A_val : A_type. Π P : (Π ignored_P_arg : FH(). Type). P A_val
        // Expected: FH() resolves to A_type_term (i.e., Var(A_type_param_name_fh))
        // The overall type of the expression is Type.
        // Note: runChurchEncodingTests calls resetMyLambdaPi() at its start, so globals are fresh-ish but accumulate.
        // This test uses unique names to avoid clashes.
    
        const A_type_param_name_fh = "A_type_for_FH_test_20";
        const A_val_param_name_fh = "A_val_for_FH_test_20";
        const P_param_name_fh = "P_for_FH_test_20";
        const ignored_P_arg_name_fh = "ignored_P_arg_for_FH_test_20";
    
        const fh_hole_instance = FH(); // This is the specific hole we're interested in.
    
        const P_param_type_decl_fh = Pi(ignored_P_arg_name_fh, Icit.Expl, fh_hole_instance, _ => Type());
    
        const term_FH_test = Pi(A_type_param_name_fh, Icit.Expl, Type(), A_type_term =>
            Pi(A_val_param_name_fh, Icit.Expl, A_type_term, A_val_term =>
                Pi(P_param_name_fh, Icit.Expl, P_param_type_decl_fh, P_term =>
                    App(P_term, A_val_term, Icit.Expl)
                )
            )
        );
    
        elabRes = elaborate(term_FH_test, undefined, baseCtx); // Expect overall type to be Type
        assert(areEqual(elabRes.type, Type(), baseCtx), "Church Test 20.1: Overall expression type is Type");
    
        const elaborated_term_FH = getTermRef(elabRes.term);
        assert(elaborated_term_FH.tag === 'Pi', "Church Test 20.2: Elaborated term is a Pi (A_type level)");
    
        const Pi_Atype_elab = elaborated_term_FH as Term & { tag: 'Pi' };
        // paramType of Pi_Atype_elab is Type(), implicitly checked by 20.1 via overall type being Type.
    
        const Pi_Aval_elab_struct = getTermRef(Pi_Atype_elab.bodyType(Var(Pi_Atype_elab.paramName)));
        assert(Pi_Aval_elab_struct.tag === 'Pi', "Church Test 20.3: Body of A_type Pi is a Pi (A_val level)");
    
        const Pi_Aval_elab = Pi_Aval_elab_struct as Term & { tag: 'Pi' };
        const expected_Aval_paramType = Var(Pi_Atype_elab.paramName); // This is Var(A_type_param_name_fh)
        assert(areEqual(getTermRef(Pi_Aval_elab.paramType), expected_Aval_paramType, baseCtx), `Church Test 20.4: A_val param type is ${Pi_Atype_elab.paramName}. Expected ${printTerm(expected_Aval_paramType)}, Got ${printTerm(getTermRef(Pi_Aval_elab.paramType))}`);
    
        const Pi_P_elab_struct = getTermRef(Pi_Aval_elab.bodyType(Var(Pi_Aval_elab.paramName)));
        assert(Pi_P_elab_struct.tag === 'Pi', "Church Test 20.5: Body of A_val Pi is a Pi (P level)");
    
        const Pi_P_elab = Pi_P_elab_struct as Term & { tag: 'Pi' };
        const P_param_type_elab = getTermRef(Pi_P_elab.paramType);
        assert(P_param_type_elab.tag === 'Pi', `Church Test 20.6: P param type is a Pi (ignored_P level). Got ${P_param_type_elab.tag}`);
    
        const Pi_ignored_elab = P_param_type_elab as Term & { tag: 'Pi' };
        const ignored_param_type_elab = getTermRef(Pi_ignored_elab.paramType);
    
        assert(areEqual(ignored_param_type_elab, expected_Aval_paramType, baseCtx), `Church Test 20.7: fh_hole resolved to ${Pi_Atype_elab.paramName}. Expected ${printTerm(expected_Aval_paramType)}, Got ${printTerm(ignored_param_type_elab)}`);
    
        const resolved_fh_direct = getTermRef(fh_hole_instance);
        assert(areEqual(resolved_fh_direct, expected_Aval_paramType, baseCtx), `Church Test 20.8: Direct check of fh_hole_instance.ref resolved to ${Pi_Atype_elab.paramName}. Expected ${printTerm(expected_Aval_paramType)}, Got ${printTerm(resolved_fh_direct)}`);
    
        const P_body_elab_struct = getTermRef(Pi_P_elab.bodyType(Var(Pi_P_elab.paramName)));
        assert(P_body_elab_struct.tag === 'App', "Church Test 20.9: Body of P Pi is an App");
        const App_P_Aval_elab = P_body_elab_struct as Term & {tag: 'App'};
        assert(App_P_Aval_elab.func.tag === 'Var' && (App_P_Aval_elab.func as Term & {tag:'Var'}).name === Pi_P_elab.paramName, `Church Test 20.10: App func is P. Expected ${Pi_P_elab.paramName}, Got ${(App_P_Aval_elab.func as any).name}`);
        assert(App_P_Aval_elab.arg.tag === 'Var' && (App_P_Aval_elab.arg as Term & {tag:'Var'}).name === Pi_Aval_elab.paramName, `Church Test 20.11: App arg is A_val. Expected ${Pi_Aval_elab.paramName}, Got ${(App_P_Aval_elab.arg as any).name}`);
    
        console.log("Church Test 20 (FH in Pi type resolution) completed.");
    
        console.log("\n--- Test: FH() in Pi type resolves correctly with Globals (Church Test 21) ---");
        // Test: Π Q : (Π ignored_Q_arg : FH(). Type). Q five_val
        // Expected: FH() resolves to Var("Nat_type")
        // The overall type of the expression is Type.
        // Assumes Nat_type and five_val are globally defined from earlier in Church Encoding tests.
    
        const Q_param_name_fh21 = "Q_for_FH_test_21";
        const ignored_Q_arg_name_fh21 = "ignored_Q_arg_for_FH_test_21";
    
        const fh_hole_instance_21 = FH(); // This is the specific hole we're interested in for Test 21.
        const five_val_global_ref = Var("five_val"); // Reference to the global five_val
        const nat_type_global_ref = Var("Nat_type"); // Reference to the global Nat_type
    
        const Q_param_type_decl_fh21 = Pi(ignored_Q_arg_name_fh21, Icit.Expl, fh_hole_instance_21, _ => Type());
    
        const term_FH_test_21 = Pi(Q_param_name_fh21, Icit.Expl, Q_param_type_decl_fh21, Q_term =>
            App(Q_term, five_val_global_ref, Icit.Expl)
        );
    
        const elabRes21 = elaborate(term_FH_test_21, undefined, baseCtx); // Expect overall type to be Type
        assert(areEqual(elabRes21.type, Type(), baseCtx), "Church Test 21.1: Overall expression type is Type");
    
        const elaborated_term_FH21 = getTermRef(elabRes21.term);
        assert(elaborated_term_FH21.tag === 'Pi', "Church Test 21.2: Elaborated term is a Pi (Q level)");
    
        const Pi_Q_elab21 = elaborated_term_FH21 as Term & { tag: 'Pi' };
        const Q_param_type_elab21 = getTermRef(Pi_Q_elab21.paramType);
        assert(Q_param_type_elab21.tag === 'Pi', `Church Test 21.3: Q param type is a Pi (ignored_Q level). Got ${Q_param_type_elab21.tag}`);
    
        const Pi_ignored_elab21 = Q_param_type_elab21 as Term & { tag: 'Pi' };
        const resolved_hole_in_Q_param_type = getTermRef(Pi_ignored_elab21.paramType);
    
        assert(areEqual(resolved_hole_in_Q_param_type, nat_type_global_ref, baseCtx), `Church Test 21.4: fh_hole_instance_21 resolved to Nat_type. Expected ${printTerm(nat_type_global_ref)}, Got ${printTerm(resolved_hole_in_Q_param_type)}`);
    
        const resolved_fh_direct_21 = getTermRef(fh_hole_instance_21);
        assert(areEqual(resolved_fh_direct_21, nat_type_global_ref, baseCtx), `Church Test 21.5: Direct check of fh_hole_instance_21.ref resolved to Nat_type. Expected ${printTerm(nat_type_global_ref)}, Got ${printTerm(resolved_fh_direct_21)}`);
        
        // Check the body of the Pi for Q
        const Q_body_elab21 = getTermRef(Pi_Q_elab21.bodyType(Var(Pi_Q_elab21.paramName)));
        const Q_body_expected = App(Var(Q_param_name_fh21), five_val_global_ref, Icit.Expl);
        assert(areEqual(Q_body_elab21, Q_body_expected, baseCtx), `Church Test 21.6: Body type of Pi Q . Expected ${printTerm(Q_body_expected)}, Got ${printTerm(Q_body_elab21)}`);
    
        console.log("Church Test 21 (FH in Pi type with Globals resolution) completed.");
    
        console.log("Church Encoding Tests Completed.");
    });
});