/**
 * @file tests/church_encoding_tests.ts
 * @description Tests for Church encodings of various data types.
 */
import {
    Term, Context, ElaborationResult, Icit,
    Type, Var, Lam, App, Pi, Hole,
    UnifyResult
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
    areEqual,
} from '../src/equality';
import {
    normalize,
} from '../src/reduction';
import {
    unify
} from '../src/unification';
import {
    elaborate, check
} from '../src/elaboration';
import { assert } from './utils';

import { describe, it } from 'node:test'; // Added for node:test
import { resetMyLambdaPi } from '../src/stdlib';

describe("Church Encoding Implicit Tests", () => {

    it("Test 1: Church encoding Implicit", () => {
        console.log("\n--- Running Church-Style Implicit Argument Tests (from Haskell examples) ---");
        const baseCtx = emptyCtx;
        let elabRes: ElaborationResult;
    
        resetMyLambdaPi(); // Resets globals, constraints, hole/var ids
    
        // --- Bool --- T = (B : _) -> B -> B -> B;
        const Bool_type_val = Pi("B_param", Icit.Expl, Type(), B_term =>
            Pi("t_param", Icit.Expl, B_term, _t_term =>
                Pi("f_param", Icit.Expl, B_term, _f_term => B_term)
            )
        );
        defineGlobal("Bool", Type(), Bool_type_val);
        elabRes = elaborate(Var("Bool"), undefined, baseCtx);
        assert(areEqual(elabRes.type, Type(), baseCtx), "HSI Test 1.1: Bool type check");
        assert(unify(elabRes.term, Bool_type_val, baseCtx) === UnifyResult.Solved, "HSI Test 1.2: Bool value check");
    
        // true = \B t f. t;    // BE CAREFUL, non-annotated : Boool, only to be used as shorthand
        // its type is: (Π (B_true : Type). (Π (t_true : ?h0_lam_t_true_paramT_infer_(:Type)). (Π (f_true : ?h1_lam_f_true_paramT_infer_(:Type)). ?h0_lam_t_true_paramT_infer_(:Type))))
        const true_val_val = Lam("B_true", Icit.Expl, B_true_term =>
            Lam("t_true", Icit.Expl, t_true_actual_term =>
                Lam("f_true", Icit.Expl, _f_actual_term => t_true_actual_term)
            )
        );
        defineGlobal("true_hs", Var("Bool"), true_val_val);
        elabRes = elaborate(Var("true_hs"), undefined, baseCtx);
        assert(areEqual(elabRes.type, Var("Bool"), baseCtx), "HSI Test 2.1: true_hs type check");
        assert(areEqual(normalize(elabRes.term, baseCtx), normalize(check(baseCtx, true_val_val, Var("Bool")), baseCtx), baseCtx), "HSI Test 2.2: true_hs value check");
    
        // false = \B t f. f;
        const false_val_val = Lam("B_false", Icit.Expl, B_false_term =>
            Lam("t_false", Icit.Expl, _t_actual_term =>
                Lam("f_false", Icit.Expl, f_false_actual_term => f_false_actual_term)
            )
        );
        defineGlobal("false_hs", Var("Bool"), false_val_val);
        elabRes = elaborate(Var("false_hs"), undefined, baseCtx);
        assert(areEqual(elabRes.type, Var("Bool"), baseCtx), "HSI Test 3.1: false_hs type check");
        assert(areEqual(normalize(elabRes.term, baseCtx), normalize(check(baseCtx, false_val_val, Var("Bool")), baseCtx), baseCtx), "HSI Test 3.2: false_hs value check");
    
        // not = \b B t f. b B f t;  // BE CAREFUL, non-annotated : Bool -> Bool, only to be used as shorthand
        const not_func_type = Pi("b_not_param", Icit.Expl, Var("Bool"), _b_term => Var("Bool"));
        const not_func_val = Lam("b_not_val", Icit.Expl, Var("Bool"), b_not_actual_term =>
            Lam("B_not", Icit.Expl, Type(), B_not_term =>
                Lam("t_not", Icit.Expl, B_not_term, t_not_actual_term =>
                    Lam("f_not", Icit.Expl, B_not_term, f_not_actual_term =>
                        App(App(App(b_not_actual_term, B_not_term, Icit.Expl), f_not_actual_term, Icit.Expl), t_not_actual_term, Icit.Expl)
                    )
                )
            )
        );
        defineGlobal("not_hs", not_func_type, not_func_val);
        elabRes = elaborate(Var("not_hs"), undefined, baseCtx);
        assert(areEqual(elabRes.type, not_func_type, baseCtx), "HSI Test 4.1: not_hs type check");
        assert(areEqual(elabRes.term, check(baseCtx, not_func_val, not_func_type), baseCtx), "HSI Test 4.2: not_hs value check");
    
        // --- Lists --- 
        // let List : U -> U
        // = \A. (L : _) -> (A -> L -> L) -> L -> L;
        const List_type_constructor_type = Pi("A_List_type_param", Icit.Expl, Type(), _A_List_type_term => Type());
        const List_type_constructor_val = Lam("A_List_val", Icit.Expl, Type(), A_List_val_term => 
            Pi("L_List_param", Icit.Expl, Type(), L_List_val_term => 
                Pi("cons_List_param", Icit.Expl, Pi("elem_type_in_cons", Icit.Expl, A_List_val_term, _ => Pi("list_type_in_cons", Icit.Expl, L_List_val_term, _ => L_List_val_term)), _cons_func_term =>
                    Pi("nil_List_param", Icit.Expl, L_List_val_term, _nil_actual_term => L_List_val_term)
                )
            )
        );
        defineGlobal("List_hs", List_type_constructor_type, List_type_constructor_val); 
        elabRes = elaborate(Var("List_hs"), undefined, baseCtx);
        assert(areEqual(elabRes.type, List_type_constructor_type, baseCtx), "HSI Test 5.1: List_hs type check");
        assert(areEqual(elabRes.term, List_type_constructor_val, baseCtx), "HSI Test 5.2: List_hs value check");
    
        // let nil : {A} -> List A
        // = \L cons nil. nil;
        const nil_func_type = Pi("A_nil_param", Icit.Impl, Type(), A_nil_term => App(Var("List_hs"), A_nil_term, Icit.Expl));
        const nil_func_val_raw = Lam("L_nil_param", Icit.Expl, L_nil_val_term =>
            Lam("cons_nil_param", Icit.Expl, _cons_func_term =>  
                Lam("nil_actual_val_param", Icit.Expl, nil_actual_val_term => nil_actual_val_term)
            )
        );
        const nil_func_val_elab_expected = Lam("A_nil_impl", Icit.Impl, Type(), A_val =>
            Lam("L_nil_expl", Icit.Expl, Type(), L_val =>
                Lam("c_nil_expl", Icit.Expl, Pi("_elem", Icit.Expl, A_val, _ => Pi("_list", Icit.Expl, L_val, _ => L_val)), _c_val => 
                    Lam("n_nil_expl", Icit.Expl, L_val, n_val => n_val) 
                )
            )
        );
        defineGlobal("nil_hs", nil_func_type, nil_func_val_raw); 
        elabRes = elaborate(Var("nil_hs"), undefined, baseCtx); 
        // NOTE: the non-fully-elaborated no-implicit-insertions `nil_hs` is available from globalDefs.get("nil_hs")
        assert(unify(elabRes.type, App(Var("List_hs"), FH(), Icit.Expl), baseCtx) === UnifyResult.Solved, "HSI Test 6.1: nil_hs type check");
        const globalNilHsDef = globalDefs.get("nil_hs")!
        // console.log({globalNilHsDef});
        assert(areEqual(globalNilHsDef.value,  nil_func_val_elab_expected, baseCtx), "HSI Test 6.2: nil_hs value check against non-fully elaborated form (no implicit insertions) ");
    
        // let cons : {A} -> A -> List A -> List A
        // = \x xs L cons nil. cons x (xs L cons nil);
        const cons_func_type = Pi("A_cons_param", Icit.Impl, Type(), A_cons_term =>
            Pi("x_cons_param", Icit.Expl, A_cons_term, _x_term =>
                Pi("xs_cons_param", Icit.Expl, App(Var("List_hs"), A_cons_term, Icit.Expl), _xs_term =>
                    App(Var("List_hs"), A_cons_term, Icit.Expl)
                )
            )
        );
        const cons_func_val_raw = Lam("x_cons_val", Icit.Expl, x_cons_actual_term => 
            Lam("xs_cons_val", Icit.Expl, xs_cons_actual_term => 
                Lam("L_cons_param", Icit.Expl, L_cons_val_term => 
                    Lam("cons_fn_cons_param", Icit.Expl, cons_fn_actual_term => 
                        Lam("nil_fn_cons_param", Icit.Expl, nil_fn_actual_term => 
                            App(App(cons_fn_actual_term, x_cons_actual_term, Icit.Expl), 
                                App(App(App(xs_cons_actual_term, L_cons_val_term, Icit.Expl), cons_fn_actual_term, Icit.Expl), nil_fn_actual_term, Icit.Expl), 
                                Icit.Expl
                            )
                        )
                    )
                )
            )
        );
        const cons_func_val_elab_expected = Lam("A_impl", Icit.Impl, Type(), A_term =>
            Lam("x_expl", Icit.Expl, A_term, x_term =>
                Lam("xs_expl", Icit.Expl, App(Var("List_hs"), A_term, Icit.Expl), xs_term =>
                    Lam("L_expl", Icit.Expl, Type(), L_term =>
                        Lam("c_expl", Icit.Expl, Pi("_e",Icit.Expl,A_term,_=>Pi("_l",Icit.Expl,L_term,_=>L_term)), c_term =>
                            Lam("n_expl", Icit.Expl, L_term, n_term =>
                                App(App(c_term, x_term, Icit.Expl),
                                    App(App(App(xs_term, L_term, Icit.Expl), c_term, Icit.Expl), n_term, Icit.Expl),
                                    Icit.Expl)))))));
        defineGlobal("cons_hs", cons_func_type, cons_func_val_raw);
        assert(areEqual(globalDefs.get("cons_hs").type, cons_func_type, baseCtx), "HSI Test 7.1: cons_hs type check");
        // console.log('printTerm(globalDefs.get("cons_hs")!.value)', printTerm(globalDefs.get("cons_hs")!.value));
        // console.log('printTerm(cons_func_val_elab_expected)', printTerm(cons_func_val_elab_expected));
        assert(areEqual(globalDefs.get("cons_hs")!.value, cons_func_val_elab_expected, baseCtx), "HSI Test 7.2: cons_hs value check");
    
        // let map : {A B} -> (A -> B) -> List A -> List B
        // = \{A}{B} f xs L c n. xs L (\a. c (f a)) n;
        const map_func_type = Pi("A_map", Icit.Impl, Type(), A_map_term =>
            Pi("B_map", Icit.Impl, Type(), B_map_term =>
                Pi("f_map", Icit.Expl, Pi("_arg", Icit.Expl, A_map_term, _ => B_map_term), _f_term => 
                    Pi("xs_map", Icit.Expl, App(Var("List_hs"), A_map_term, Icit.Expl), _xs_term =>
                        App(Var("List_hs"), B_map_term, Icit.Expl)
                    )
                )
            )
        );
        const map_func_val_raw = Lam("A_impl_map", Icit.Impl, A_val_map => 
            Lam("B_impl_map", Icit.Impl, B_val_map =>
                Lam("f_expl_map", Icit.Expl, f_val_map => 
                    Lam("xs_expl_map", Icit.Expl, xs_val_map => 
                        Lam("L_expl_map", Icit.Expl, L_val_map => 
                            Lam("c_expl_map", Icit.Expl, c_val_map => 
                                Lam("n_expl_map", Icit.Expl, n_val_map => 
                                    App(App(App(xs_val_map, L_val_map, Icit.Expl), 
                                            Lam("a_inner_map", Icit.Expl, a_inner_val_map => App(c_val_map, App(f_val_map, a_inner_val_map, Icit.Expl), Icit.Expl)), 
                                            Icit.Expl), 
                                        n_val_map, Icit.Expl)
                                )
                            )
                        )
                    )
                )
            )
        );
        const map_func_val_annotated = Lam("A_impl_map", Icit.Impl, Type(), A_val_map => 
            Lam("B_impl_map", Icit.Impl, Type(), B_val_map =>
                Lam("f_expl_map", Icit.Expl, Pi("_arg_map_f",Icit.Expl,A_val_map,_=>B_val_map), f_val_map => 
                    Lam("xs_expl_map", Icit.Expl, App(Var("List_hs"), A_val_map, Icit.Expl), xs_val_map => 
                        Lam("L_expl_map", Icit.Expl, Type(), L_val_map => 
                            Lam("c_expl_map", Icit.Expl, Pi("_b_map_c",Icit.Expl,B_val_map,_=>Pi("_l_map_c",Icit.Expl,L_val_map,_=>L_val_map)), c_val_map => 
                                Lam("n_expl_map", Icit.Expl, L_val_map, n_val_map => 
                                    App(App(App(xs_val_map, L_val_map, Icit.Expl), 
                                            Lam("a_inner_map", Icit.Expl, A_val_map, a_inner_val_map => App(c_val_map, App(f_val_map, a_inner_val_map, Icit.Expl), Icit.Expl)), 
                                            Icit.Expl), 
                                        n_val_map, Icit.Expl)
                                )
                            )
                        )
                    )
                )
            )
        );
        defineGlobal("map_hs", map_func_type, map_func_val_raw);
        elabRes = elaborate(Var("map_hs"), undefined, baseCtx);
        assert(areEqual(globalDefs.get("map_hs").type, map_func_type, baseCtx), "HSI Test 8.1: map_hs type check");
        assert(areEqual(globalDefs.get("map_hs").value, map_func_val_annotated, baseCtx), "HSI Test 8.2: map_hs value check");
    
        // let list1 : List Bool
        // = cons true (cons false (cons true nil));
        const list1_hs_type = App(Var("List_hs"), Var("Bool"), Icit.Expl);
        const list1_hs_val = App(App(Var("cons_hs"), Var("true_hs"), Icit.Expl), 
                               App(App(Var("cons_hs"), Var("false_hs"), Icit.Expl), 
                               App(Var("nil_hs"), Var("Bool"), Icit.Impl), 
                                   Icit.Expl), 
                               Icit.Expl);
        const list1_hs_val_FAIL = App(App(Var("cons_hs"), Var("true_hs"), Icit.Expl), 
                               App(App(Var("cons_hs"), Var("false_hs"), Icit.Expl), 
                               Var("nil_hs"), 
                                   Icit.Expl), 
                               Icit.Expl);
        const list1_hs_val_annotated = App(App(App(Var("cons_hs"), Var("Bool"), Icit.Impl), Var("true_hs"), Icit.Expl), 
                               App(App(App(Var("cons_hs"), Var("Bool"), Icit.Impl), Var("false_hs"), Icit.Expl), 
                                   App(Var("nil_hs"), Var("Bool"), Icit.Impl), 
                                   Icit.Expl), 
                               Icit.Expl);
        defineGlobal("list1_hs", list1_hs_type, list1_hs_val_FAIL);
        // abort();
        elabRes = elaborate(Var("list1_hs"), undefined, baseCtx);
        console.log('printTerm(elabRes.type)', printTerm(elabRes.type));
        console.log('printTerm(list1_hs_type)', printTerm(list1_hs_type));
        assert(areEqual(elabRes.type, list1_hs_type, baseCtx), "HSI Test 9.1: list1_hs type check");
        assert(areEqual(elabRes.term, list1_hs_val_annotated, baseCtx), "HSI Test 9.2: list1_hs value check");
    
        // --- Dependent Function Composition ---
    //     -- dependent function composition
    // let comp : {A}{B : A -> U}{C : {a} -> B a -> U}
    //            (f : {a}(b : B a) -> C b)
    //            (g : (a : A) -> B a)
    //            (a : A)
    //            -> C (g a)
    //     = \f g a. f (g a);
        const comp_func_type = Pi("A_comp", Icit.Impl, Type(), A_comp_term =>
            Pi("B_comp", Icit.Impl, Pi("_a_B", Icit.Expl, A_comp_term, _ => Type()), B_comp_func_term => 
                Pi("C_comp", Icit.Impl, 
                    Pi("a_C_arg", Icit.Impl, A_comp_term, a_C_val => 
                        Pi("b_C_arg", Icit.Expl, App(B_comp_func_term, a_C_val, Icit.Expl), _b_C_val => Type())
                    ), C_comp_func_term =>
                    Pi("f_comp_param", Icit.Expl, 
                        Pi("a_f_arg", Icit.Impl, A_comp_term, a_f_val => 
                            Pi("b_f_arg", Icit.Expl, App(B_comp_func_term, a_f_val, Icit.Expl), b_f_val => 
                                App(App(C_comp_func_term, a_f_val, Icit.Impl), b_f_val, Icit.Expl) 
                            )
                        ), f_param_term =>
                            Pi("g_comp_param", Icit.Expl, Pi("a_g_arg", Icit.Expl, A_comp_term, a_g_val => App(B_comp_func_term, a_g_val, Icit.Expl)), g_param_term => 
                                Pi("a_comp_param", Icit.Expl, A_comp_term, a_comp_val => 
                                    App(App(C_comp_func_term, a_comp_val, Icit.Impl), App(g_param_term, a_comp_val, Icit.Expl), Icit.Expl)
                                )
                            )
                    )
                )
            )
        );
        const comp_func_val_raw = Lam("f_val_raw", Icit.Expl, f_val => 
            Lam("g_val_raw", Icit.Expl, g_val => 
                Lam("a_val_raw", Icit.Expl, a_val => 
                    App(f_val, App(g_val, a_val, Icit.Expl), Icit.Expl)
                )
            )
        );
        // issue solved: ?h11_auto_inserted_impl_arg
        // const comp_func_val_annotated = 
        // (λ {A_comp : Type}. (λ {B_comp : (Π (_a_B : A_comp). Type)}. (λ {C_comp : (Π {a_C_arg : A_comp}. (Π (b_C_arg : (B_comp a_C_arg)). Type))}. (λ (f_val_raw : (Π {a_f_arg : A_comp}. (Π (b_f_arg : (B_comp a_f_arg)). ((C_comp {a_f_arg}) b_f_arg)))). (λ (g_val_raw : (Π (a_g_arg : A_comp). (B_comp a_g_arg))). (λ (a_val_raw : A_comp). ((f_val_raw {?h11_auto_inserted_impl_arg(:A_comp)}) (g_val_raw a_val_raw))))))))
    
        defineGlobal("comp_hs", comp_func_type, comp_func_val_raw);
        // console.log('printTerm(globalDefs.get("comp_hs")!.value)', printTerm(globalDefs.get("comp_hs")!.value));
        assert(areEqual(globalDefs.get("comp_hs").type, comp_func_type, baseCtx), "HSI Test 10.1: comp_hs type check");
    
    
        // let compExample = comp (cons true) (cons false) nil;
        // NOTE: no higher-order meta supported yet; therefore must provide B and C
        const B_for_compEx = Lam("_a_B_ex", Icit.Expl, _ => App(Var("List_hs"), Var("Bool"), Icit.Expl));
        const C_for_compEx = Lam("a_C_ex", Icit.Impl, a_C_val => 
                                Lam("b_C_ex", Icit.Expl, _ => App(Var("List_hs"), Var("Bool"), Icit.Expl)));
    
        const f_for_compEx = App(Var("cons_hs"), Var("true_hs"), Icit.Expl);
        const g_for_compEx = App(Var("cons_hs"), Var("false_hs"), Icit.Expl);
        const a_for_compEx = Var("nil_hs");
    
        const compEx_val = App(App(App(App(App(App(Var("comp_hs"), 
            FH(), Icit.Impl),      
            B_for_compEx, Icit.Impl),   
            C_for_compEx, Icit.Impl),   
            f_for_compEx, Icit.Expl),   
            g_for_compEx, Icit.Expl),   
            a_for_compEx, Icit.Expl);
        
        const compEx_expected_type = App(Var("List_hs"), Var("Bool"), Icit.Expl); 
        defineGlobal("compExample_hs", compEx_expected_type, compEx_val);
        console.log('printTerm(normalize(globalDefs.get("compExample_hs")!.value, baseCtx))', 
            printTerm(normalize(globalDefs.get("compExample_hs")!.value, baseCtx)), "HSI Test 11.0: compExample_hs value normalized");
    
        elabRes = elaborate(Var("compExample_hs"), undefined, baseCtx);
        assert(areEqual(globalDefs.get("compExample_hs").type, compEx_expected_type, baseCtx), "HSI Test 11.1: compExample_hs type check");
        assert(areEqual(elabRes.term, check(baseCtx, compEx_val, compEx_expected_type), baseCtx), "HSI Test 11.2: compExample_hs value check");
    
        const Nat_hs_type_val = Pi("N_Nat_param", Icit.Expl, Type(), N_Nat_term =>
            Pi("s_Nat_param", Icit.Expl, Pi("arg_s_Nat", Icit.Expl, N_Nat_term, _ => N_Nat_term), _s_term =>
                Pi("z_Nat_param", Icit.Expl, N_Nat_term, _z_term => N_Nat_term)
            )
        );
        defineGlobal("Nat_hs", Type(), Nat_hs_type_val);
        elabRes = elaborate(Var("Nat_hs"), undefined, baseCtx);
        assert(areEqual(elabRes.type, Type(), baseCtx), "HSI Test 12.1: Nat_hs type check");
    
        const ten_hs_val_raw = Lam("N_ten", Icit.Expl, Type(), N_ten_term =>
            Lam("s_ten", Icit.Expl, Pi("_arg_s", Icit.Expl, N_ten_term, _ => N_ten_term), s_ten_actual_term =>
                Lam("z_ten", Icit.Expl, N_ten_term, z_ten_actual_term =>
                    App(s_ten_actual_term, 
                        App(s_ten_actual_term, 
                            App(s_ten_actual_term, 
                                App(s_ten_actual_term, 
                                    App(s_ten_actual_term, 
                                        App(s_ten_actual_term, 
                                            App(s_ten_actual_term, 
                                                App(s_ten_actual_term, 
                                                    App(s_ten_actual_term, 
                                                        App(s_ten_actual_term, z_ten_actual_term, Icit.Expl)
                                                    , Icit.Expl)
                                                , Icit.Expl)
                                            , Icit.Expl)
                                        , Icit.Expl)
                                    , Icit.Expl)
                                , Icit.Expl)
                            , Icit.Expl)
                        , Icit.Expl)
                    , Icit.Expl)
                )
            )
        );
        defineGlobal("ten_hs", Var("Nat_hs"), ten_hs_val_raw);
        elabRes = elaborate(Var("ten_hs"), undefined, baseCtx);
        assert(areEqual(elabRes.type, Var("Nat_hs"), baseCtx), "HSI Test 13.1: ten_hs type check");
        assert(areEqual(elabRes.term, check(baseCtx, ten_hs_val_raw, Var("Nat_hs")), baseCtx), "HSI Test 13.2: ten_hs value check");
    
        const mul_hs_type = Pi("a_mul", Icit.Expl, Var("Nat_hs"), _ => Pi("b_mul", Icit.Expl, Var("Nat_hs"), _ => Var("Nat_hs")));
        const mul_hs_val_raw = Lam("a_m", Icit.Expl, a_m_val =>
            Lam("b_m", Icit.Expl, b_m_val => 
                Lam("N_m", Icit.Expl, N_m_val => 
                    Lam("s_m", Icit.Expl, s_m_val => 
                        Lam("z_m", Icit.Expl, z_m_val => 
                            App(App(App(a_m_val, FH(), Icit.Expl), 
                                    App(App(b_m_val, FH(), Icit.Expl), s_m_val, Icit.Expl), 
                                    Icit.Expl), 
                                z_m_val, Icit.Expl)
                        )
                    )
                )
            )
        );
        const mul_hs_val_annotated = Lam("a_m", Icit.Expl, Var("Nat_hs"), a_m_val =>
            Lam("b_m", Icit.Expl, Var("Nat_hs"), b_m_val => 
                Lam("N_m", Icit.Expl, Type(), N_m_val => 
                    Lam("s_m", Icit.Expl, Pi("_arg",Icit.Expl,N_m_val,_=>N_m_val), s_m_val => 
                        Lam("z_m", Icit.Expl, N_m_val, z_m_val => 
                            App(App(App(a_m_val, N_m_val, Icit.Expl), 
                                    App(App(b_m_val, N_m_val, Icit.Expl), s_m_val, Icit.Expl), 
                                    Icit.Expl), 
                                z_m_val, Icit.Expl)
                        )
                    )
                )
            )
        );
        defineGlobal("mul_hs", mul_hs_type, mul_hs_val_raw);
        elabRes = elaborate(Var("mul_hs"), undefined, baseCtx);
        assert(areEqual(elabRes.type, mul_hs_type, baseCtx), "HSI Test 14.1: mul_hs type check");
        assert(areEqual(elabRes.term, check(baseCtx, mul_hs_val_raw, mul_hs_type), baseCtx), "HSI Test 14.2: mul_hs value check");
    
        const hundred_hs_val = App(App(Var("mul_hs"), Var("ten_hs"), Icit.Expl), Var("ten_hs"), Icit.Expl);
        defineGlobal("hundred_hs", Var("Nat_hs"), hundred_hs_val);
        elabRes = elaborate(Var("hundred_hs"), undefined, baseCtx);
        assert(areEqual(elabRes.type, Var("Nat_hs"), baseCtx), "HSI Test 15.1: hundred_hs type check");
        // SLOW ~ 20s, uncomment later
        assert(areEqual(elabRes.term, check(baseCtx, hundred_hs_val, Var("Nat_hs")), baseCtx), "HSI Test 15.2: hundred_hs value check");
    
        const Eq_hs_type = Pi("A_Eq", Icit.Impl, Type(), A_Eq_term => 
            Pi("x_Eq", Icit.Expl, A_Eq_term, _ => 
                Pi("y_Eq", Icit.Expl, A_Eq_term, _ => Type())
            )
        );
        const Eq_hs_val_raw = Lam("A_eq_impl", Icit.Impl, A_eq_val => 
            Lam("x_eq_expl", Icit.Expl, x_eq_actual => 
                Lam("y_eq_expl", Icit.Expl, y_eq_actual => 
                    Pi("P_eq_expl", Icit.Expl, Pi("_ignored_P_arg", Icit.Expl, A_eq_val, _ => Type()), P_eq_val => 
                        Pi("Px_eq_expl", Icit.Expl, App(P_eq_val, x_eq_actual, Icit.Expl), _ => 
                            App(P_eq_val, y_eq_actual, Icit.Expl)
                        )
                    )
                )
            )
        );
        const A_FH = FH();
        const Eq_hs_type_impl = 
            Pi("x_Eq", Icit.Expl, A_FH, _ => 
                Pi("y_Eq", Icit.Expl, A_FH, _ => Type())
            );
        defineGlobal("Eq_hs", Eq_hs_type, Eq_hs_val_raw);
        elabRes = elaborate(Var("Eq_hs"), Eq_hs_type, baseCtx);
        // console.log(printTerm(elabRes.type));
        // console.log(printTerm(Eq_hs_type_impl));
        assert(areEqual(elabRes.type, Eq_hs_type, baseCtx), "HSI Test 16.1: Eq_hs type check");
        assert(areEqual(elabRes.term, check(baseCtx, Eq_hs_val_raw, Eq_hs_type), baseCtx) , "HSI Test 16.2: Eq_hs value check");
        // assert(unify(elabRes.type, Eq_hs_type_impl, baseCtx) == UnifyResult.Solved, "HSI Test 16.1: Eq_hs type check");
        // assert(areEqual(elabRes.term, check(baseCtx, Eq_hs_val_raw, Eq_hs_type_impl), baseCtx) , "HSI Test 16.2: Eq_hs value check");
    
        const refl_hs_type = Pi("A_refl", Icit.Impl, Type(), A_refl_term => 
            Pi("x_refl", Icit.Impl, A_refl_term, x_refl_term => 
                // This version, instead of the manually-already-elaborated version below,
                // creates the requirement to elaborate types before storing them with global symbols
                // And this creates slow-performance problems
                App(App(Var("Eq_hs"), x_refl_term, Icit.Expl), x_refl_term, Icit.Expl)
                // manually-already-elaborated version:
                // App(App(App(Var("Eq_hs"), A_refl_term, Icit.Impl), x_refl_term, Icit.Expl), x_refl_term, Icit.Expl)
            )
        );
        const refl_hs_val_raw = 
                Lam("P_refl_expl", Icit.Expl,  P_val =>
                    Lam("Px_refl_expl", Icit.Expl, Px_refl_actual => 
                        Px_refl_actual
                    )
                );
        const refl_hs_val_annotated = Lam("A_refl_impl", Icit.Impl, Type(), A_refl_val => 
            Lam("x_refl_impl", Icit.Impl, A_refl_val, x_refl_actual_val => 
                Lam("P_refl_expl", Icit.Expl, Pi("_ignored_P_arg", Icit.Expl, A_refl_val, _ => Type()), P_val =>
                    Lam("Px_refl_expl", Icit.Expl, App(P_val, x_refl_actual_val, Icit.Expl) , Px_refl_actual => 
                        Px_refl_actual
                    )
                )
            )
        );
        defineGlobal("refl_hs", refl_hs_type, refl_hs_val_raw, false, false, true);
        elabRes = elaborate(Var("refl_hs"), refl_hs_type, baseCtx); // fails alone without expected type
        // assert(areEqual(elabRes.type, refl_hs_type, baseCtx), "HSI Test 17.1: refl_hs type check");
        // console.log(elabRes.term);
    
        console.log(printTerm(elabRes.term));
        // console.log(printTerm(check(baseCtx, refl_hs_val_annotated, refl_hs_type))); //fails to print term
        // assert(areEqual(elabRes.term, check(baseCtx, refl_hs_val_annotated, refl_hs_type), baseCtx), "HSI Test 17.2: refl_hs value check");
    
        const sym_hs_type = Pi("A_sym", Icit.Impl, Type(), A_sym_term =>
            Pi("x_sym", Icit.Impl, A_sym_term, x_sym_term => 
                Pi("y_sym", Icit.Impl, A_sym_term, y_sym_term => 
                    Pi("p_sym", Icit.Expl, App(App(App(Var("Eq_hs"), A_sym_term, Icit.Impl), x_sym_term, Icit.Expl), y_sym_term, Icit.Expl), _p_term =>
                        App(App(App(Var("Eq_hs"), A_sym_term, Icit.Impl), y_sym_term, Icit.Expl), x_sym_term, Icit.Expl)
                    )
                )
            )
        );
        const sym_hs_val_raw = Lam("A_s_impl", Icit.Impl, A_s_val => 
            Lam("x_s_impl", Icit.Impl, x_s_val => 
                Lam("y_s_impl", Icit.Impl, y_s_val => 
                    Lam("p_s_expl", Icit.Expl, App(App(App(Var("Eq_hs"),A_s_val,Icit.Impl),x_s_val,Icit.Expl),y_s_val,Icit.Expl), p_s_val => 
                        App( App(p_s_val, 
                                Lam("y_inner_s", Icit.Expl, y_inner_s_val => 
                                    App(App(Var("Eq_hs"), y_inner_s_val, Icit.Expl), x_s_val, Icit.Expl)
                                ), Icit.Expl), 
                             Var("refl_hs"), Icit.Expl
                            )
                    )
                )
            )
        );
        // const sym_hs_val_raw = Lam("A_s_impl", Icit.Impl, Type(), A_s_val => 
        //     Lam("x_s_impl", Icit.Impl, A_s_val, x_s_val => 
        //         Lam("y_s_impl", Icit.Impl, A_s_val, y_s_val => 
        //             Lam("p_s_expl", Icit.Expl, App(App(App(Var("Eq_hs"),A_s_val,Icit.Impl),x_s_val,Icit.Expl),y_s_val,Icit.Expl), p_s_val => 
        //                 App( App(p_s_val, 
        //                         Lam("y_inner_s", Icit.Expl, A_s_val, y_inner_s_val => 
        //                             App(App(App(Var("Eq_hs"), A_s_val, Icit.Impl), y_inner_s_val, Icit.Expl), x_s_val, Icit.Expl)
        //                         ), Icit.Expl), 
        //                      App(App(Var("refl_hs"), A_s_val, Icit.Impl), x_s_val, Icit.Impl), Icit.Expl
        //                     )
        //             )
        //         )
        //     )
        // );
        defineGlobal("sym_hs", sym_hs_type, sym_hs_val_raw);
        elabRes = elaborate(Var("sym_hs"), sym_hs_type, baseCtx);
        // console.log(printTerm(globalDefs.get("sym_hs").value));
    
        // assert(areEqual(elabRes.type, sym_hs_type, baseCtx), "HSI Test 18.1: sym_hs type check");
        // assert(areEqual(normalize(elabRes.term, baseCtx), normalize(check(baseCtx, sym_hs_val_raw, sym_hs_type), baseCtx), baseCtx), "HSI Test 18.2: sym_hs value check");
    
        // (A:_) means A is a type, so Pi("A", Icit.Expl, Type(), ...)
        const the_type = Pi("A", Icit.Expl, Type(), A => Pi("x", Icit.Expl, A, _ => A));
        // Raw value uses FH() for the type of 'A' in Lam binding, to be inferred/checked.
        // However, paramType for Lam is required for _isAnnotated: true.
        // Let's be explicit based on the Pi type.
        const the_raw_val = Lam("A_", Icit.Expl, Type(), A_ => Lam("x", Icit.Expl, A_, x => x));
    
        // defineGlobal requires the value to be elaborated if not a base constant.
        defineGlobal("the", the_type, the_raw_val);
        const elabThe = elaborate(Var("the"), the_type);
    
        const mul_ten_ten_val = App(App(Var("mul_hs"), Var("ten_hs"), Icit.Expl), Var("ten_hs"), Icit.Expl);
        const final_expr_type_expected = App(App(App(Var("Eq_hs"), Var("Nat_hs"), Icit.Impl), mul_ten_ten_val, Icit.Expl), Var("hundred_hs"), Icit.Expl);
        // const final_expr_val_expected = App(App(Var("refl_hs"), Var("Nat_hs"), Icit.Impl), Var("hundred_hs"), Icit.Impl);
    
        // assert(areEqual(normalize(mul_ten_ten_val, baseCtx), normalize(Var("hundred_hs"), baseCtx), baseCtx), "HSI Test 19.0: (mul ten ten) == hundred check");
    
        const the_final_expr_term_to_check = App(App(Var("the"), final_expr_type_expected, Icit.Expl), Var("refl_hs"), Icit.Expl);
        const the_final_expr_term_to_check_ = App(Var("the"), final_expr_type_expected, Icit.Expl);
        // SLOW ~ 200s, uncomment later
        // defineGlobal("the_refl", final_expr_type_expected, the_final_expr_term_to_check);
        // elabRes = elaborate(the_final_expr_term_to_check, undefined, baseCtx);
    
        // assert(areEqual(elabRes.type, final_expr_type_expected, baseCtx), "HSI Test 19.1: final 'the' expression type check");
        // assert(areEqual(normalize(elabRes.term, baseCtx), normalize(final_expr_val_expected, baseCtx), baseCtx), "HSI Test 19.2: final 'the' expression value check");
    
        console.log("Church-Style Implicit Argument Tests Completed.");
    });
});