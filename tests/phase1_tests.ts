/**
 * @file tests/phase1_tests.ts
 * @description Tests for Phase 1 features: basic Cat/Obj/Hom types and mkCat_ projections.
 */
import {
    Term, Context, Icit,
    Type, Var, Lam, App, Pi, Hole,
    CatTerm, ObjTerm, HomTerm
} from '../src/types';
import {
    emptyCtx, getTermRef, globalDefs, printTerm, FH
} from '../src/state';
import {
    defineGlobal, addRewriteRule
} from '../src/globals';
import {
    resetMyLambdaPi_Emdash, setupCatTheoryPrimitives, setupPhase1GlobalsAndRules // Use the combined setup
} from '../src/stdlib';
import {
    areEqual,
} from '../src/equality';
import {
    normalize,
} from '../src/reduction';
import {
    elaborate
} from '../src/elaboration';
import { assertEqual, assert } from './utils';
import { describe, it } from 'node:test'; // Added for node:test

describe("Phase 1 Tests", () => {
    let baseCtx = emptyCtx;
    let testTerm: Term;
    let elabRes;

    // Test 1: Basic Cat/Obj/Hom Types
    it("Test 1: Basic Cat/Obj/Hom Types", () => {
        resetMyLambdaPi_Emdash(); 
        baseCtx = emptyCtx; // Ensure fresh context for each test section

        const NatObjRepr = Var("NatType"); // This is defined in stdlib but used as a placeholder here
        testTerm = CatTerm();
        elabRes = elaborate(testTerm, undefined, baseCtx);
        assert(elabRes.type.tag === 'Type', "Test 1.1: Cat term should have type Type");

        const someCatHole = Hole("?MyCat_T1"); // Ensure unique hole names
        testTerm = ObjTerm(someCatHole);
        elabRes = elaborate(testTerm, undefined, baseCtx);
        assert(elabRes.type.tag === 'Type', "Test 1.2: Obj ?MyCat_T1 should have type Type");

        const objXHole = Hole("?X_T1");
        const objYHole = Hole("?Y_T1");
        testTerm = HomTerm(someCatHole, objXHole, objYHole);
        elabRes = elaborate(testTerm, undefined, baseCtx);
        assert(elabRes.type.tag === 'Type', "Test 1.3: Hom ?MyCat_T1 ?X_T1 ?Y_T1 should have type Type");
    });


    // Test 2: MkCat_ and Projections
    it("Test 2: MkCat_ and Projections", () => {
        resetMyLambdaPi_Emdash(); 
        baseCtx = emptyCtx;
        const NatObjRepr = Var("NatType"); // As defined/used in original test

        defineGlobal("H_repr_Nat_Global", Pi("X", Icit.Expl, NatObjRepr, _X => Pi("Y", Icit.Expl, NatObjRepr, _Y => Type())), undefined, true);
        defineGlobal("C_impl_Nat_dummy_Global",
            Pi("X_arg", Icit.Impl, NatObjRepr, X_term =>
            Pi("Y_arg", Icit.Impl, NatObjRepr, Y_term =>
            Pi("Z_arg", Icit.Impl, NatObjRepr, Z_term =>
            Pi("g_morph", Icit.Expl, App(App(Var("H_repr_Nat_Global"), Y_term, Icit.Expl), Z_term, Icit.Expl), _g_term =>
            Pi("f_morph", Icit.Expl, App(App(Var("H_repr_Nat_Global"), X_term, Icit.Expl), Y_term, Icit.Expl), _f_term =>
            App(App(Var("H_repr_Nat_Global"), X_term, Icit.Expl), Z_term, Icit.Expl)
            ))))), undefined, true);
    
        // [SOLVED] elaboration has issues with this version (must use a manually elaborated C_impl_Nat_dummy_Global):
        const NatCategoryTermVal = App(App(App(Var("mkCat_"), NatObjRepr, Icit.Expl), Var("H_repr_Nat_Global"), Icit.Expl), Var("C_impl_Nat_dummy_Global"), Icit.Expl);
        // const C_impl_Nat_dummy_Global = Lam("X", Icit.Impl, NatObjRepr, X_val =>
        //         Lam("Y", Icit.Impl, NatObjRepr, Y_val =>
        //             Lam("Z", Icit.Impl, NatObjRepr, Z_val => App(App(App(Var("C_impl_Nat_dummy_Global"), X_val, Icit.Impl), Y_val, Icit.Impl), Z_val, Icit.Impl))))
        // const NatCategoryTermVal = App(App(App(Var("mkCat_"), NatObjRepr, Icit.Expl), Var("H_repr_Nat_Global"), Icit.Expl), C_impl_Nat_dummy_Global, Icit.Expl);
        elabRes = elaborate(NatCategoryTermVal, undefined, baseCtx);
        assert(elabRes.type.tag === 'CatTerm', "Test 2.1: MkCat_ term should have type Cat");
    
        const ObjOfNatCat = ObjTerm(NatCategoryTermVal);
        elabRes = elaborate(ObjOfNatCat, undefined, baseCtx);
        assert(areEqual(elabRes.term, NatObjRepr, baseCtx), `Test 2.2: Obj(NatCategoryTerm) should reduce to NatType. Got ${printTerm(elabRes.term)}`);
    
        defineGlobal("nat_val1_t2", NatObjRepr, undefined, true);
        defineGlobal("nat_val2_t2", NatObjRepr, undefined, true);
        const X_in_NatCat = Var("nat_val1_t2");
        const Y_in_NatCat = Var("nat_val2_t2");
    
        const HomInNatCat = HomTerm(NatCategoryTermVal, X_in_NatCat, Y_in_NatCat);
        elabRes = elaborate(HomInNatCat, undefined, baseCtx);
        const expectedHomReduced = App(App(Var("H_repr_Nat_Global"), X_in_NatCat, Icit.Expl), Y_in_NatCat, Icit.Expl);
        assert(areEqual(elabRes.term, normalize(expectedHomReduced, baseCtx), baseCtx), `Test 2.3: Hom(NatCat,X,Y) should reduce to H_repr(X,Y). Expected ${printTerm(normalize(expectedHomReduced,baseCtx))} Got ${printTerm(elabRes.term)}`);
        console.log("Test 2 Passed.");
    
        console.log("\n--- Test 3: IdentityMorph ---");
        // resetMyLambdaPi(); setupPhase1GlobalsAndRules();
        const MyNatCat3_val = App(App(App(Var("mkCat_"), NatObjRepr, Icit.Expl), Var("H_repr_Nat_Global"), Icit.Expl), Var("C_impl_Nat_dummy_Global"), Icit.Expl);
        // const MyNatCat3_val = App(App(App(Var("mkCat_"), NatObjRepr, Icit.Expl), Var("H_repr_Nat_Global"), Icit.Expl), C_impl_Nat_dummy_Global, Icit.Expl);
        defineGlobal("MyNatCat3_GlobalDef", CatTerm(), MyNatCat3_val);
    
        defineGlobal("x_obj_val_t3", ObjTerm(Var("MyNatCat3_GlobalDef")), undefined, true);
        const anObjX_term = Var("x_obj_val_t3");
        // const id_x = IdentityMorph(anObjX_term, Var("MyNatCat3_GlobalDef"));
        const id_x = App(App(Var("identity_morph"), Var("MyNatCat3_GlobalDef"), Icit.Impl), anObjX_term, Icit.Expl);
        const expected_id_x_type_structure = HomTerm(Var("MyNatCat3_GlobalDef"), anObjX_term, anObjX_term);
        defineGlobal("id_x", expected_id_x_type_structure, id_x);
        elabRes = elaborate(id_x, expected_id_x_type_structure, baseCtx);
    
        // // After refactor, id_x elaborates to an App(...) term.
        // // We mainly care that its type is correct and it normalizes as expected by rewrite rules.
        // assert(elabRes.term.tag === 'App', "Test 3.0: Elaborated id_x should be an App term");
        // // Check if the head of the application is indeed 'identity_morph'
        // let currentApp = getTermRef(elabRes.term);
        // while(currentApp.tag === 'App') currentApp = getTermRef(currentApp.func);
        // assert(currentApp.tag === 'Var' && currentApp.name === 'identity_morph', "Test 3.1: Head of id_x app should be identity_morph");
    
        const expected_normalized_type_t3 = App(App(Var("H_repr_Nat_Global"), anObjX_term, Icit.Expl), anObjX_term, Icit.Expl);
        assert(areEqual(elabRes.type, expected_normalized_type_t3, baseCtx), `Test 3.2: id_x type should be Hom(Cat,X,X) (normalized). Expected ${printTerm(expected_normalized_type_t3)}, Got ${printTerm(elabRes.type)}`);
        console.log("Test 3 Passed.");
    });

    // Test 4: ComposeMorph Inference
    it("Test 4: ComposeMorph Inference", () => {
        resetMyLambdaPi_Emdash(); 
        baseCtx = emptyCtx;
        defineGlobal("C4_Global", CatTerm(), undefined, true);
        defineGlobal("obj_x_val_t4", ObjTerm(Var("C4_Global")), undefined, true);
        defineGlobal("obj_z_val_t4", ObjTerm(Var("C4_Global")), undefined, true);
        const x_term_t4 = Var("obj_x_val_t4");
        const z_term_t4 = Var("obj_z_val_t4");
        const y_hole_obj_t4 = Hole("?y_obj_t4");
        const f_morph_hole = Hole("?f_xy_t4");
        const g_morph_hole = Hole("?g_yz_t4");
    
        // const comp_gf = ComposeMorph(g_morph_hole, f_morph_hole, Var("C4_Global"), x_term_t4, y_hole_obj_t4, z_term_t4);
        const comp_gf = App(App(App(App(App(App(Var("compose_morph"), Var("C4_Global"), Icit.Impl), x_term_t4, Icit.Impl), y_hole_obj_t4, Icit.Impl), z_term_t4, Icit.Impl), g_morph_hole, Icit.Expl), f_morph_hole, Icit.Expl);
        const expectedCompType = HomTerm(Var("C4_Global"), x_term_t4, z_term_t4);
        defineGlobal("comp_gf", expectedCompType, comp_gf);
        elabRes = elaborate(comp_gf, expectedCompType, baseCtx);
    
        assert(areEqual(elabRes.type, expectedCompType, baseCtx), `Test 4.0: comp_gf type should be Hom(C,X,Z). Expected ${printTerm(expectedCompType)}, Got ${printTerm(elabRes.type)}`);
    
        const f_hole_ref = getTermRef(f_morph_hole) as Term & {tag:"Hole"};
        const g_hole_ref = getTermRef(g_morph_hole) as Term & {tag:"Hole"};
        assert(!!f_hole_ref.elaboratedType, "Test 4.2a: f_morph_hole (?f_xy_t4) should have an elaborated type.");
        assert(!!g_hole_ref.elaboratedType, "Test 4.2b: g_morph_hole (?g_yz_t4) should have an elaborated type.");
        const expected_f_type = HomTerm(Var("C4_Global"), x_term_t4, y_hole_obj_t4);
        const expected_g_type = HomTerm(Var("C4_Global"), y_hole_obj_t4, z_term_t4);
        assert(areEqual(getTermRef(f_hole_ref.elaboratedType!), expected_f_type, baseCtx), `Test 4.3a: f_morph_hole type should be Hom(C,X,Y_hole). Expected ${printTerm(expected_f_type)}, Got ${printTerm(getTermRef(f_hole_ref.elaboratedType!))}`);
        assert(areEqual(getTermRef(g_hole_ref.elaboratedType!), expected_g_type, baseCtx), `Test 4.3b: g_morph_hole type should be Hom(C,Y_hole,Z). Expected ${printTerm(expected_g_type)}, Got ${printTerm(getTermRef(g_hole_ref.elaboratedType!))}`);
        console.log("Test 4 Passed.");
    });

    // Test 5: Rewrite rule comp (g o id)
    it("Test 5: Rewrite rule comp (g o id)", () => {
        resetMyLambdaPi_Emdash(); 
        baseCtx = emptyCtx;
        defineGlobal("C5_cat_global", CatTerm(), undefined, true); 
        defineGlobal("x5_obj_t5", ObjTerm(Var("C5_cat_global")), undefined, true);
        defineGlobal("y5_obj_t5", ObjTerm(Var("C5_cat_global")), undefined, true);
        const X5_term = Var("x5_obj_t5");
        const Y5_term = Var("y5_obj_t5");
    
        defineGlobal("g_XY_concrete_t5", HomTerm(Var("C5_cat_global"), X5_term, Y5_term), undefined, true);
        const g_XY_for_rule = Var("g_XY_concrete_t5");
        // const id_X5_for_rule = IdentityMorph(X5_term, Var("C5_cat_global"));
        const id_X5_for_rule = App(App(Var("identity_morph"), Var("C5_cat_global"), Icit.Impl), X5_term, Icit.Expl);
        // const test_term_g_o_id = ComposeMorph(g_XY_for_rule, id_X5_for_rule, Var("C5_cat_global"), X5_term, X5_term, Y5_term);
        const test_term_g_o_id = App(App(App(App(App(App(Var("compose_morph"), Var("C5_cat_global"), Icit.Impl), X5_term, Icit.Impl), X5_term, Icit.Impl), Y5_term, Icit.Impl), g_XY_for_rule, Icit.Expl), id_X5_for_rule, Icit.Expl);
        elabRes = elaborate(test_term_g_o_id, undefined, baseCtx);
        assert(areEqual(elabRes.term, g_XY_for_rule, baseCtx), `Test 5.1: (g o id_X) should reduce to g. Got ${printTerm(elabRes.term)} Expected ${printTerm(g_XY_for_rule)}`);
        console.log("Test 5 Passed.");
    });
});