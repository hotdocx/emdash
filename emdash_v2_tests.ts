import {
    Term, Context, ElaborationResult, Icit,
    Type, Var, Lam, App, Pi, Hole,
    CatTerm, ObjTerm, HomTerm, MkCat_, IdentityMorph, ComposeMorph,
    PatternVarDecl, UnifyResult, StoredRewriteRule // Added StoredRewriteRule, UnifyResult from core_types
} from './src/core_types';
import {
    defineGlobal, addRewriteRule, resetMyLambdaPi, setupPhase1GlobalsAndRules,
    emptyCtx, getTermRef, addConstraint, userRewriteRules, // Removed StoredRewriteRule from here
    cloneTerm, setDebugVerbose, getDebugVerbose // Use getter/setter for DEBUG_VERBOSE
} from './src/core_context_globals';
import {
    areEqual, normalize, whnf, unify // Removed UnifyResult from here
} from './src/core_logic';
import {
    elaborate, printTerm, infer, check, isPatternVarName, matchPattern, ElaborationOptions
} from './src/core_elaboration';

// Helper function to assert equality for test cases
function assertEqual(actual: string, expected: string, message: string) {
    if (actual !== expected) {
        console.error(`Assertion Failed: ${message}`);
        console.error(`Expected: ${expected}`);
        console.error(`Actual:   ${actual}`);
        throw new Error(`Assertion Failed: ${message}`);
    }
    console.log(`Assertion Passed: ${message}`);
}
function assert(condition: boolean, message: string) {
    if (!condition) {
            console.error(`Assertion Failed: ${message}`);
            throw new Error(`Assertion Failed: ${message}`);
    }
    console.log(`Assertion Passed: ${message}`);
}


function runPhase1Tests() {
    const baseCtx = emptyCtx;
    const NatObjRepr = Var("NatType"); 
    console.log("\n--- Test 1: Basic Cat/Obj/Hom Types ---");
    resetMyLambdaPi(); setupPhase1GlobalsAndRules();
    let testTerm : Term;
    testTerm = CatTerm();
    let elabRes = elaborate(testTerm, undefined, baseCtx);
    assert(elabRes.type.tag === 'Type', "Test 1.1: Cat term should have type Type");

    const someCatHole = Hole("?MyCat");
    testTerm = ObjTerm(someCatHole);
    elabRes = elaborate(testTerm, undefined, baseCtx);
    assert(elabRes.type.tag === 'Type', "Test 1.2: Obj ?MyCat should have type Type");

    const objXHole = Hole("?X");
    const objYHole = Hole("?Y");
    testTerm = HomTerm(someCatHole, objXHole, objYHole);
    elabRes = elaborate(testTerm, undefined, baseCtx);
    assert(elabRes.type.tag === 'Type', "Test 1.3: Hom ?MyCat ?X ?Y should have type Type");
    console.log("Test 1 Passed.");


    console.log("\n--- Test 2: MkCat_ and Projections ---");
    resetMyLambdaPi(); setupPhase1GlobalsAndRules();
    defineGlobal("H_repr_Nat_Global", Pi("X", Icit.Expl, NatObjRepr, _X => Pi("Y", Icit.Expl, NatObjRepr, _Y => Type())), undefined, true);
    defineGlobal("C_impl_Nat_dummy_Global",
        Pi("X_arg", Icit.Expl, NatObjRepr, X_term =>
        Pi("Y_arg", Icit.Expl, NatObjRepr, Y_term =>
        Pi("Z_arg", Icit.Expl, NatObjRepr, Z_term =>
        Pi("g_morph", Icit.Expl, App(App(Var("H_repr_Nat_Global"), Y_term, Icit.Expl), Z_term, Icit.Expl), _g_term =>
        Pi("f_morph", Icit.Expl, App(App(Var("H_repr_Nat_Global"), X_term, Icit.Expl), Y_term, Icit.Expl), _f_term =>
        App(App(Var("H_repr_Nat_Global"), X_term, Icit.Expl), Z_term, Icit.Expl)
        ))))), undefined, true);
    
    const NatCategoryTermVal = MkCat_(NatObjRepr, Var("H_repr_Nat_Global"), Var("C_impl_Nat_dummy_Global"));
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
    resetMyLambdaPi(); setupPhase1GlobalsAndRules();
    const MyNatCat3_val = MkCat_(NatObjRepr, Var("H_repr_Nat_Global"), Var("C_impl_Nat_dummy_Global"));
    defineGlobal("MyNatCat3_GlobalDef", CatTerm(), MyNatCat3_val, false);

    defineGlobal("x_obj_val_t3", ObjTerm(Var("MyNatCat3_GlobalDef")), undefined, true);
    const anObjX_term = Var("x_obj_val_t3");
    const id_x = IdentityMorph(anObjX_term); 
    const expected_id_x_type_structure = HomTerm(Var("MyNatCat3_GlobalDef"), anObjX_term, anObjX_term);
    elabRes = elaborate(id_x, expected_id_x_type_structure, baseCtx);

    const idTermSolved = getTermRef(elabRes.term) as Term & {tag: 'IdentityMorph'};
    assert(idTermSolved.tag === 'IdentityMorph', `Test 3.0: Elaborated id_x should be IdentityMorph, but got ${idTermSolved.tag}`);
    assert(!!idTermSolved.cat_IMPLICIT, "Test 3.1a: id_x.cat_IMPLICIT should be filled");
    assert(areEqual(getTermRef(idTermSolved.cat_IMPLICIT!), Var("MyNatCat3_GlobalDef"), baseCtx), `Test 3.1b: id_x.cat_IMPLICIT should resolve to MyNatCat3_GlobalDef. Expected ${printTerm(Var("MyNatCat3_GlobalDef"))}, Got: ${printTerm(getTermRef(idTermSolved.cat_IMPLICIT!))}`);
    
    const expected_normalized_type_t3 = normalize(App(App(Var("H_repr_Nat_Global"), anObjX_term, Icit.Expl), anObjX_term, Icit.Expl), baseCtx);
    assert(areEqual(elabRes.type, expected_normalized_type_t3, baseCtx), `Test 3.2: id_x type should be Hom(Cat,X,X) (normalized). Expected ${printTerm(expected_normalized_type_t3)}, Got ${printTerm(elabRes.type)}`);
    console.log("Test 3 Passed.");

    console.log("\n--- Test 4: ComposeMorph Inference ---");
    resetMyLambdaPi(); setupPhase1GlobalsAndRules();
    defineGlobal("C4_Global", CatTerm(), undefined, true);
    defineGlobal("obj_x_val_t4", ObjTerm(Var("C4_Global")), undefined, true);
    defineGlobal("obj_z_val_t4", ObjTerm(Var("C4_Global")), undefined, true);
    const x_term_t4 = Var("obj_x_val_t4");
    const z_term_t4 = Var("obj_z_val_t4");
    const y_hole_obj_t4 = Hole("?y_obj_t4");
    const f_morph_hole = Hole("?f_xy_t4");
    const g_morph_hole = Hole("?g_yz_t4");

    const comp_gf = ComposeMorph(g_morph_hole, f_morph_hole, Var("C4_Global"), x_term_t4, y_hole_obj_t4, z_term_t4);
    const expectedCompType = HomTerm(Var("C4_Global"), x_term_t4, z_term_t4);
    elabRes = elaborate(comp_gf, expectedCompType, baseCtx);

    assert(areEqual(elabRes.type, expectedCompType, baseCtx), `Test 4.0: comp_gf type should be Hom(C,X,Z). Expected ${printTerm(expectedCompType)}, Got ${printTerm(elabRes.type)}`);
    const compTermSolved = elabRes.term as Term & {tag:"ComposeMorph"};
    assert(compTermSolved.tag === 'ComposeMorph', `Test 4.0b: comp_gf should remain a ComposeMorph term. Got ${compTermSolved.tag}`);
    assert(!!compTermSolved.cat_IMPLICIT && !!compTermSolved.objX_IMPLICIT && !!compTermSolved.objY_IMPLICIT && !!compTermSolved.objZ_IMPLICIT, "Test 4.1: ComposeMorph implicits (cat, X, Y, Z) should be resolved/present.");
    
    const f_hole_ref = getTermRef(f_morph_hole) as Term & {tag:"Hole"};
    const g_hole_ref = getTermRef(g_morph_hole) as Term & {tag:"Hole"};
    assert(!!f_hole_ref.elaboratedType, "Test 4.2a: f_morph_hole (?f_xy_t4) should have an elaborated type.");
    assert(!!g_hole_ref.elaboratedType, "Test 4.2b: g_morph_hole (?g_yz_t4) should have an elaborated type.");
    const expected_f_type = HomTerm(Var("C4_Global"), x_term_t4, y_hole_obj_t4);
    const expected_g_type = HomTerm(Var("C4_Global"), y_hole_obj_t4, z_term_t4);
    assert(areEqual(getTermRef(f_hole_ref.elaboratedType!), expected_f_type, baseCtx), `Test 4.3a: f_morph_hole type should be Hom(C,X,Y_hole). Expected ${printTerm(expected_f_type)}, Got ${printTerm(getTermRef(f_hole_ref.elaboratedType!))}`);
    assert(areEqual(getTermRef(g_hole_ref.elaboratedType!), expected_g_type, baseCtx), `Test 4.3b: g_morph_hole type should be Hom(C,Y_hole,Z). Expected ${printTerm(expected_g_type)}, Got ${printTerm(getTermRef(g_hole_ref.elaboratedType!))}`);
    console.log("Test 4 Passed.");


    console.log("\n--- Test 5: Rewrite rule comp (g o id) ---");
    resetMyLambdaPi(); setupPhase1GlobalsAndRules(); 
    defineGlobal("C5_cat_global", CatTerm(), undefined, true); 
    defineGlobal("x5_obj_t5", ObjTerm(Var("C5_cat_global")), undefined, true);
    defineGlobal("y5_obj_t5", ObjTerm(Var("C5_cat_global")), undefined, true);
    const X5_term = Var("x5_obj_t5");
    const Y5_term = Var("y5_obj_t5");

    defineGlobal("g_XY_concrete_t5", HomTerm(Var("C5_cat_global"), X5_term, Y5_term), undefined, true);
    const g_XY_for_rule = Var("g_XY_concrete_t5");
    const id_X5_for_rule = IdentityMorph(X5_term, Var("C5_cat_global"));
    const test_term_g_o_id = ComposeMorph(g_XY_for_rule, id_X5_for_rule, Var("C5_cat_global"), X5_term, X5_term, Y5_term);
    elabRes = elaborate(test_term_g_o_id, undefined, baseCtx);
    assert(areEqual(elabRes.term, g_XY_for_rule, baseCtx), `Test 5.1: (g o id_X) should reduce to g. Got ${printTerm(elabRes.term)} Expected ${printTerm(g_XY_for_rule)}`);
    console.log("Test 5 Passed.");
}

function runImplicitArgumentTests() {
    console.log("\n--- Running Implicit Argument Tests ---");
    const ctx = emptyCtx;

    resetMyLambdaPi();
    defineGlobal("constId",
        Pi("A", Icit.Impl, Type(), A_param => Pi("x", Icit.Expl, A_param, _x_param => A_param)),
        Lam("A_lam", Icit.Impl, Type(), A_term => Lam("x_lam", Icit.Expl, A_term, x_term => x_term))
    );
    defineGlobal("Nat", Type(), undefined, true);
    defineGlobal("five", Var("Nat"), undefined, true);

    let term = App(App(Var("constId"), Var("Nat"), Icit.Impl), Var("five"), Icit.Expl); 
    let elabRes = elaborate(term, undefined, ctx);
    assertEqual(printTerm(elabRes.term), "five", "IA1.1: (constId {Nat} five) should elaborate to five");
    assertEqual(printTerm(elabRes.type), "Nat", "IA1.1: Type of (constId {Nat} five) should be Nat");

    term = App(Var("constId"), Var("five"), Icit.Expl); 
    elabRes = elaborate(term, undefined, ctx);
    assertEqual(printTerm(elabRes.term), "five", "IA1.2: (constId five) should elaborate to five (A inferred as Nat)");
    assertEqual(printTerm(elabRes.type), "Nat", "IA1.2: Type of (constId five) should be Nat");

    resetMyLambdaPi();
    defineGlobal("Nat", Type(), undefined, true);
    const idFuncType = Pi("A_pi", Icit.Impl, Type(), A_pi_param => Pi("x_pi", Icit.Expl, A_pi_param, _x_pi_param => A_pi_param));
    const polySimpleId = Lam("y_lam", Icit.Expl, Hole("?Y_param_type"), y_body_param => y_body_param); 

    elabRes = elaborate(polySimpleId, idFuncType, ctx);
    const elabTerm = elabRes.term; console.log({elabTerm});
    assert(elabTerm.tag === 'Lam' && elabTerm.icit === Icit.Impl, "IA2.1: Elaborated polyId against Pi type should have an outer implicit lambda");
    
    if (elabTerm.tag === 'Lam') { // Ensure elabTerm is narrowed for TS
        assert(elabTerm.paramType?.tag === 'Type', "IA2.1: Outer implicit lambda's parameter type should be Type");
        
        const outerLamParamName = elabTerm.paramName;
        const innerLamTerm = elabTerm.body(Var(outerLamParamName)); 
        const finalInnerLam = getTermRef(innerLamTerm) as Term & {tag:'Lam'};

        assert(finalInnerLam.tag === 'Lam' && finalInnerLam.icit === Icit.Expl, "IA2.1: Inner lambda should be explicit");
        assert(finalInnerLam._isAnnotated, "IA2.1: Inner lambda should be annotated");
        assert(!!finalInnerLam.paramType, "IA2.1: Inner lambda paramType should be defined");
        
        const finalYParamType = finalInnerLam.paramType!; 
        assert(finalYParamType.tag === 'Var' && finalYParamType.name === outerLamParamName, `IA2.1: Inner lambda's param type should be the var bound by outer implicit lambda. Expected Var(${outerLamParamName}), Got ${printTerm(finalYParamType)}`);
        } else {
        assert(false, "IA2.1: elabTerm was not a Lam as expected.");
    }


    resetMyLambdaPi();
    defineGlobal("Eq", Pi("T", Icit.Impl, Type(), T_param => Pi("x", Icit.Expl, T_param, _ => Pi("y", Icit.Expl, T_param, _ => Type()))));
    defineGlobal("refl", Pi("T", Icit.Impl, Type(), T_param => Pi("x", Icit.Expl, T_param, x_param => App(App(App(Var("Eq"),T_param,Icit.Impl),x_param,Icit.Expl),x_param,Icit.Expl) )));
    defineGlobal("f_inj", Pi("T", Icit.Impl, Type(), T_param => Pi("x", Icit.Expl, T_param, _ => T_param)), undefined, false, true); 
    defineGlobal("g_noninj", Pi("T", Icit.Impl, Type(), T_param => Pi("x", Icit.Expl, T_param, _ => T_param)), undefined, false, false); 

    defineGlobal("Nat", Type(), undefined, true);
    defineGlobal("a_val", Var("Nat"), undefined, true);
    defineGlobal("b_val", Var("Nat"), undefined, true);

    const hole1 = Hole("?h1_ia3");
    const term_f_a = App(App(Var("f_inj"), Var("Nat"), Icit.Impl), Var("a_val"), Icit.Expl);
    const term_f_h1 = App(App(Var("f_inj"), Var("Nat"), Icit.Impl), hole1, Icit.Expl);
    addConstraint(term_f_a, term_f_h1, "IA3.1 Constraint: f_inj a = f_inj ?h1 (injective)");
    elaborate(hole1, Var("Nat"), ctx); 
    assert(areEqual(getTermRef(hole1), Var("a_val"), ctx), "IA3.1: For injective f_inj, (f_inj a = f_inj ?h1) should solve ?h1 to a_val");

    resetMyLambdaPi();
    defineGlobal("Eq", Pi("T", Icit.Impl, Type(), T => Pi("x", Icit.Expl, T, _ => Pi("y", Icit.Expl, T, _ => Type()))));
    defineGlobal("refl", Pi("T", Icit.Impl, Type(), T => Pi("x", Icit.Expl, T, x => App(App(App(Var("Eq"),T,Icit.Impl),x,Icit.Expl),x,Icit.Expl) )));
    defineGlobal("f_inj", Pi("T", Icit.Impl, Type(), T => Pi("x", Icit.Expl, T, _ => T)), undefined, false, true); 
    defineGlobal("g_noninj", Pi("T", Icit.Impl, Type(), T => Pi("x", Icit.Expl, T, _ => T)), undefined, false, false);
    defineGlobal("Nat", Type(), undefined, true);
    defineGlobal("a_val", Var("Nat"), undefined, true);

    const hole3 = Hole("?h3_ia3");
    const term_g_a = App(App(Var("g_noninj"), Var("Nat"), Icit.Impl), Var("a_val"), Icit.Expl);
    const term_g_h3 = App(App(Var("g_noninj"), Var("Nat"), Icit.Impl), hole3, Icit.Expl); 
    addConstraint(term_g_a, term_g_h3, "IA3.2 Constraint: g_noninj a = g_noninj ?h3 (non-injective)");
    elaborate(hole3, Var("Nat"), ctx); 
    assert(getTermRef(hole3).tag === 'Hole', "IA3.2: For non-injective g_noninj, (g_noninj a = g_noninj ?h3) should leave ?h3 as a hole");

    console.log("Implicit Argument Tests Completed.");
}

function runElaborateNonNormalizedTest() {
    console.log("\n--- Test: Elaborate with normalizeResultTerm:false ---");
    resetMyLambdaPi();
    const ctx = emptyCtx;
    const termRaw = App(Lam("x", Icit.Expl, Type(), (x_var: Term): Term => x_var), Type(), Icit.Expl);
    const elabOpts: ElaborationOptions = { normalizeResultTerm: false };
    const elabRes = elaborate(termRaw, undefined, ctx, elabOpts);

    assert(elabRes.term.tag === 'App', "ElabNoNorm.1: Result term should be App (not normalized)");
    if (elabRes.term.tag === 'App') {
        assert(elabRes.term.func.tag === 'Lam', "ElabNoNorm.1: Function part of App should be Lam");
        assert(elabRes.term.arg.tag === 'Type', "ElabNoNorm.1: Argument part of App should be Type");
    }
    assertEqual(printTerm(elabRes.type), "Type", "ElabNoNorm.1: Type (which is always normalized) should be Type");
    console.log("Test Elaborate with normalizeResultTerm:false Passed.");
}


if (require.main === module) {
    let originalDebugVerbose = getDebugVerbose();
    setDebugVerbose(false); 
    
    try {
        runPhase1Tests();
        // runNonLinearPatternTests(); 
        runImplicitArgumentTests();
        runElaborateNonNormalizedTest();

    } catch (e) {
        console.error("A test suite threw an uncaught error:", e);
    } finally {
        setDebugVerbose(originalDebugVerbose); 
    }
}

export { runPhase1Tests, runImplicitArgumentTests, runElaborateNonNormalizedTest, assertEqual, assert };