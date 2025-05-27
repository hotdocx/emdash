import {
    Term, Context, ElaborationResult, Icit,
    Type, Var, Lam, App, Pi, Hole,
    CatTerm, ObjTerm, HomTerm, MkCat_, IdentityMorph, ComposeMorph,
    PatternVarDecl, UnifyResult, StoredRewriteRule // Added StoredRewriteRule, UnifyResult from core_types
} from './src/core_types';
import {
    defineGlobal, addRewriteRule, resetMyLambdaPi, setupPhase1GlobalsAndRules,
    emptyCtx, getTermRef, addConstraint, userRewriteRules, // Removed StoredRewriteRule from here
    cloneTerm, setDebugVerbose, getDebugVerbose, FH, // Imported FH, removed freshHoleName
    globalDefs
} from './src/core_context_globals';
import {
    areEqual, normalize, whnf, unify, solveConstraints // Removed UnifyResult from here
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
    // resetMyLambdaPi(); setupPhase1GlobalsAndRules();
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
    // resetMyLambdaPi(); setupPhase1GlobalsAndRules();
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
    setDebugVerbose(false);
    defineGlobal("constId",
        Pi("A", Icit.Impl, Type(), A_param => Pi("x", Icit.Expl, A_param, _x_param => A_param)),
        Lam("A_lam", Icit.Impl, Type(), A_term => Lam("x_lam", Icit.Expl, A_term, x_term => x_term))
    );
    defineGlobal("Nat", Type(), undefined, true);
    defineGlobal("five", Var("Nat"), undefined, true);

    let term = App(App(Var("constId"), Var("Nat"), Icit.Impl), Var("five"), Icit.Expl); 
    let elabRes = elaborate(term, undefined, ctx)// , { normalizeResultTerm : false });
    assertEqual(printTerm(elabRes.term), "five", "IA1.1: (constId {Nat} five) should elaborate to five, Got " + printTerm(elabRes.term));
    assertEqual(printTerm(elabRes.type), "Nat", "IA1.1: Type of (constId {Nat} five) should be Nat");

    term = App(Var("constId"), Var("five"), Icit.Expl); 
    elabRes = elaborate(term, undefined, ctx);
    assertEqual(printTerm(elabRes.term), "five", "IA1.2: (constId five) should elaborate to five (A inferred as Nat)");
    assertEqual(printTerm(elabRes.type), "Nat", "IA1.2: Type of (constId five) should be Nat");

    resetMyLambdaPi();
    setDebugVerbose(false);
    defineGlobal("Nat", Type(), undefined, true, false, true); // isTypeNameLike: true, isConstantSymbol: true
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
        // assert(finalYParamType.tag === 'Var' && finalYParamType.name === outerLamParamName, `IA2.1: Inner lambda's param type should be the var bound by outer implicit lambda. Expected Var(${outerLamParamName}), Got ${printTerm(finalYParamType)}`);
        } else {
        assert(false, "IA2.1: elabTerm was not a Lam as expected.");
    }


    resetMyLambdaPi();
    setDebugVerbose(false);
    defineGlobal("Eq", Pi("T", Icit.Impl, Type(), T_param => Pi("x", Icit.Expl, T_param, _ => Pi("y", Icit.Expl, T_param, _ => Type()))));
    defineGlobal("refl", Pi("T", Icit.Impl, Type(), T_param => Pi("x", Icit.Expl, T_param, x_param => App(App(App(Var("Eq"),T_param,Icit.Impl),x_param,Icit.Expl),x_param,Icit.Expl) )));
    defineGlobal("f_inj", Pi("T", Icit.Impl, Type(), T_param => Pi("x", Icit.Expl, T_param, _ => T_param)), undefined, false, true); 
    defineGlobal("g_noninj", Pi("T", Icit.Impl, Type(), T_param => Pi("x", Icit.Expl, T_param, _ => T_param)), undefined, false, false); 

    defineGlobal("Nat", Type(), undefined, true, false, true); // isTypeNameLike: true, isConstantSymbol: true
    defineGlobal("a_val", Var("Nat"), undefined, true); // isConstantSymbol: true
    defineGlobal("b_val", Var("Nat"), undefined, true); // isConstantSymbol: true

    const hole1 = Hole("?h1_ia3");
    const term_f_a = App(App(Var("f_inj"), Var("Nat"), Icit.Impl), Var("a_val"), Icit.Expl);
    const term_f_h1 = App(App(Var("f_inj"), Var("Nat"), Icit.Impl), hole1, Icit.Expl);
    addConstraint(term_f_a, term_f_h1, "IA3.1 Constraint: f_inj a = f_inj ?h1 (injective)");
    solveConstraints(ctx);
    console.log(`[DEBUG CHECK IA3.1] DEBUG_VERBOSE before elaborate(hole1): ${getDebugVerbose()}`);
    elaborate(hole1, Var("Nat"), ctx);

    console.log(`[TEST IA3.1] After elaborate for ?h1_ia3:`);
    console.log(`[TEST IA3.1]   hole1 direct: ${printTerm(hole1)}`);
    const hole1Ref = getTermRef(hole1);
    console.log(`[TEST IA3.1]   getTermRef(hole1): ${printTerm(hole1Ref)}`);
    // For more detailed structure inspection of the hole object itself:
    console.log(`[TEST IA3.1]   hole1 object structure:`, JSON.stringify(hole1, (key, value) => {
        if (value && typeof value === 'object' && value.tag && typeof value.body === 'function') return `${value.tag} (body as func)`; // Avoid serializing functions
        if (value && typeof value === 'object' && value.tag && typeof value.bodyType === 'function') return `${value.tag} (bodyType as func)`;
        if (typeof value === 'function') return '<function>';
        return value;
    }, 2));
    if (hole1.tag === 'Hole' && hole1.ref) {
        console.log(`[TEST IA3.1]   hole1.ref direct: ${printTerm(hole1.ref)}`);
    }


    assert(areEqual(getTermRef(hole1), Var("a_val"), ctx), "IA3.1: For injective f_inj, (f_inj a = f_inj ?h1) should solve ?h1 to a_val");

    resetMyLambdaPi();
    setDebugVerbose(false);
    defineGlobal("Eq", Pi("T", Icit.Impl, Type(), T_param => Pi("x", Icit.Expl, T_param, _ => Pi("y", Icit.Expl, T_param, _ => Type()))));
    defineGlobal("refl", Pi("T", Icit.Impl, Type(), T_param => Pi("x", Icit.Expl, T_param, x_param => App(App(App(Var("Eq"),T_param,Icit.Impl),x_param,Icit.Expl),x_param,Icit.Expl) )));
    defineGlobal("f_inj", Pi("T", Icit.Impl, Type(), T_param => Pi("x", Icit.Expl, T_param, _ => T_param)), undefined, false, true); 
    defineGlobal("g_noninj", Pi("T", Icit.Impl, Type(), T_param => Pi("x", Icit.Expl, T_param, _ => T_param)), undefined, false, false);
    defineGlobal("Nat", Type(), undefined, true, false, true); // isTypeNameLike: true, isConstantSymbol: true
    defineGlobal("a_val", Var("Nat"), undefined, true); // isConstantSymbol: true

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

function runChurchEncodingTests() {
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
    defineGlobal("List_type", List_type_type, List_type_val, false, false, true);
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
    defineGlobal("Bool_type", Type(), Bool_type_val_original_with_FH, false, false, true);
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
        Lam("B_not_param", Icit.Expl, B_not_term =>
            Lam("t_not_param", Icit.Expl, t_not_actual_term =>
                Lam("f_not_param", Icit.Expl, f_not_actual_term =>
                    App(App(App(b_not_actual_term, B_not_term, Icit.Expl), f_not_actual_term, Icit.Expl), t_not_actual_term, Icit.Expl)
                )
            )
        )
    );
    defineGlobal("not_func", not_func_type, not_func_val);
    elabRes = elaborate(Var("not_func"), undefined, baseCtx);
    assert(areEqual(elabRes.type, not_func_type, baseCtx), "Church Test 8.1: not_func type check");

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
    defineGlobal("Eq_type", Eq_type_type_original, Eq_type_val, false, true, true);
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
    defineGlobal("Nat_type", Type(), Nat_type_val, false, true, true);
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
    // setDebugVerbose(true);
    // let eqTest : Eq _ hundred hundred = refl _ _;
    const eqTest_val_type_original = App(App(App(Var("Eq_type"), Var("Nat_type"), Icit.Expl), Var("hundred_val"), Icit.Expl), Var("hundred_val"), Icit.Expl);
    const eqTest_val_val = App(App(Var("refl_func"), FH(), Icit.Expl), FH(), Icit.Expl);
    defineGlobal("eqTest_val", eqTest_val_type_original, eqTest_val_val);
    elabRes = elaborate(Var("eqTest_val"), undefined, baseCtx);

    const eqTest_val_term = Var("eqTest_val");
    const eqTest_val_type_expected = App(App(App(Var("Eq_type"), Var("Nat_type"), Icit.Expl), Var("hundred_val"), Icit.Expl), Var("hundred_val"), Icit.Expl);
    const gdef = globalDefs.get("eqTest_val");
    console.log(`[DEBUG TEST 18.1] gdef type: ${printTerm(gdef.type)}`);
    console.log(`[DEBUG TEST 18.1] gdef value: ${printTerm(gdef.value)}`);
    console.log(`[DEBUG TEST 18.1] eqTest_val_term: ${printTerm(whnf(Var("eqTest_val"), baseCtx))}`);
    console.log(`[DEBUG TEST 18.1] elabRes.type: ${printTerm(elabRes.type)}`);
    console.log(`[DEBUG TEST 18.1] eqTest_val_type_expected: ${printTerm(eqTest_val_type_expected)}`);
    const n1_debug_18_1 = whnf(elabRes.type, baseCtx);
    const n2_debug_18_1 = whnf(eqTest_val_type_expected, baseCtx);
    console.log(`[DEBUG TEST 18.1] whnf(elabRes.type): ${printTerm(n1_debug_18_1)}`);
    console.log(`[DEBUG TEST 18.1] whnf(eqTest_val_type_expected): ${printTerm(n2_debug_18_1)}`);
    const isEqualDebug_18_1 = areEqual(elabRes.type, eqTest_val_type_expected, baseCtx);
    console.log(`[DEBUG TEST 18.1] areEqual result: ${isEqualDebug_18_1}`);

    assert(isEqualDebug_18_1, "Church Test 18.1: eqTest_val type check");

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
}


if (require.main === module) {
    let originalDebugVerbose = getDebugVerbose();
    setDebugVerbose(false); 
    
    try {
        setDebugVerbose(true);
        console.log(`[DEBUG CHECK] DEBUG_VERBOSE is initially: ${getDebugVerbose()}`);
        runPhase1Tests();
        // runNonLinearPatternTests(); 
        runImplicitArgumentTests();
        runElaborateNonNormalizedTest();
        runChurchEncodingTests();

    } catch (e) {
        console.error("A test suite threw an uncaught error:", e);
    } finally {
        setDebugVerbose(originalDebugVerbose); 
    }
}

export { runPhase1Tests, runImplicitArgumentTests, runElaborateNonNormalizedTest, runChurchEncodingTests, assertEqual, assert };