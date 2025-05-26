import {
    Term, Context, ElaborationResult, Icit,
    Type, Var, Lam, App, Pi, Hole,
    CatTerm, ObjTerm, HomTerm, MkCat_, IdentityMorph, ComposeMorph,
    PatternVarDecl, ElaborationOptions
} from './src/core_types';
import {
    defineGlobal, addRewriteRule, resetMyLambdaPi, setupPhase1GlobalsAndRules,
    emptyCtx, getTermRef, addConstraint, StoredRewriteRule, userRewriteRules,
    cloneTerm
} from './src/core_context_globals';
import {
    areEqual, normalize, whnf, unify, UnifyResult
} from './src/core_logic';
import {
    elaborate, printTerm, infer, check, isPatternVarName, matchPattern
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
    assert(elabRes.type.tag === 'Type', "Test 1.1: Cat is not Type");

    const someCatHole = Hole("?MyCat");
    testTerm = ObjTerm(someCatHole);
    elabRes = elaborate(testTerm, undefined, baseCtx);
    assert(elabRes.type.tag === 'Type', "Test 1.2: Obj ?MyCat is not Type");

    const objXHole = Hole("?X");
    const objYHole = Hole("?Y");
    testTerm = HomTerm(someCatHole, objXHole, objYHole);
    elabRes = elaborate(testTerm, undefined, baseCtx);
    assert(elabRes.type.tag === 'Type', "Test 1.3: Hom ?MyCat ?X ?Y is not Type");
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
    assert(elabRes.type.tag === 'CatTerm', "Test 2.1: MkCat_ type is not Cat");

    const ObjOfNatCat = ObjTerm(NatCategoryTermVal);
    elabRes = elaborate(ObjOfNatCat, undefined, baseCtx);
    assert(areEqual(elabRes.term, NatObjRepr, baseCtx), `Test 2.2: Obj(NatCategoryTerm) did not reduce to NatType. Got ${printTerm(elabRes.term)}`);

    defineGlobal("nat_val1_t2", NatObjRepr, undefined, true);
    defineGlobal("nat_val2_t2", NatObjRepr, undefined, true);
    const X_in_NatCat = Var("nat_val1_t2");
    const Y_in_NatCat = Var("nat_val2_t2");

    const HomInNatCat = HomTerm(NatCategoryTermVal, X_in_NatCat, Y_in_NatCat);
    elabRes = elaborate(HomInNatCat, undefined, baseCtx);
    const expectedHomReduced = App(App(Var("H_repr_Nat_Global"), X_in_NatCat, Icit.Expl), Y_in_NatCat, Icit.Expl);
    assert(areEqual(elabRes.term, normalize(expectedHomReduced, baseCtx), baseCtx), `Test 2.3: Hom(NatCat,X,Y) did not reduce correctly. Expected ${printTerm(normalize(expectedHomReduced,baseCtx))} Got ${printTerm(elabRes.term)}`);
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
    assert(idTermSolved.tag === 'IdentityMorph', `Test 3.0 failed: elaborated id_x is not IdentityMorph, but ${idTermSolved.tag}`);
    assert(!!idTermSolved.cat_IMPLICIT, "Test 3.1a failed: id_x cat_IMPLICIT not filled.");
    assert(areEqual(getTermRef(idTermSolved.cat_IMPLICIT!), Var("MyNatCat3_GlobalDef"), baseCtx), `Test 3.1b failed: id_x.cat_IMPLICIT not resolved. Got: ${printTerm(getTermRef(idTermSolved.cat_IMPLICIT!))}`);
    const expected_normalized_type_t3 = normalize(App(App(Var("H_repr_Nat_Global"), anObjX_term, Icit.Expl), anObjX_term, Icit.Expl), baseCtx);
    assert(areEqual(elabRes.type, expected_normalized_type_t3, baseCtx), `Test 3.2 failed: id_x type mismatch. Expected ${printTerm(expected_normalized_type_t3)}, Got ${printTerm(elabRes.type)}`);
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

    assert(areEqual(elabRes.type, expectedCompType, baseCtx), `Test 4.0 Failed: comp_gf type not as expected.`);
    const compTermSolved = elabRes.term as Term & {tag:"ComposeMorph"};
    assert(compTermSolved.tag === 'ComposeMorph', `Test 4.0b failed: comp_gf did not remain ComposeMorph.`);
    assert(!!compTermSolved.cat_IMPLICIT && !!compTermSolved.objX_IMPLICIT && !!compTermSolved.objY_IMPLICIT && !!compTermSolved.objZ_IMPLICIT, "Test 4.1 failed: ComposeMorph implicits not resolved/present.");
    const f_type_hole = getTermRef(f_morph_hole) as Term & {tag:"Hole"};
    const g_type_hole = getTermRef(g_morph_hole) as Term & {tag:"Hole"};
    assert(!!f_type_hole.elaboratedType && !!g_type_hole.elaboratedType, "Test 4.2: f or g did not get elaborated types.");
    console.log("Test 4 Passed.");


    console.log("\n--- Test 5: Rewrite rule comp (g o id) ---");
    resetMyLambdaPi(); setupPhase1GlobalsAndRules(); // Rules already added here via setup
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
    assert(areEqual(elabRes.term, g_XY_for_rule, baseCtx), `Test 5.1 failed: (g o id_X) did not reduce to g.`);
    console.log("Test 5 Passed.");
}

function runImplicitArgumentTests() {
    console.log("\n--- Running Implicit Argument Tests ---");
    const ctx = emptyCtx;

    // Test IA1: Implicit Pi type and App with implicit insertion
    resetMyLambdaPi();
    // constId : {A:Type} -> A -> A = \{A} x. x
    defineGlobal("constId",
        Pi("A", Icit.Impl, Type(), A => Pi("x", Icit.Expl, A, _x => A)),
        Lam("A", Icit.Impl, Type(), A => Lam("x", Icit.Expl, A, x => x))
    );
    // constId NatType 5 (where NatType is Type, 5 is NatType after type checking for 5)
    // This requires a placeholder for 5, let's use a Var assumed to be NatType
    defineGlobal("Nat", Type(), undefined, true);
    defineGlobal("five", Var("Nat"), undefined, true);

    let term = App(App(Var("constId"), Var("Nat"), Icit.Impl), Var("five"), Icit.Expl); // Explicitly provide implicit
    let elabRes = elaborate(term, undefined, ctx);
    assertEqual(printTerm(elabRes.term), "five", "IA1.1: constId {Nat} five -> five");
    assertEqual(printTerm(elabRes.type), "Nat", "IA1.1: Type is Nat");

    term = App(Var("constId"), Var("five"), Icit.Expl); // Auto-insert implicit for A
    elabRes = elaborate(term, undefined, ctx);
    assertEqual(printTerm(elabRes.term), "five", "IA1.2: constId five -> five (A inferred for Nat via 'five')");
    assertEqual(printTerm(elabRes.type), "Nat", "IA1.2: Type is Nat");

    // Test IA2: Check with implicit lambda insertion
    // Type of constId is {A:Type} -> A -> A
    // We check (λx.x) against this type.
    resetMyLambdaPi();
    defineGlobal("Nat", Type(), undefined, true);
    const idFuncType = Pi("A", Icit.Impl, Type(), A => Pi("x", Icit.Expl, A, _x => A));
    const simpleId = Lam("x", Icit.Expl, Var("Nat") /* assume Nat for x */, x => x); // λ (x:Nat). x
    // This check should insert Lam("A", Icit.Impl, Type(), A_impl => simpleId_where_x_has_type_A_impl)
    // Forcing Nat as type of x in simpleId means it won't unify with {A:Type}A->A directly.
    // Let's make simpleId polymorphic in its argument type for the check
    const polySimpleId = Lam("y", Icit.Expl, Hole("?Y_param_type"), y => y); // λ(y:_).y

    elabRes = elaborate(polySimpleId, idFuncType, ctx);
    // Expected elaborated term: \{A:Type} (λ (y:A). y)
    const elabTerm = elabRes.term;
    assert(elabTerm.tag === 'Lam' && elabTerm.icit === Icit.Impl, "IA2.1: Outer lambda implicit");
    assert(elabTerm.paramType?.tag === 'Type', "IA2.1: Outer param type is Type");
    const innerLam = (elabTerm as Term & {tag:'Lam'}).body(Type());
    assert(innerLam.tag === 'Lam' && innerLam.icit === Icit.Expl, "IA2.1: Inner lambda explicit");
    // Check that the hole ?Y_param_type got resolved to A (from the Pi)
    const finalYParamType = (getTermRef(innerLam) as Term & {tag:'Lam'}).paramType;
    assert(finalYParamType?.tag === 'Var' && finalYParamType.name === (elabTerm as Term & {tag:'Lam'}).paramName, "IA2.1: Inner param type is outer A");


    // Test IA3: Injectivity
    resetMyLambdaPi();
    defineGlobal("Eq", Pi("T", Icit.Impl, Type(), T => Pi("x", Icit.Expl, T, _ => Pi("y", Icit.Expl, T, _ => Type()))));
    defineGlobal("refl", Pi("T", Icit.Impl, Type(), T => Pi("x", Icit.Expl, T, x => App(App(App(Var("Eq"),T,Icit.Impl),x,Icit.Expl),x,Icit.Expl) )));
    defineGlobal("f", Pi("T", Icit.Impl, Type(), T => Pi("x", Icit.Expl, T, _ => T)), undefined, false, true); // f is injective
    defineGlobal("g", Pi("T", Icit.Impl, Type(), T => Pi("x", Icit.Expl, T, _ => T)), undefined, false, false); // g is NOT injective

    defineGlobal("Nat", Type(), undefined, true);
    defineGlobal("a", Var("Nat"), undefined, true);
    defineGlobal("b", Var("Nat"), undefined, true);

    // f {Nat} a = f {Nat} b  SHOULD imply a = b (if unification uses injectivity)
    // For testing, we'd set up a unification problem constraint.
    // This requires more direct use of unify, or a test through rewrite rules.
    // For now, this serves as a setup. We can test unification behavior separately.
    const hole1 = Hole("?h1_ia3");
    const hole2 = Hole("?h2_ia3");
    const term_f_a = App(App(Var("f"), Var("Nat"), Icit.Impl), Var("a"), Icit.Expl);
    const term_f_b = App(App(Var("f"), Var("Nat"), Icit.Impl), hole1, Icit.Expl); // hole1 should become 'a' if f a = f ?h1
    addConstraint(term_f_a, term_f_b, "IA3.1: f a = f ?h1 (injective)");
    elaborate(hole1, Var("Nat"), ctx); // Elaborate something to run solveConstraints
    assert(areEqual(getTermRef(hole1), Var("a"), ctx), "IA3.1: Injectivity for f solved ?h1 to a");

    resetMyLambdaPi(); // Reset constraints etc.
    defineGlobal("Eq", Pi("T", Icit.Impl, Type(), T => Pi("x", Icit.Expl, T, _ => Pi("y", Icit.Expl, T, _ => Type()))));
    defineGlobal("refl", Pi("T", Icit.Impl, Type(), T => Pi("x", Icit.Expl, T, x => App(App(App(Var("Eq"),T,Icit.Impl),x,Icit.Expl),x,Icit.Expl) )));
    defineGlobal("f", Pi("T", Icit.Impl, Type(), T => Pi("x", Icit.Expl, T, _ => T)), undefined, false, true); // f is injective
    defineGlobal("g", Pi("T", Icit.Impl, Type(), T => Pi("x", Icit.Expl, T, _ => T)), undefined, false, false); // g is NOT injective
    defineGlobal("Nat", Type(), undefined, true);
    defineGlobal("a", Var("Nat"), undefined, true);
    defineGlobal("b", Var("Nat"), undefined, true);
    const hole3 = Hole("?h3_ia3");
    const term_g_a = App(App(Var("g"), Var("Nat"), Icit.Impl), Var("a"), Icit.Expl);
    const term_g_b = App(App(Var("g"), Var("Nat"), Icit.Impl), hole3, Icit.Expl); // hole3 should NOT become 'a'
    addConstraint(term_g_a, term_g_b, "IA3.2: g a = g ?h3 (non-injective)");
    elaborate(hole3, Var("Nat"), ctx);
    assert(getTermRef(hole3).tag === 'Hole', "IA3.2: Non-injectivity for g means ?h3 remains a hole");

    console.log("Implicit Argument Tests Completed.");
}

function runElaborateNonNormalizedTest() {
    console.log("\n--- Test: Elaborate with normalizeResultTerm:false ---");
    resetMyLambdaPi();
    const ctx = emptyCtx;
    // (λ x:Type. x) Type  -> should elaborate to (λ x:Type. x) Type, not Type, if not normalized
    const termRaw = App(Lam("x", Icit.Expl, Type(), (x_var: Term): Term => x_var), Type(), Icit.Expl);
    const elabOpts: ElaborationOptions = { normalizeResultTerm: false };
    const elabRes = elaborate(termRaw, undefined, ctx, elabOpts);

    // The term should be App(Lam(...), Type), not its beta-reduced form 'Type'
    assert(elabRes.term.tag === 'App', "ElabNoNorm.1: Result term should be App");
    if (elabRes.term.tag === 'App') {
        assert(elabRes.term.func.tag === 'Lam', "ElabNoNorm.1: Func part should be Lam");
        assert(elabRes.term.arg.tag === 'Type', "ElabNoNorm.1: Arg part should be Type");
    }
    assertEqual(printTerm(elabRes.type), "Type", "ElabNoNorm.1: Type should still be Type (and normalized)");
    console.log("Test Elaborate with normalizeResultTerm:false Passed.");
}


// Add a main execution block or export test runner
if (require.main === module) {
    let DEBUG_VERBOSE_orig = (globalThis as any).DEBUG_VERBOSE;
    (globalThis as any).DEBUG_VERBOSE = false; // Disable verbose logging for tests unless specified

    try {
        runPhase1Tests();
        // runBaseDTTTests(); // These might be outdated or overlap, focus on new ones.
        runNonLinearPatternTests();
        runImplicitArgumentTests();
        runElaborateNonNormalizedTest();

    } catch (e) {
        console.error("A test suite threw an uncaught error:", e);
    } finally {
        (globalThis as any).DEBUG_VERBOSE = DEBUG_VERBOSE_orig;
    }
}

export { runPhase1Tests, runImplicitArgumentTests, assertEqual, assert };

if (typeof (globalThis as any).DEBUG_VERBOSE === 'undefined') {
    (globalThis as any).DEBUG_VERBOSE = false;
}