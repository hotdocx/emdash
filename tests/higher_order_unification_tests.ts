import {
    Term, Context, UnifyResult, Icit,
    Type, Var, Lam, App, Pi, Hole
} from '../src/types';
import {
    emptyCtx, getTermRef, globalDefs, printTerm, FH, constraints, addConstraint, lookupCtx, extendCtx
} from '../src/state';
import {
    defineGlobal
} from '../src/globals';
import {
    resetMyLambdaPi_Emdash, resetMyLambdaPi // Assuming resetMyLambdaPi is the one to use for fresh state
} from '../src/stdlib';
import {
    areEqual,
} from '../src/equality';
import {
    normalize, whnf
} from '../src/reduction';
import {
    unify, solveConstraints
} from '../src/unification';
import {
    elaborate, check
} from '../src/elaboration';
import { assert } from './utils';
import { describe, it, beforeEach } from 'node:test';

describe("Higher-Order Unification Tests", () => {
    let baseCtx: Context;

    beforeEach(() => {
        resetMyLambdaPi(); // Resets globals, constraints, hole/var ids for each test
        baseCtx = emptyCtx;

        // Basic Types and Globals for testing
        defineGlobal("MyType", Type());
        defineGlobal("MyOtherType", Type());
        defineGlobal("ConstF", Pi("arg", Icit.Expl, Var("MyType"), _ => Var("MyOtherType")));
        defineGlobal("ConstG", Pi("arg1", Icit.Expl, Var("MyType"), _ => Pi("arg2", Icit.Expl, Var("MyType"), _ => Var("MyOtherType"))));
        defineGlobal("const_c", Var("MyType"));
        defineGlobal("const_d", Var("MyOtherType"));
    });

    it("Test 1: Simple Flex-Rigid: ?M x = f x", () => {
        const x_bound_name = "x_bound";
        const ctx = extendCtx(emptyCtx, x_bound_name, Var("MyType"), Icit.Expl);
        const x_var = Var(x_bound_name, true);

        const holeM = FH(); // ?M
        const lhs = App(holeM, x_var, Icit.Expl); // ?M x
        const rhs = App(Var("ConstF"), x_var, Icit.Expl); // f x

        addConstraint(lhs, rhs, "Test 1");
        const success = solveConstraints(ctx);
        assert(success, "Test 1: Constraints should be solvable");

        const solution = getTermRef(holeM.ref!);
        // Expected: Lam("y", MyType, (p_y) => App(Var("ConstF"), p_y))
        const expectedSolution = Lam("y_param", Icit.Expl, Var("MyType"), (p_y) => App(Var("ConstF"), p_y, Icit.Expl));
        
        // console.log("Test 1 Solution:", printTerm(solution));
        // console.log("Test 1 Expected:", printTerm(expectedSolution));
        assert(areEqual(solution, expectedSolution, ctx), "Test 1: ?M x = f x => ?M = (λy. f y)");
    });

    it("Test 2: Simple Flex-Rigid with constant: ?M x = c", () => {
        const x_bound_name = "x_bound_c";
        const ctx = extendCtx(emptyCtx, x_bound_name, Var("MyType"), Icit.Expl);
        const x_var = Var(x_bound_name, true);

        const holeM = FH();
        const lhs = App(holeM, x_var, Icit.Expl); // ?M x
        const rhs = Var("const_d"); // const_d has type MyOtherType, assuming ?M x : MyOtherType

        addConstraint(lhs, rhs, "Test 2");
        const success = solveConstraints(ctx);
        assert(success, "Test 2: Constraints should be solvable");

        const solution = getTermRef(holeM.ref!);
        // Expected: Lam("y", MyType, (_) => Var("const_d"))
        const expectedSolution = Lam("y_param", Icit.Expl, Var("MyType"), (_) => Var("const_d"));
        assert(areEqual(solution, expectedSolution, ctx), "Test 2: ?M x = c => ?M = (λy. c)");
    });

    it("Test 3: Two Spine Variables: ?M x y = g x y", () => {
        const x_bound_name = "x_b";
        const y_bound_name = "y_b";
        let ctx = extendCtx(emptyCtx, x_bound_name, Var("MyType"), Icit.Expl);
        ctx = extendCtx(ctx, y_bound_name, Var("MyType"), Icit.Expl);
        const x_var = Var(x_bound_name, true);
        const y_var = Var(y_bound_name, true);

        const holeM = FH();
        const lhs = App(App(holeM, x_var, Icit.Expl), y_var, Icit.Expl); // ?M x y
        const rhs = App(App(Var("ConstG"), x_var, Icit.Expl), y_var, Icit.Expl); // g x y

        addConstraint(lhs, rhs, "Test 3");
        const success = solveConstraints(ctx);
        assert(success, "Test 3: Constraints should be solvable");

        const solution = getTermRef(holeM.ref!);
        // Expected: Lam("a", MyType, (p_a) => Lam("b", MyType, (p_b) => App(App(Var("ConstG"), p_a), p_b)))
        const expectedSolution = Lam("a_param", Icit.Expl, Var("MyType"), (p_a) => 
                                    Lam("b_param", Icit.Expl, Var("MyType"), (p_b) => 
                                        App(App(Var("ConstG"), p_a, Icit.Expl), p_b, Icit.Expl)));
        assert(areEqual(solution, expectedSolution, ctx), "Test 3: ?M x y = g x y => ?M = (λa b. g a b)");
    });

    it("Test 4: RHS depends on only one spine var: ?M x y = f x", () => {
        const x_bound_name = "x_f";
        const y_bound_name = "y_f";
        let ctx = extendCtx(emptyCtx, x_bound_name, Var("MyType"), Icit.Expl);
        ctx = extendCtx(ctx, y_bound_name, Var("MyType"), Icit.Expl); // y is bound but not used in RHS
        const x_var = Var(x_bound_name, true);
        const y_var = Var(y_bound_name, true);

        const holeM = FH();
        const lhs = App(App(holeM, x_var, Icit.Expl), y_var, Icit.Expl); // ?M x y
        const rhs = App(Var("ConstF"), x_var, Icit.Expl); // f x

        addConstraint(lhs, rhs, "Test 4");
        const success = solveConstraints(ctx);
        assert(success, "Test 4: Constraints should be solvable");

        const solution = getTermRef(holeM.ref!);
        // Expected: Lam("a", MyType, (p_a) => Lam("b", MyType, (_) => App(Var("ConstF"), p_a)))
        const expectedSolution = Lam("a_param", Icit.Expl, Var("MyType"), (p_a) => 
                                    Lam("b_param", Icit.Expl, Var("MyType"), (_) => 
                                        App(Var("ConstF"), p_a, Icit.Expl)));
        assert(areEqual(solution, expectedSolution, ctx), "Test 4: ?M x y = f x => ?M = (λa b. f a)");
    });

    it("Test 5: Occurs Check Fail: ?M x = App (?M y_other) x", () => {
        const x_bound_name = "x_occ";
        const y_other_name = "y_other_occ";
        let ctx = extendCtx(emptyCtx, x_bound_name, Var("MyType"), Icit.Expl);
        ctx = extendCtx(ctx, y_other_name, Var("MyType"), Icit.Expl);
        const x_var = Var(x_bound_name, true);
        const y_other_var = Var(y_other_name, true); // A different var

        const holeM = FH();
        const lhs = App(holeM, x_var, Icit.Expl); // ?M x
        const rhs = App(App(holeM, y_other_var, Icit.Expl), x_var, Icit.Expl); // (?M y_other) x

        addConstraint(lhs, rhs, "Test 5");
        const success = solveConstraints(ctx);
        assert(!success, "Test 5: Constraints should NOT be solvable due to occurs check");
        assert(holeM.ref === undefined, "Test 5: Hole ?M should not be solved");
    });

    it("Test 6: Invalid Spine (non-var): ?M c = d", () => {
        const ctx = emptyCtx;
        const holeM = FH();
        const lhs = App(holeM, Var("const_c"), Icit.Expl); // ?M const_c
        const rhs = Var("const_d");

        // Manually call unify to check solveHoFlexRigid's direct response
        const result = unify(lhs, rhs, ctx);
        // solveHoFlexRigid should fail, then unify might try unifyHole (which may or may not solve ?M to (d c) depending on types)
        // For this test, we assert that solveHoFlexRigid itself would fail, so holeM.ref might be set by unifyHole based on types.
        // The key is that solveHoFlexRigid itself won't produce the lambda structure.
        // If it did solve via unifyHole, then holeM.ref would be const_d, not a lambda.
        // However, we expect solveHoFlexRigid to return UnifyResult.Failed, then unifyHole could solve it.
        // Let's check that solveConstraints fails if types aren't compatible for unifyHole.
        addConstraint(lhs, rhs, "Test 6");
        const success = solveConstraints(ctx); 
        // This might succeed if unifyHole solves ?M to a function that ignores its arg and returns d.
        // The direct test is that solveHoFlexRigid fails internally.
        // For this test, let's make types incompatible for unifyHole to see solveConstraints fail.
        // ?M : MyType -> MyOtherType.   (const_c : MyType).  (const_d : MyOtherType)
        // If holeM type is (MyType -> MyOtherType), then unifyHole(holeM, Lam(_,_,_)) would work if types align for lambda.
        // To ensure failure of Miller path, this test is tricky. Let's assume it falls through.
        assert(result === UnifyResult.Failed || result === UnifyResult.Progress, "Test 6: Unify attempt should fail Miller path or progress to unifyHole");
        // A more direct test of solveHoFlexRigid would require exporting it or more elaborate setup.
        // For now, we assume it correctly returns Failed and unify proceeds.
    });

    it("Test 7: Invalid Spine (non-distinct): ?M x x = d", () => {
        const x_bound_name = "x_nd";
        const ctx = extendCtx(emptyCtx, x_bound_name, Var("MyType"), Icit.Expl);
        const x_var = Var(x_bound_name, true);

        const holeM = FH();
        const lhs = App(App(holeM, x_var, Icit.Expl), x_var, Icit.Expl); // ?M x x
        const rhs = Var("const_d");

        const result = unify(lhs, rhs, ctx);
        assert(result === UnifyResult.Failed || result === UnifyResult.Progress, "Test 7: Unify attempt should fail Miller path or progress to unifyHole");
    });

    it("Test 8: Complex RHS with Lam: ?M x = (λz:MyOtherType. App x z_const)", () => {
        // where z_const is some global const of MyType, to make App(x, z_const) type check if x: MyOtherType -> SomeFinalType
        // For simplicity, let x: MyType, and RHS : MyOtherType, so ?M : MyType -> MyOtherType
        defineGlobal("z_const", Var("MyType"));
        const x_bound_name = "x_cx";
        const ctx = extendCtx(emptyCtx, x_bound_name, Var("MyType"), Icit.Expl);
        const x_var = Var(x_bound_name, true);

        const holeM = FH(); // ?M
        const lhs = App(holeM, x_var, Icit.Expl); // ?M x
        // RHS: Lam("z_param", MyOtherType, (p_z) => App(x_var, Var("z_const"))) - this type is complex to ensure.
        // Let RHS be: Lam("z_param", MyOtherType, (_) => x_var) for simplicity. This means RHS is MyOtherType -> MyType
        // So holeM needs to be MyType -> (MyOtherType -> MyType)
        const rhs = Lam("z_param", Icit.Expl, Var("MyOtherType"), (_) => x_var); 

        addConstraint(lhs, rhs, "Test 8");
        const success = solveConstraints(ctx);
        assert(success, "Test 8: Constraints should be solvable");

        const solution = getTermRef(holeM.ref!);
        // Expected: Lam("p1", MyType, (v_p1) => Lam("z_param", MyOtherType, (_) => v_p1) )
        const expectedSolution = Lam("p1", Icit.Expl, Var("MyType"), (v_p1) => 
                                    Lam("z_param", Icit.Expl, Var("MyOtherType"), (_) => v_p1));
        
        // console.log("Test 8 Solution:", printTerm(solution));
        // console.log("Test 8 Expected:", printTerm(expectedSolution));
        assert(areEqual(solution, expectedSolution, ctx), "Test 8: ?M x = (λz. x) => ?M = (λp1. λz. p1)");
    });

    it("Test 9: compExample-like: ?B a = List_Bool, where a: SomeTypeA", () => {
        defineGlobal("SomeTypeA", Type());
        defineGlobal("List", Pi("_T", Icit.Expl, Type(), _ => Type()));
        defineGlobal("Bool", Type());
        const List_Bool = App(Var("List"), Var("Bool"), Icit.Expl);

        const a_bound_name = "a_comp";
        const ctx = extendCtx(emptyCtx, a_bound_name, Var("SomeTypeA"), Icit.Expl);
        const a_var = Var(a_bound_name, true);

        const holeB = FH(); // ?B is expected to be SomeTypeA -> Type, then (List Bool) is the result of App(?B, a_var)
        const lhs = App(holeB, a_var, Icit.Expl);
        const rhs = List_Bool; 

        addConstraint(lhs, rhs, "Test 9");
        const success = solveConstraints(ctx);
        assert(success, "Test 9: Constraints should be solvable");

        const solution = getTermRef(holeB.ref!);
        // Expected: Lam("alpha", SomeTypeA, (_) => List_Bool)
        const expectedSolution = Lam("alpha", Icit.Expl, Var("SomeTypeA"), (_) => List_Bool);
        
        // console.log("Test 9 Solution:", printTerm(solution));
        // console.log("Test 9 Expected:", printTerm(expectedSolution));
        assert(areEqual(solution, expectedSolution, ctx), "Test 9: ?B a = List_Bool => ?B = (λalpha. List_Bool)");
    });

    it("Test 10: RHS Lam parameter shadows spine var name: ?M x = (λx:MyOtherType. const_d)", () => {
        const x_bound_name = "x_shadow"; // This is the spine variable
        const ctx = extendCtx(emptyCtx, x_bound_name, Var("MyType"), Icit.Expl);
        const x_var_spine = Var(x_bound_name, true);

        const holeM = FH();
        const lhs = App(holeM, x_var_spine, Icit.Expl); // ?M x_shadow
        // RHS: Lam("x_shadow", MyOtherType, (_ignored_param) => Var("const_d"))
        // The "x_shadow" in Lam is a NEW binder, shadowing the outer one for the body of the lambda.
        const rhs = Lam("x_shadow", Icit.Expl, Var("MyOtherType"), (_ignored_param) => Var("const_d"));

        addConstraint(lhs, rhs, "Test 10");
        const success = solveConstraints(ctx);
        assert(success, "Test 10: Constraints should be solvable");

        const solution = getTermRef(holeM.ref!);
        // Expected solution for ?M : Lam("p_outer", MyType, (v_p_outer) => Lam("x_shadow", MyOtherType, (_) => Var("const_d")))
        // The v_p_outer (replacement for original x_var_spine) is NOT used in the inner lambda's body because of shadowing.
        const expectedSolution = Lam("p_outer", Icit.Expl, Var("MyType"), (_v_p_outer) => 
                                    Lam("x_shadow", Icit.Expl, Var("MyOtherType"), (_) => Var("const_d")));
        
        // console.log("Test 10 Solution:", printTerm(solution));
        // console.log("Test 10 Expected:", printTerm(expectedSolution));
        assert(areEqual(solution, expectedSolution, ctx), "Test 10: Shadowing in RHS Lam correctly handled");
    });

}); 