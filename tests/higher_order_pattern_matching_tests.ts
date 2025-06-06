import {
    Term, Context, UnifyResult, Icit,
    Type, Var, Lam, App, Pi, Hole, PatternVarDecl, Substitution
} from '../src/types';
import {
    emptyCtx, getTermRef, globalDefs, printTerm, FH, constraints, addConstraint, lookupCtx, extendCtx, freshHoleName
} from '../src/state';
import {
    defineGlobal, addRewriteRule
} from '../src/globals';
import {
    resetMyLambdaPi_Emdash, resetMyLambdaPi
} from '../src/stdlib';
import { areEqual } from '../src/equality';
import { normalize, whnf } from '../src/reduction';
import { matchPattern, applySubst } from '../src/pattern';
import { assert } from './utils';
import { describe, it, beforeEach } from 'node:test';

describe("Higher-Order Pattern Matching Tests", () => {
    let baseCtx: Context;
    const pvarF = "$F";
    const pvarG = "$G";
    const pvarX = "$X";
    const patternVarDecls: PatternVarDecl[] = [pvarF, pvarG, pvarX];

    beforeEach(() => {
        resetMyLambdaPi(); // Use Emdash reset to get Cat, Set, etc.
        baseCtx = emptyCtx;

        // Basic Types and Globals for testing
        defineGlobal("MyType", Type());
        defineGlobal("AnotherType", Type());
        defineGlobal("GlobalFunc", Pi("arg", Icit.Expl, Var("MyType"), _ => Var("AnotherType")));
        defineGlobal("GlobalConst", Var("MyType"));
        defineGlobal("AnotherGlobalConst", Var("AnotherType"));

        defineGlobal("GlobalFuncTakesTwo", 
            Pi("arg1", Icit.Expl, Var("MyType"), _ => 
            Pi("arg2", Icit.Expl, Var("AnotherType"), _ => Type()))
        );
        defineGlobal("SomeOtherGlobalFunc", 
            Pi("arg", Icit.Expl, Var("AnotherType"), _ => Var("MyType"))
        );

    });

    it("Test 1: Eta-like pattern (λx. $F.[] x) matches (λy. GlobalFunc y)", () => {
        const pattern = Lam("x", Icit.Expl, Var("MyType"), 
            (vx) => App(Hole(pvarF, []), vx, Icit.Expl)); 
        
        const termToMatch = Lam("y", Icit.Expl, Var("MyType"), 
            (vy) => App(Var("GlobalFunc"), vy, Icit.Expl));

        const subst = matchPattern(pattern, termToMatch, baseCtx, patternVarDecls);
        assert(subst !== null, "Test 1: Match should succeed.");
        assert(subst!.has(pvarF), "Test 1: $F should be in substitution.");
        
        const fSubst = getTermRef(subst!.get(pvarF)!);
        const expectedF = Lam("y", Icit.Expl, Var("MyType"), (vy) => App(Var("GlobalFunc"), vy, Icit.Expl));

        assert(areEqual(fSubst, expectedF, baseCtx), "Test 1: $F should be (λy. GlobalFunc y).");
    });

    it("Test 2: Eta-like pattern (λx. $F.[] x) now PASSES to match (λy. y)", () => {
        // Pattern: (λx: MyType. $F.[] x)
        const pattern = Lam("x", Icit.Expl, Var("MyType"), 
            (vx) => App(Hole(pvarF, []), vx, Icit.Expl));

        // Term: (λy: MyType. (λz: AnotherType. y) AnotherGlobalConst)
        // The body normalizes to just `y`.
        // So, $F.[] x matches y. HO Unification solves this to $F := (λv. v).
        // This solution has no free variables, so the scope check $F.[] passes.
        const termToMatch = Lam("y", Icit.Expl, Var("MyType"), 
            (_vy) => App( Lam("z", Icit.Expl, Var("AnotherType"), (vz) => Var("y")), Var("AnotherGlobalConst"), Icit.Expl)
        );

        const subst = matchPattern(pattern, termToMatch, baseCtx, patternVarDecls);
        assert(subst !== null, "Test 2: Match should now SUCCEED.");
        assert(subst!.has(pvarF), "Test 2: $F should be in substitution.");
        const fSubst = getTermRef(subst!.get(pvarF)!);
        const expectedF = Lam("v", Icit.Expl, Var("MyType"), v => v);
        
        assert(areEqual(fSubst, expectedF, baseCtx), "Test 2: $F should be the identity function.");
    });

    it("Test 3: Mixed scope (λx y. $G.[x] y) matches (λa b. (GFuncForT3 a) b)", () => {
        defineGlobal("GFuncForT3", Pi("argT3_1", Icit.Expl, Var("MyType"), _ => Pi("argT3_2", Icit.Expl, Var("AnotherType"), _ => Var("MyType"))));
        
        // Pattern: (λx:MyType. λy:AnotherType. ($G.[x] y) )
        // $G.[x] means G can contain x (from pattern) but not y (from pattern)
        const patternT3 = Lam("x", Icit.Expl, Var("MyType"), 
                                (vx) => Lam("y", Icit.Expl, Var("AnotherType"), 
                                    (vy) => App(Hole(pvarG, ["x"]), vy, Icit.Expl)));
        
        // Term: (λa:MyType. λb:AnotherType. ( (GFuncForT3 a) b) )
        // $G.[x] will match (GFuncForT3 a). This term contains 'a' (which corresponds to pattern's 'x').
        // 'a' is in the allowed list ["x"] for $G. So this part is fine.
        // The variable 'b' (corresponding to pattern's 'y') is not free in (GFuncForT3 a). This is also fine.
        const termT3 = Lam("a", Icit.Expl, Var("MyType"), 
                            (va) => Lam("b", Icit.Expl, Var("AnotherType"), 
                                (vb) => App( App(Var("GFuncForT3"), va, Icit.Expl), vb, Icit.Expl)));

        const subst = matchPattern(patternT3, termT3, baseCtx, patternVarDecls);
        assert(subst !== null, "Test 3: Match should succeed.");
        assert(subst!.has(pvarG), "Test 3: $G should be in substitution.");
        
        const gSubst = getTermRef(subst!.get(pvarG)!);
        // With HO matching, $G y matches (GFuncForT3 a) b.
        // So, $G should be solved to λy. (GFuncForT3 a) y
        const expectedGSubst = Lam("b", Icit.Expl, Var("AnotherType"), (vb) => App(App(Var("GFuncForT3"), Var("a"), Icit.Expl), vb, Icit.Expl));
        
        // We need to check areEqual(gSubst, expectedGSubst) in a context where 'a' is understood.
        const checkCtx = extendCtx(baseCtx, "a", Var("MyType"));
        assert(areEqual(gSubst, expectedGSubst, checkCtx), "Test 3: $G should be (λb. (GFuncForT3 a) b).");
    });

    it("Test 4: Mixed scope (λx y. $G.[x] y) now PASSES (λa b. (GlobalFuncTakesTwo a b) b)", () => {
        // Pattern: (λx:MyType. λy:AnotherType. ($G.[x] y) )
        // $G.[x] allows x, forbids y.
        const pattern = Lam("x", Icit.Expl, Var("MyType"), 
            (_vx) => Lam("y", Icit.Expl, Var("AnotherType"), 
                (vy) => App(Hole(pvarG, ["x"]), vy, Icit.Expl)
            )
        );
        // Term: (λa:MyType. λb:AnotherType. ( (GlobalFuncTakesTwo a b) b) )
        // HO matching: $G.[x] y matches ((GlobalFuncTakesTwo a b) b)
        // Solution for $G$ is λv. ((GlobalFuncTakesTwo a v) v).
        // Free vars of this solution is {'a'}. 'a' corresponds to 'x', which is in the allowed list for $G.[x].
        // So the match should now succeed.
        const termToMatch = Lam("a", Icit.Expl, Var("MyType"),
            (va) => Lam("b", Icit.Expl, Var("AnotherType"),
                (vb) => App( App(App(Var("GlobalFuncTakesTwo"), va, Icit.Expl), vb, Icit.Expl), vb, Icit.Expl) // Body: ((GlobalFuncTakesTwo a b) b)
            )
        );
        const subst = matchPattern(pattern, termToMatch, baseCtx, patternVarDecls);
        assert(subst !== null, "Test 4: Match should now SUCCEED due to HO unification.");
        assert(subst!.has(pvarG), "Test 4: $G should be in substitution.");

        const gSubst = getTermRef(subst!.get(pvarG)!);
        const expectedG = Lam("b_arg", Icit.Expl, Var("AnotherType"), (vb) => 
            App( App(App(Var("GlobalFuncTakesTwo"), Var("a"), Icit.Expl), vb, Icit.Expl), vb, Icit.Expl)
        );

        const checkCtx = extendCtx(baseCtx, "a", Var("MyType"));
        assert(areEqual(gSubst, expectedG, checkCtx), "Test 4: $G should be λb.((GlobalFuncTakesTwo a b) b)");
    });

    it("Test 5: Pattern var not in head (λx. GlobalFunc ($F.[x] GlobalConst))", () => {
        // Pattern: (λx:MyType. GlobalFunc ($F.[x] AnotherGlobalConst) )
        // $F.[x] AnotherGlobalConst should match SomeOtherGlobalFunc AnotherGlobalConst
        // So $F.[x] matches SomeOtherGlobalFunc. `SomeOtherGlobalFunc` has no free vars related to 'x'. 'x' is allowed. OK.
        const pattern = Lam("x", Icit.Expl, Var("MyType"),
            (_vx) => App(Var("GlobalFunc"), 
                         App(Hole(pvarF, ["x"]), Var("AnotherGlobalConst"), Icit.Expl), 
                         Icit.Expl
                        )
        );
        // Term: (λy:MyType. GlobalFunc (SomeOtherGlobalFunc AnotherGlobalConst))
        const termToMatch = Lam("y", Icit.Expl, Var("MyType"),
            (_vy) => App(Var("GlobalFunc"),
                         App(Var("SomeOtherGlobalFunc"), Var("AnotherGlobalConst"), Icit.Expl),
                         Icit.Expl
                        )
        );
        const subst = matchPattern(pattern, termToMatch, baseCtx, patternVarDecls);
        assert(subst !== null, "Test 5: Match should succeed.");
        assert(subst!.has(pvarF), "Test 5: $F should be in substitution.");
        const fSubst = getTermRef(subst!.get(pvarF)!);
        assert(areEqual(fSubst, Var("SomeOtherGlobalFunc"), baseCtx), "Test 5: $F should be SomeOtherGlobalFunc.");
    });

    it("Test 6: Simple $F x pattern: App($F, GlobalConst) matches App(GlobalFunc, GlobalConst)", () => {
        // Pattern: $F GlobalConst (no scope restriction on $F as patternAllowedLocalBinders is undefined)
        const pattern = App(Hole(pvarF), Var("GlobalConst"), Icit.Expl);
        // Term: GlobalFunc GlobalConst
        const termToMatch = App(Var("GlobalFunc"), Var("GlobalConst"), Icit.Expl);

        const subst = matchPattern(pattern, termToMatch, baseCtx, patternVarDecls);
        assert(subst !== null, "Test 6: Match should succeed.");
        assert(subst!.has(pvarF), "Test 6: $F should be in substitution.");
        const fSubst = getTermRef(subst!.get(pvarF)!);
        assert(areEqual(fSubst, Var("GlobalFunc"), baseCtx), "Test 6: $F should be GlobalFunc.");
    });

     it("Test 7: Eta-like pattern (λx. $F.[] x) matches (λy. y)", () => {
        // Pattern: (λx: MyType. $F.[] x)
        const pattern = Lam("x", Icit.Expl, Var("MyType"), 
            (vx) => App(Hole(pvarF, []), vx, Icit.Expl)); 
        
        // Term: (λy: MyType. y)
        const termToMatch = Lam("y", Icit.Expl, Var("MyType"), (vy) => vy);

        const subst = matchPattern(pattern, termToMatch, baseCtx, patternVarDecls);
        // $F.[] x matches y. HO Unification solves this to $F := (λz. z).
        // This solution has no free variables, so the scope check $F.[] passes.
        assert(subst !== null, "Test 7: Match should succeed.");
        assert(subst!.has(pvarF), "Test 7: $F should be in substitution.");
        const fSubst = getTermRef(subst!.get(pvarF)!);
        const expectedF = Lam("z_id", Icit.Expl, Var("MyType"), id_vz => id_vz);
        assert(areEqual(fSubst, expectedF, baseCtx), "Test 7: $F should be identity lambda.");
    });

}); 