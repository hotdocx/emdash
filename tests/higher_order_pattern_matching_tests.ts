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
        // console.log("Test 1 $F:", printTerm(fSubst));
        assert(areEqual(fSubst, Var("GlobalFunc"), baseCtx), "Test 1: $F should be GlobalFunc.");
    });

    it("Test 2: Eta-like pattern (λx. $F.[] x) FAILS to match (λy. (λz.y) AnotherGlobalConst) due to scope", () => {
        // Pattern: (λx: MyType. $F.[] x)
        const pattern = Lam("x", Icit.Expl, Var("MyType"), 
            (vx) => App(Hole(pvarF, []), vx, Icit.Expl));

        // Term: (λy: MyType. (λz: AnotherType. y) AnotherGlobalConst)
        // The body ( (λz.y) AnotherGlobalConst ) reduces to y.
        // So, $F.[] x is trying to match y (where x and y are alpha-equivalent).
        // $F would need to match (λz.y), but this term contains y freely (violating $F.[])
        const termToMatch = Lam("y", Icit.Expl, Var("MyType"), 
            (_vy) => App( Lam("z", Icit.Expl, Var("AnotherType"), (vz) => Var("y")), Var("AnotherGlobalConst"), Icit.Expl)
        );

        const subst = matchPattern(pattern, termToMatch, baseCtx, patternVarDecls);
        // console.log("Test 2 Subst:", subst ? Array.from(subst.entries()).map(([k,v]) => [k, printTerm(v)]) : null);
        assert(subst === null, "Test 2: Match should FAIL due to scope violation for $F.[].");
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
        // gSubst should be App(Var("GFuncForT3"), Var("a")) 
        // because $G.[x] (where x corresponds to 'a') matched App(Var("GFuncForT3"), Var("a")).
        const expectedGSubst = App(Var("GFuncForT3"), Var("a"));
        
        console.log("Test 3 $G raw substitution:", printTerm(gSubst));
        console.log("Test 3 Expected for $G:", printTerm(expectedGSubst));
        
        // We need to check areEqual(gSubst, expectedGSubst) in a context where 'a' is understood.
        // Or, more simply, the printTerm output should be structurally identical if names line up.
        // Since `gSubst` captures the term `App(Var("GFuncForT3"), Var("a"))` where "a" is the name from termT3,
        // direct comparison should work.
        assert(areEqual(gSubst, expectedGSubst, baseCtx), "Test 3: $G should be (GFuncForT3 a).");
    });

    it("Test 4: Mixed scope (λx y. $G.[x] y) FAILS (λa b. (GlobalFuncTakesTwo a b) b)", () => {
        // Pattern: (λx:MyType. λy:AnotherType. ($G.[x] y) )
        // $G.[x] allows x, forbids y.
        const pattern = Lam("x", Icit.Expl, Var("MyType"), 
            (_vx) => Lam("y", Icit.Expl, Var("AnotherType"), 
                (vy) => App(Hole(pvarG, ["x"]), vy, Icit.Expl)
            )
        );
        // Term: (λa:MyType. λb:AnotherType. ( (GlobalFuncTakesTwo a b) b) )
        // $G.[x] (where x~a, y~b) would need to match (GlobalFuncTakesTwo a b). 
        // This matched term `(GlobalFuncTakesTwo a b)` has 'b' (which corresponds to pattern's 'y') free in it.
        // But 'y' is NOT in $G.[x]'s allowed list `["x"]`. So it should fail.
        const termToMatch = Lam("a", Icit.Expl, Var("MyType"),
            (va) => Lam("b", Icit.Expl, Var("AnotherType"),
                (vb) => App( App(App(Var("GlobalFuncTakesTwo"), va, Icit.Expl), vb, Icit.Expl), vb, Icit.Expl) // Body: ((GlobalFuncTakesTwo a b) b)
            )
        );
        const subst = matchPattern(pattern, termToMatch, baseCtx, patternVarDecls);
        // console.log("Test 4 Subst:", subst ? Array.from(subst.entries()).map(([k,v]) => [k, printTerm(v)]) : null);
        assert(subst === null, "Test 4: Match should FAIL due to scope violation for $G.[x].");
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
        // console.log("Test 5 $F:", printTerm(fSubst));
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
        // console.log("Test 6 $F:", printTerm(fSubst));
        assert(areEqual(fSubst, Var("GlobalFunc"), baseCtx), "Test 6: $F should be GlobalFunc.");
    });

     it("Test 7: Eta-like pattern (λx. $F.[] x) matches (λy. y)", () => {
        // Pattern: (λx: MyType. $F.[] x)
        const pattern = Lam("x", Icit.Expl, Var("MyType"), 
            (vx) => App(Hole(pvarF, []), vx, Icit.Expl)); 
        
        // Term: (λy: MyType. y)
        const termToMatch = Lam("y", Icit.Expl, Var("MyType"), (vy) => vy);

        const subst = matchPattern(pattern, termToMatch, baseCtx, patternVarDecls);
        // $F.[] x matches y. So $F$ should match (λz.z) (Identity function for MyType)
        // The term matched by $F$ is (λz.z), which does not contain x (pattern var) freely.
        assert(subst !== null, "Test 7: Match should succeed.");
        assert(subst!.has(pvarF), "Test 7: $F should be in substitution.");
        const fSubst = getTermRef(subst!.get(pvarF)!);
        // Expected $F$ is Lam("z_id", Icit.Expl, Var("MyType"), id_vz => id_vz)
        const expectedF = Lam("z_id", Icit.Expl, Var("MyType"), id_vz => id_vz);
        console.log("Test 7 $F:", printTerm(fSubst));
        console.log("Test 7 Expected $F:", printTerm(expectedF));
        assert(areEqual(fSubst, expectedF, baseCtx), "Test 7: $F should be identity lambda.");
    });

}); 