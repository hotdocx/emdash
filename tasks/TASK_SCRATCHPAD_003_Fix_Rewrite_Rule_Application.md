# Task: Fix Rewrite Rule Application for Obj_mkCat_eval and Hom_mkCat_eval

## Problem Description

The `emdash_v2_tests.ts` revealed two primary issues:
1.  The rewrite rule `Obj_mkCat_eval` (`Obj(mkCat_ $O $H $C) ==> $O`) was not being applied. This caused `Test 2.2: Obj(NatCategoryTerm) should reduce to NatType` to fail.
2.  The rewrite rule `Hom_mkCat_eval` (`Hom(mkCat_ $O $H $C, $X, $Y) ==> $H $X $Y`) failed to be added during setup. This was due to an unsolved constraint `Obj(mkCat_ $O $H $C) === $O` during the rule's type-checking phase, which itself was a symptom of `Obj_mkCat_eval` not firing.

## Root Cause Analysis

The root cause was identified in the `whnf` (weak head normal form) function in `src/core_logic.ts`. This function uses `isKernelConstantSymbolStructurally` (from `src/core_state.ts`) to decide whether to attempt applying user rewrite rules.
The `isKernelConstantSymbolStructurally` function was incorrectly returning `true` for `ObjTerm` and `HomTerm`. This prevented `whnf` from attempting to apply rewrite rules like `Obj_mkCat_eval` to terms headed by `Obj(...)` or `Hom(...)`.

## Implemented Solution

The `isKernelConstantSymbolStructurally` function in `src/core_state.ts` was modified. The new logic ensures that this function returns `false` for terms with the tags `ObjTerm` and `HomTerm`. This allows the `whnf` function to proceed with attempting to apply rewrite rules to these terms.

Specifically, the function was changed to:

```typescript
// src/core_state.ts
export function isKernelConstantSymbolStructurally(term: Term): boolean {
    const rt = getTermRef(term);
    if (rt.tag === 'Var') {
        const gdef = globalDefs.get(rt.name);
        return !!(gdef && gdef.isConstantSymbol); // True if it's a Var defined as a constant
    }

    // For other term tags, decide if they should bypass rewrite rules.
    // ObjTerm and HomTerm should NOT bypass, so they are NOT listed here.
    // Other structural terms might still be shielded.
    switch (rt.tag) {
        case 'CatTerm':
        case 'FunctorCategoryTerm':
        case 'FMap0Term':
        case 'FMap1Term':
        case 'NatTransTypeTerm':
        case 'NatTransComponentTerm':
        case 'HomCovFunctorIdentity':
        case 'SetTerm':
            // These are structural and typically shouldn't be rewritten *as a whole* by general rules.
            return true;
        case 'ObjTerm':
        case 'HomTerm':
            // These should allow rewrite rules like Obj_mkCat_eval and Hom_mkCat_eval.
            return false;
        case 'Type': // Type itself is a primitive, doesn't get rewritten.
            return true;
        default:
            // For any tag not explicitly listed as true, assume false.
            // This includes Lam, App, Pi, Hole, and any future tags not covered.
            return false;
    }
}
```

## Expected Outcome

1.  The `Obj_mkCat_eval` rule should now apply correctly.
2.  `Test 2.2` in `emdash_v2_tests.ts` (i.e., `Obj(NatCategoryTerm)` reducing to `NatType`) should pass.
3.  The `Hom_mkCat_eval` rule should be added successfully during system setup, as the blocking constraint should now be resolvable.
4.  Overall, the system's rewrite rule mechanism should be more robust for these types of projection rules.

## Next Steps

1.  Run the `emdash_v2_tests.ts` to confirm the fixes.
2.  If tests pass, this task can be considered complete.
3.  If new issues arise related to pattern matching (e.g., the lambda elaboration `(λ {Y_obj : $O}. (λ {Z_obj : $O}. $C))` interaction with rules), a new task should be created to address them.

## Status

-   [x] Problem identified
-   [x] Root cause analyzed
-   [x] Solution implemented in `src/core_state.ts`
-   [ ] Verification (pending test execution by the user)

We are ready to archive this task file if the tests pass. The next user prompt should be to run the tests. 