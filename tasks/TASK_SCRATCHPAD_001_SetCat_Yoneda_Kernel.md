## Task: Implement Set Category and Yoneda Primitives (Kernel Focus)

### Implemented:

- **`core_types.ts`**:
    - Added `HomCovFunctorIdentity` to `BaseTerm` union: `| { tag: 'HomCovFunctorIdentity', domainCat: Term, objW_InDomainCat: Term }`.
    - Added constructor `HomCovFunctorIdentity(domainCat: Term, objW_InDomainCat: Term)`. 

- **`core_logic.ts`**:
    - `areStructurallyEqualNoWhnf`: Added case for `HomCovFunctorIdentity` (compares `domainCat`, `objW_InDomainCat`).
    - `whnf`:
        - `HomTerm` case: Added logic to reduce `Hom Set X Y` to `Π (_ : X). Y` (approximating `X → Y`).
        - `FMap0Term` case: Added logic to reduce `fapp0 (hom_cov A W) Y` to `HomTerm A W Y`.
    - `normalize`: Added case for `HomCovFunctorIdentity` (normalizes `domainCat`, `objW_InDomainCat`).
    - `areEqual`: Added case for `HomCovFunctorIdentity` (compares components using `areEqual` after `whnf`).
    - `termContainsHole`: Added case for `HomCovFunctorIdentity` (recurses on `domainCat`, `objW_InDomainCat`).
    - `unify`:
        - Added rule: if `ObjTerm A` is unified with `Type`, add constraint `A === Set`.
        - `HomCovFunctorIdentity` case: Unifies `domainCat` and `objW_InDomainCat` of both terms.
    - `collectPatternVars`: Added case for `HomCovFunctorIdentity`.

- **`core_elaboration.ts`**:
    - `infer`: Added case for `HomCovFunctorIdentity`.
        - Infers type as `ObjTerm(FunctorCategoryTerm(domainCat, globalSetTerm))`.
    - `matchPattern`: Added case for `HomCovFunctorIdentity`.
    - `applySubst`: Added case for `HomCovFunctorIdentity`.
    - `printTerm`: Added case for `HomCovFunctorIdentity` (e.g., `(HomCovFunctor domainCat objW_InDomainCat)`).
    - Fixed a linter error (incorrect variable name in error message).

- **`core_context_globals.ts`**:
    - Created `setupCatTheoryPrimitives(ctx: Context)`:
        - Defines global `"Set"` as `CatTerm()` (constant, injective, typeNameLike=true).
        - Defines global `"hom_cov"`:
            - Type: `Π [A : Cat], Π (W: Obj A), Obj (Functor A Set)`
            - Value: `Lam A_impl Lam W_expl => HomCovFunctorIdentity(A_impl, W_expl)`
            - Marked as constant and injective.
        - Adds user rewrite rule `"naturality_direct_hom_cov_fapp1_tapp"`:
            - LHS: `App(FMap1Term(HomCovFunctorIdentity($A_cat, $W_obj), FMap1Term($G_func, $a_morph, ...), ...), NatTransComponentTerm($eps_transf, $X_obj, ...))`
            - RHS: `App(FMap1Term(HomCovFunctorIdentity($A_cat, $W_obj), FMap1Term($F_func, $a_morph, ...), ...), NatTransComponentTerm($eps_transf, $X_prime_obj, ...))`
    - `resetMyLambdaPi_Emdash`: Calls `setupCatTheoryPrimitives(emptyCtx)`.

### Remaining to be Implemented (for this task or future):

- Extensive testing of the new primitives and rules.
- The `emdash_specification_lambdapi.lp` mentions `Hom_Type`. Currently, `HomTerm` directly produces a `Type`. The reduction `fapp0 (hom_cov $X) $Y ↪ Hom_Type $X $Y` is implemented as `fapp0 (hom_cov A W) Y` reducing to `HomTerm A W Y`. This seems consistent with the TypeScript structure where `HomTerm` itself is the representation of the type of morphisms.
- The `τ` type decoder is not implemented, as per instructions.
- Contravariant Yoneda (`hom_con`) is not yet implemented.
- `Cat_cat` and related concepts are explicitly skipped for now.

### Next Steps:

- Proceed with testing the current implementations.
- Address any bugs or inconsistencies found during testing.
- The next main task could involve implementing the extensionality rules for `Set` or further kernel features like `Cat_cat` or the skipped rules from the "EXTRA KERNEL SPECIFICATION" section of the LP file.

Ready to archive this Task file and move on to the next main Task after testing and potential bug fixes. 