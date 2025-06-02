## Task: Implement Set Category and Yoneda Primitives (Kernel Focus)

### Implemented:

- **`core_types.ts`**:
    - Added `HomCovFunctorIdentity` to `BaseTerm` union: `| { tag: 'HomCovFunctorIdentity', domainCat: Term, objW_InDomainCat: Term }`.
    - Added constructor `HomCovFunctorIdentity(domainCat: Term, objW_InDomainCat: Term)`.
    - **Added `SetTerm` to `BaseTerm` union: `| { tag: 'SetTerm' }` and its constructor `SetTerm()`.**

- **`core_logic.ts`**:
    - `areStructurallyEqualNoWhnf`: Added cases for `HomCovFunctorIdentity` and `SetTerm`.
    - `whnf`:
        - `HomTerm` case: Logic to reduce `Hom S X Y` (where `S` is `SetTerm()`) to `Π (_ : X). Y`.
        - `FMap0Term` case: Logic to reduce `fapp0 (hom_cov A W) Y` to `HomTerm A W Y`.
    - `normalize`: Added cases for `HomCovFunctorIdentity` and `SetTerm`.
    - `areEqual`: Added cases for `HomCovFunctorIdentity` and `SetTerm`.
    - `termContainsHole`: Added cases for `HomCovFunctorIdentity` and `SetTerm`.
    - `unify`:
        - Rule: `ObjTerm A === Type` adds constraint `A === SetTerm()`.
        - Added cases for `HomCovFunctorIdentity` and `SetTerm` (returns `UnifyResult.Solved`).
    - `collectPatternVars`: Added cases for `HomCovFunctorIdentity` and `SetTerm`.

- **`core_elaboration.ts`**:
    - `infer`: Added cases for `HomCovFunctorIdentity` and `SetTerm` (infers type of `SetTerm()` as `CatTerm()`).
    - `matchPattern`: Added cases for `HomCovFunctorIdentity` and `SetTerm`.
    - `applySubst`: Added cases for `HomCovFunctorIdentity` and `SetTerm`.
    - `printTerm`: Added cases for `HomCovFunctorIdentity` and `SetTerm` (prints as `Set`).
    - Fixed a linter error.

- **`core_context_globals.ts`**:
    - `EMDASH_CONSTANT_SYMBOLS_TAGS`: Added `'SetTerm'`.
    - `EMDASH_UNIFICATION_INJECTIVE_TAGS`: Added `'SetTerm'`.
    - `setupCatTheoryPrimitives(ctx: Context)`:
        - Defines global `"Set"` with type `CatTerm()` and value `SetTerm()` (constant, injective, typeNameLike=true).
        - Defines global `"hom_cov"`:
            - Type: `Π [A : Cat], Π (W: Obj A), Obj (Functor A SetTerm())`
            - Value: `Lam A_impl Lam W_expl => HomCovFunctorIdentity(A_impl, W_expl)`
            - Marked as constant and injective.
        - Adds user rewrite rule `"naturality_direct_hom_cov_fapp1_tapp"` using `SetTerm()` in patterns.
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