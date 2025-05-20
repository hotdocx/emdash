Great, I’ll begin a thorough analysis of the Emdash system based on the provided source code and Lambdapi specification. The goal will be to produce a detailed, publication-quality report in markdown format. It will include a critical code review, implementation summary, type-theoretic comparison with Lambdapi, discussion of problems and future work, and a roadmap for Phase 2 implementation (functors and transformations).

I’ll let you know once the first part of the report is ready.


# Emdash: A Dependently-Typed System for Synthetic Category Theory

## Project Summary

Emdash is a prototype dependently-typed language and type-checker implemented in TypeScript, designed to support *computational synthetic category theory*.  Its core idea is to treat **categories**, **objects**, and **morphisms** as first-class types and terms within a dependently-typed lambda calculus.  In Emdash, `Cat : Type` declares the type of categories; given `C:Cat`, one has `ObjTerm(C) : Type` (the type of objects of category *C*) and `HomTerm(C,X,Y) : Type` (the type of morphisms from object *X* to *Y* in *C*).  These design choices are guided by a Lambdapi-based specification (in *emdash\_specification\_lambdapi.lp*), which formalizes the intended rules and rewrite laws for categories, identities, composition, functors, and natural transformations.

Emdash is built on a basic λΠ-calculus **kernel** (inspired by Lambdapi) with extensions for categorical constructs.  The architecture follows a standard **bidirectional type-checking** and elaboration model with holes (metavariables) and constraints.  The system maintains a global context of definitions and rewrite rules, implements *weak-head normalization* (WHNF) with β-reduction and user-specified rewrites, and solves type constraints via unification.  Synthetic reasoning is achieved by embedding category-theoretic axioms as rewrite rules.  For example, Emdash includes pattern-matching rewrite rules such as `compose_morph (identity_morph X) f ↦ f` and `compose_morph g (identity_morph X) ↦ g` to enforce identity laws.  This makes proofs about categories computational: terms representing categorical constructions automatically normalize according to the axioms.

In summary, Emdash aims to provide a type-theoretic framework where categories and categorical constructions are built into the core calculus.  Its goals are (1) *synthetic category theory* – treating categorical concepts as types and terms – and (2) *dependently-typed guarantees* – ensuring consistency and correctness by type-checking and definitional equality.  The implementation prioritizes clarity and correctness over performance, using well-known techniques (λΠ-elaboration, pattern unification, rewriting) in a TypeScript codebase for experimentation.

## Source Code Review and Analysis

The core implementation resides in **emdash\_v2.ts**, which extends a base λΠ-calculus (dubbed “MyLambdaPi”) with category constructs.  Terms are represented by a TypeScript `Term` object with tags like `Type`, `Var`, `App`, `Lam`, `Pi`, and *Emdash* extensions: `CatTerm`, `ObjTerm`, `HomTerm`, `MkCat_`, `IdentityMorph`, and `ComposeMorph`.  The top of the file declares `// MyLambdaPi with Emdash Phase 1: Core Categories` indicating that this version adds only the Phase-1 primitives (categories, objects, homs, identity, composition).

### Typing and Elaboration

Type inference (`infer`) and checking (`check`) follow a bidirectional design.  For example, in **infer**, a `CatTerm` is simply given type `Type()` (i.e. `Cat : Type`).  An `ObjTerm(C)` requires checking that `C : Cat`; the code does `check(ctx, current.cat, CatTerm(), ...)` then returns `Type()`.  Likewise, `HomTerm(C, X, Y)` checks `C : Cat` and `X,Y : Obj(C)` before returning `Type()`.  These behaviors correspond to the rules in the Lambdapi spec (e.g. “Obj: Cat → Type” and “Hom : Π A\:Cat. Obj A → Obj A → Type”).

When inferring a lambda without an annotation, the code creates a fresh hole for the parameter type and updates the lambda node in-place (`current.paramType = Hole(freshHoleName())`).  This “bug fix” (labeled *Bug Fix #1* in comments) ensures that subsequent processing sees an annotated lambda.  While effective, it is a somewhat hacky in-place mutation of the AST: one would expect inference to avoid mutating user terms.  However, this technique is a practical workaround to propagate a newly guessed type.

The `check` function contains special-case logic for `IdentityMorph` and `ComposeMorph` nodes when the *expected* type is a `HomTerm`.  Normally one would check their inferred type and unify it with the expected type, but here the code *directly adds constraints* on the implicit category and object fields to align with the expected hom type.  For example:

```ts
if (current.tag==='IdentityMorph' && normExpectedType.tag==='HomTerm') {
    addConstraint(idTerm.cat_IMPLICIT!, expHom.cat, `...`);
    addConstraint(idTerm.obj, expHom.dom, `...`);
    addConstraint(idTerm.obj, expHom.cod, `...`);
    // Also ensure `obj : Obj(cat_IMPLICIT)`
    const objActualType = infer(ctx, idTerm.obj, ...);
    addConstraint(objActualType, ObjTerm(idTerm.cat_IMPLICIT!), `...`);
    return;
}
```

This workaround was introduced to solve the difficulty that an identity morphism term (`IdentityMorph`) has implicit arguments (category and object) that must match the expected `HomTerm(cat, dom, cod)`.  The code explicitly constrains these fields before returning, deferring the rest to the constraint solver.  While effective, it is an *ad hoc* solution: ideally the type-checker would uniformly handle implicits, but here the identity/composition case needed a bespoke branch.  (The comment notes it corresponds to “Solution 5” of some design notes.)

### Rewrite and Normalization

Normalization (`whnf`) applies β-reduction and user rewrite rules in a loop.  It first resolves any solved holes (`getTermRef`), then *user-defined rewrite rules*, then *head-specific β-reductions*.  User rules are pattern rules added via `addRewriteRule`.  In Phase 1, two rules implement the identity laws for composition: `ComposeMorph(g, IdentityMorph(X,C), C, X, X, Y) ↦ g` and `ComposeMorph(IdentityMorph(Y,C), f, C, X, Y, Y) ↦ f`.  During WHNF, each rule’s pattern is matched against the term; if it matches and causes a structural change (checked by `areStructurallyEqualNoWhnf`), the term is rewritten to the rule’s RHS.

Head reductions then handle β-reduction and “categorical β-reduction”.  For example, `(App (Lam x => M) N)` reduces to `M[N/x]`.  Crucially, `ObjTerm(C)` reduces to `C.objRepresentation` when `C` is a `MkCat_` term (the “objects” projection), and `HomTerm(C,X,Y)` reduces to `C.homRepresentation(X,Y)` when `C` is a `MkCat_` (the “hom” projection).  Similarly, `ComposeMorph(g,f)` reduces via the category’s `composeImplementation` when all implicits are present.  These reductions correspond to the spec rules (e.g. `@Obj (mkCat_ O H C) ↦ τ O`).

One logical concern is complexity of WHNF and solving: the loop has a large `MAX_WHNF_ITERATIONS` and the solver is iterative and potentially non-terminating in pathological cases.  But for Phase 1 examples, it suffices.

### Unification and Constraints

Emdash collects **constraints** of the form `T1 ≡ T2` during checking and inference, then attempts to solve them by unification in `solveConstraints`.  The solver repeatedly scans the constraint list, using the `unify` function to process each pair.  If terms are already equal (by `areEqual` with WHNF), the constraint is dropped.  Otherwise, `unify` tries to unify holes with terms (`unifyHole` does occurs-check and assignment), and performs *injective unification* for known constructors (`ObjTerm`, `HomTerm`, `MkCat_`, `IdentityMorph`) before resorting to full WHNF and general unification.

The unifier distinguishes `Solved`, `Progress`, `Failed`, and `RewrittenByRule`.  If a unification rule applies (via `tryUnificationRules`), it adds new constraints rather than equating terms immediately.  In Phase 1, no unification rules are defined in user code, so this path isn’t used.  Otherwise, the solver will decompose structures (unifying components) or eventually fail with an error.  The overall solve loop repeats until no constraints change or a failure is reported.

The **definitional equality** check (`areEqual`) compares two terms by normalizing both with WHNF and then recursively checking structure.  For example, two identity morphism terms are equal if their implicit categories and objects match up.  This implements the λΠ-calculus modulo rewriting: two terms that differ by a rewrite rule or β-reduction are considered equal.

### Bugs, Inconsistencies, and Workarounds

* **In-place Lambda Annotation:** As noted, inferring an unannotated `Lam` annotates it with a fresh hole type.  This mutates the AST and could lead to surprising state if reused.  A purer approach would clone or record this, but the code opts for simplicity.

* **Implicit Arguments:** The code manually injects holes for implicit fields (`ensureImplicitsAsHoles`) before type-checking function-like terms.  This is needed because patterns like `IdentityMorph(x)` implicitly require a category.  The approach is consistent but requires many special cases (e.g. in `compose_morph` or `identity_morph` inference).  The special-case in `check` for `IdentityMorph` and `ComposeMorph` (discussed above) is another sign that implicit handling was tricky.

* **Pattern Matching Corner Cases:** The `matchPattern` routine handles matching of pattern variables and concrete terms for rewrite rules.  In complex patterns (e.g. `ComposeMorph`), careful ordering of implicit arguments is needed.  The rewrite rules defined in `setupPhase1GlobalsAndRules` use pattern variables (`X_obj_pv`, etc.), but these must be chosen distinct from any global names.  The comment warns about naming conflicts, but the system does not enforce hygiene, so pattern variables overlapping global names could break matching.

* **Limited Error Checking:** Many error paths simply throw on stack overflow or unbound variable, but user-friendly messages are minimal.  For example, applying a non-function term yields an error: `Cannot apply non-function: ...`.  However, type errors from unsolved constraints just report the remaining constraint (not a precise location in the source).

* **Unification Complexity:** The solver can potentially loop for complex constraints.  The code sets a very high iteration limit and logs warnings if it gets too big.  This might mask deeper issues in type-checking rules or termination guarantees.

* **Missing Cases:** As of Phase 1, several constructs in the Lambdapi spec are not supported.  For instance, while the spec includes a `Functor` type and natural transformations, the code has no corresponding `FunctorTerm` or `TransfTerm` constructors.  This is by design (reserved for Phase 2), but it means code paths that handle functor application and transformation are absent.

Despite these quirks, the implementation is largely coherent: it closely follows expected λΠ-elaboration patterns, uses WHNF and unification in the standard way, and implements rewrite rules idiomatically.  Clever techniques include using pattern-based rewrite and unification rules to encode equations, and the iterative constraint solver to handle dependent pattern unification.  The deviations from a pure design (AST mutation, special-case branches) appear necessary given the prototype nature of the project.

## System Summary

Emdash implements a full elaboration pipeline:

* **Bidirectional Typing:** The `infer` function synthesizes a type for a term, while `check` verifies a term against an expected type.  For variables and constructors (`Var`, `App`, `Pi`, etc.), `infer` follows standard rules: lookup a variable in context, check function and argument in application, etc.  For lambdas, `infer` and `check` coordinate: an annotated lambda is checked against an expected Π-type; an unannotated lambda is given a fresh type hole in `infer`.

* **Hole Filling (Metavariables):** Unknown types or arguments are represented as `Hole` terms.  The system introduces holes for omitted annotations and implicit arguments.  During elaboration, type constraints (`t1 ≡ t2`) involving holes are collected.  After initial check/infer, `solveConstraints` attempts to assign holes consistently via unification.

* **Constraint Solving:** Constraints are solved in a global loop.  Each `t1 ≡ t2` is unified.  The unifier handles:

  * **Hole Unification:** If one side is a hole, `unifyHole` (with occurs-check) assigns the hole to the other term.
  * **Structural Unification:** If both sides are the same injective constructor (like `ObjTerm` or `HomTerm`), their parts are unified recursively.
  * **Normalization-based Unification:** Otherwise, it weakly-normalizes both terms (β+rewrites) and retries.  If equal after normalization, success; if not, attempts to unify subterms or apply unification rules.
  * **Unification Rules:** If pattern-based unification rules are provided, `tryUnificationRules` pattern-matches the terms against left-hand patterns of a rule, then adds the rule’s right-hand *constraints* via `applyAndAddRuleConstraints`.  (In Phase 1, no such rules are defined by the user.)

  The solver iterates until no constraints remain or it detects failure (e.g. a rigid mismatch).

* **Pattern Matching:** Rewrite and unification rules use a `matchPattern(pattern, term, ctx, pvars, subst)` routine.  Pattern variables (declared with a name and type) match any subterm, binding the variable in the substitution.  Wildcards (`_`) are supported.  Matching is structural and recursive: for example, matching a `ComposeMorph` pattern against a term decomposes and matches each component.  Unification rules similarly match two terms in either order.

* **Computation (WHNF & Rewrite):** `whnf(term, ctx)` reduces a term by:

  1. **Resolving Holes:** Replace any hole that has been solved (aliased to another term) via `getTermRef`.
  2. **Rewrite Rules:** Apply any user rewrite rule whose LHS matches the term (when the term head is not a declared constant).  If a rule applies and changes the term, restart WHNF.
  3. **Head Reductions:** Perform built-in β-reductions:

     * `App(Lam x. M, N)` ⇒ `M[N/x]`.
     * `ObjTerm(mkCat_(O,H,C))` ⇒ `O` (object projection).
     * `HomTerm(mkCat_(O,H,C), X, Y)` ⇒ `H X Y` (hom projection).
     * `ComposeMorph(g,f)` with a concrete category simplifies via the category’s `composeImplementation`.
     * `Var(x)` delta-reduces if `x` is a global definition (non-constant) to its body.
  4. **Reiterate:** If any change occurred, repeat.  Otherwise terminate with the WHNF.

* **Definitional Equality:** The function `areEqual(t1,t2)` tests whether two terms are definitionally equal by normalizing both (WHNF) and then doing a structural compare.  It treats holes as unequal (unless identical).  For binders (`Lam`, `Pi`), it uses a fresh variable and recursion to compare bodies.

All these components follow conventional designs found in many dependently-typed systems (e.g. Idris, Agda, or Lambdapi).  The elaboration strategy is standard bidirectional typing with holes and constraints.  The unification approach (try structural then fallback to normalization) is similar to other implementations of higher-order unification for dependent types.  The novel aspect is the integration of user rewrite rules into both normalization and unification (pattern-directed rewriting), mimicking the λΠ-Modulo framework.  Emdash’s `unif_rule` and `rule` mechanisms replicate Lambdapi’s oriented equations, albeit in a simplified, explicit form.

## Comparative Analysis

Emdash’s type theory and algorithms closely mirror those of the **λΠ-calculus Modulo** (Lambdapi/Dedukti) but in a simplified, TS-based setting.  Key points of comparison:

* **Elaboration and Type-Checking:** Like Lambdapi, Emdash uses dependent types with Π-types, λ-abstraction, and universes (`Type:Type`).  The elaboration (`infer`/`check`) is typical of modern implementations.  Unlike full Lambdapi, Emdash does not yet support user-defined implicit argument inference except via holes, nor rich module or pattern features.  Lambdapi allows declaring arguments as implicit and tries to fill them; Emdash simulates this by *forcing* implicit arguments to be holes beforehand.  This is simpler but less flexible.

* **Holes/Metavariables:** Emdash exposes holes (`Hole(id)`) directly and uses them for missing types or terms.  Lambdapi’s core also has metavariables during interactive proof, but Emdash does not have a proof mode; holes are only for implicit terms.  The strategy of collecting constraints and solving them is analogous to unification of metavariables in proof assistants.

* **Rewrite and Conversion:** A major similarity is the use of **user-defined rewrite rules** as part of conversion.  Lambdapi explicitly allows oriented equations (rewrite rules) to define identity and composition laws; Emdash likewise has a list of `userRewriteRules` applied during normalization.  Both systems require ensuring confluence/termination, though Emdash currently trusts user rules to be well-behaved.  Emdash’s `whnf` loop is essentially Lambdapi’s conversion check: it normalizes via β and rules until fixed point.

* **Unification:** Emdash implements a higher-order unification algorithm (with occurs-check) that handles Π-types, λ, etc.  This is comparable to Lambdapi’s unification used for implicit arguments or in proof search.  Unlike Lambdapi’s fully algorithmic approach, Emdash uses an ad-hoc mix of structural unification and rule-driven unification (pattern-based rules can add constraints).  This is somewhat novel: Lambdapi (and underlying Dedukti) typically require confluence of rewrites to ensure decidability of type-checking, whereas Emdash tries unification rules as needed.  In practice, Emdash’s unification is more manual and less guaranteed to terminate.

* **Pattern Matching:** Emdash explicitly implements pattern matching (`matchPattern`) for rewrite/unif rules. Lambdapi’s rewrite rules are pattern-based as well, but handled by the system’s core.  The approach here is similar in spirit.  There is no separate pattern-matching on datatype values as in Agda/Coq; these are only for rule matching.

* **Definitional Equality:** Both systems allow rewriting by user rules.  In Lambdapi, identity rules like `f ∘ id = f` are normally added as rewrite rules.  Emdash does the same, ensuring two terms are considered equal if one rewrites to the other.  The difference is that Emdash inlines some rewrites in the checker (special cases) rather than purely relying on normalization.  For instance, Emdash’s special-case `check` for `IdentityMorph` ensures types align before normalization, whereas Lambdapi would likely defer to the rewrite during normalization.

* **Extensions:** The Lambdapi spec (and implementation) supports far more: inductive types, sophisticated pattern rules, proof tactics, etc..  Emdash so far covers only a tiny fragment: the raw λΠ-kernel plus categories.  Functors and natural transformations are in the **spec file** (the `emdash_specification_lambdapi.lp` describes them) but not in the code.  Thus, Emdash so far *omits* all functorial constructs, which Lambdapi could encode by user rules.

In summary, Emdash essentially re-implements a **minimal Lambdapi-like kernel** with category primitives.  It *simplifies* many aspects (no implicit argument inference, no modules, limited rewriting control) but *mimics* the core ideas: rewriting modulo β, dependent Π-types, and pattern-based rules.  This makes Emdash both similar to established systems (via standard algorithms) and a testbed for category-specific additions.

## Type Theory Specification Summary

The accompanying file *emdash\_specification\_lambdapi.lp* defines the formal kernel of Emdash (in Lambdapi syntax).  It introduces:

* **Universes and Base:** `Type : TYPE` is the universe, with `τ : Type → TYPE` for *interpreting* internal types (a standard Dedukti-style trick).

* **Categories:** A constant `Cat : TYPE` is declared.  An injective symbol `Obj : Cat → TYPE` assigns each category the type of its objects; similarly `Hom : Π (A:Cat) (X:Obj A) (Y:Obj A), TYPE` for morphisms.  Type-correctness rules (not shown in spec but implemented in code) ensure `ObjTerm(C) : Type` and `HomTerm(C,X,Y) : Type` only when well-formed.  The spec also includes helper constants `Obj_Type` and `Hom_Type` mapping to `τ`-encoded types.

* **Category Axioms:** Constants `identity_morph : Π A:Cat, Π X:Obj A, Hom A X X` and `compose_morph : Π A,X,Y,Z:Obj A, Hom A Y Z → Hom A X Y → Hom A X Z` define identities and composition.  Rewrite rules enforce unit laws: composing with an identity on either side reduces to the other morphism.  A constructor `mkCat_` of type `Π (Obj:Type) (Hom:Obj→Obj→Type) (compose_morph:…) → Cat` packages a category from given data.  Projection rules `@Obj (mkCat_ O H C) ↦ τ O` and `@Hom (mkCat_ O H C) X Y ↦ τ (H X Y)` tie this to the `Obj` and `Hom` symbols.  This specification ensures that a `MkCat_` term behaves like a category with the supplied object/hom carriers and composition.

* **Functors:** The spec declares `Functor : Π A:Cat, Π B:Cat, Cat`.  It defines symbols `fapp0` and `fapp1` for object and morphism application of a functor.  Functor laws are given: `fapp1 F (identity X) ↦ identity (fapp0 F X)` and `compose_morph (fapp1 F a') (fapp1 F a) ↦ fapp1 F (compose_morph a' a)`.  A constructor `mkFunctor_` bundles object- and morphism-mapping into a functor, with projection rules for `fapp0` and `fapp1`.  These rules are not yet implemented in code.

* **Natural Transformations:** The spec defines `Transf : Π A B:Cat, Π F G:Obj (Functor A B), TYPE` for natural transformations between functors.  It creates a symbol `tapp` for the component at an object.  Additional rules express the naturality condition: e.g. `fapp1 G a ∘ (tapp ε X) ↦ (tapp ε X') ∘ fapp1 F a` (with appropriate types).  There are also type-level formulas (`naturality_TYPE`) ensuring commutativity of the square, and a wrapper `mkTransf_`.  These details show the intended formal structure of naturality.

* **Yoneda and Set:** Later sections add a `Set : Cat` for a base category of sets/types, together with additional rewrite rules for `Obj Set X ↦ τ X` and `Hom Set X Y ↦ (τ X → τ Y)`, encoding extensional equality.  They define a covariant Yoneda embedding `hom_cov : Π A, Π W:Obj A, Obj (Functor A Set)` and give rewrite rules for the Yoneda action (e.g. `((fapp1 (hom_cov W) a) f) ↦ compose_morph a f`).  These are advanced features hinting at future Phase 2 work (Yoneda functor test is mentioned).

Overall, the specification enumerates *all* the primitive judgments and rewrite rules Emdash should satisfy.  It guides the implementation by listing the constants (`Cat`, `Obj`, `Hom`, `identity_morph`, `compose_morph`, `mkCat_`, etc.) and their computational behavior.  Current limitations (Phase 1) are evident: **functors** and **natural transformations** appear only in the spec, not yet in code.  Similarly, constructs like `hom_cov` are unused by Phase 1.  The spec also includes some Lambdapi-specific machinery (`τ`, `unif_rule` for injectivity) to manage rewriting, which the TypeScript code approximates with pattern matching and unification.  In effect, the spec is a blueprint that the code partially implements for categories, with the rest slated for future phases.

## Phase 1 Problem Retrospective

During Phase 1 development (implementing categories, objects, morphisms), several issues were encountered and addressed:

* **Implicit Arguments and Context Holes:**  Category-theoretic terms (`IdentityMorph`, `ComposeMorph`) have several implicit indices (e.g. the category and intermediate objects). Initially, type inference was unable to fill these automatically.  The solution (coded above) was to **add explicit constraints** on these implicits when checking such terms against an expected `HomTerm`.  This ensures, for example, that in `IdentityMorph(x) : HomTerm(C, x, x)`, the implicit `cat_IMPLICIT` is constrained to `C` and `x` is checked as an object of `C`.  Without this fix, terms like `id(x)` would not typecheck unless all implicits were manually provided.

* **Lam without Annotation:**  In the base λΠ-calculus, writing an unannotated lambda (e.g. `λx. M`) needed a strategy to infer its type.  The code’s approach was to immediately annotate such lambdas with a fresh hole for the parameter type.  This fix (noted in comments as a bug fix) ensures that `infer` can continue processing.  An alternative might have been to delay elaboration, but the in-place annotation was simpler.  The lesson is that letting lambdas introduce holes early avoided missing type information later.

* **Pattern Variable Naming:**  When adding rewrite rules (in `setupPhase1GlobalsAndRules`), care was taken to use pattern-variable names unlikely to clash with global names (e.g. `CAT_pv`, `X_obj_pv`).  If a pattern-variable name duplicates a global variable, `matchPattern` might erroneously treat it as an ordinary variable.  No automated hygiene is in place, so user vigilance was needed.

* **Rewrite Rule Design:**  The first attempt at composition rules required careful handling of the implicit object indices.  The team analyzed the category laws to determine the correct pattern for `ComposeMorph(g, id_X) ↦ g`.  This involved understanding that `id_X` has `dom=id=X` and `cod=id=X`, and aligning `g`’s domain and codomain accordingly.  The detailed comments in `setupPhase1GlobalsAndRules` show this reasoning.  Initially, some candidate rules may have been incorrect (e.g. swapping X/Y), but by explicitly encoding the constraints they arrived at the working forms shown.

* **Constraint Solver Stability:**  Iterative solving sometimes risked diverging (if a rule repeatedly added constraints).  To mitigate, the solver tracks progress and has a high iteration cap.  Although no infinite loop was encountered in tests, the warning infrastructure helps catch non-terminating cases early.

In summary, Phase 1 revealed that handling implicits and rewrite patterns required careful coordination.  The team resolved these by adding targeted constraint-generation logic and by thoroughly testing each categorical construct.  Looking forward, similar issues are expected in Phase 2: functors will introduce their own implicits (`Functor A B` as an implicit argument), and naturality conditions will require new rewrite/unification rules.  Awareness of how we solved Phase 1 (e.g. injecting constraints for expected types) will inform how we tackle functorial equations (e.g. ensuring `fapp0`/`fapp1` indices match expected categories).

## Improvement Possibilities

Several enhancements can improve Emdash:

* **Architectural Refactoring:** The code currently mixes MyLambdaPi core and Emdash extensions in one file.  For maintainability, splitting modules (e.g. a core λΠ module and a CategoryTheory extension) would clarify dependencies.  Making the constraint solver and normalization engine more modular (possibly classes or separate services) would ease understanding.

* **More Declarative Implicit Handling:** Instead of manual hole insertion and special-case checks, a systematic *implicit argument mechanism* could be implemented.  For example, declaration of `IdentityMorph` could mark its first argument as implicit, and the type-checker would auto-insert a hole and equate it to the expected category.  This mirrors Lambdapi’s implicit argument feature.  A unified treatment would eliminate some of the hacky branches in `check`.

* **Enhanced Unification Rules:** The spec’s `unif_rule` constructs (see e.g. Yoneda lines in spec) suggest more general unification rules might be needed.  Right now Emdash has no user unification rules in Phase 1.  For Phase 2, to support something like functor extensionality or naturality, it may be useful to define custom unification constraints.  Making a mini-language for these could avoid embedding complex logic in the solver.

* **Error Reporting and Debugging:** Add richer error messages and optional verbose tracing (beyond `console.log`).  For unsolved constraints, pointing to the location in the original term would be helpful.  A flag to visualize the constraint graph or the final substitution would aid debugging.

* **Test Coverage:** Current tests cover basic category constructs and a few rewrite laws.  More examples could include:

  * *Categorical constructions:* e.g. terminal object, binary products or coproducts encoded as `MkCat_` of specific types.
  * *Adjunctions:* define functors $F: A→B$ and $G: B→A$ and check the unit/counit type equalities (once functors are implemented).
  * *Extra laws:* Check that composition is associative (though that would need an additional rewrite rule or proof).
  * *Error cases:* assert that invalid compositions or mismatched types produce errors.

* **Documentation:** The code is lightly commented, but a user guide would help.  Specifically, documenting the correspondence to the spec (e.g. “`CatTerm()` in code is the constant `Cat : Type` in spec”), and explaining design decisions (e.g. why special-case check for `IdentityMorph`) would clarify intent.  Diagrams (perhaps using Mermaid) showing the elaboration pipeline or data flow would also be useful.

* **Example Programs:** The system would benefit from built-in examples illustrating its use.  For instance, encode a small concrete category (like the natural numbers as a category with paths) and show object and hom manipulations.  Implement the `super_yoneda_functor_1` from the spec: once functors exist, define the Yoneda functor $\mathrm{Yoneda}_W = \hom(-,W)$ and check its type and action on morphisms.  Other categorical examples (such as the product category of two categories) would both test and demonstrate Emdash’s capabilities.

## Development Roadmap (Phase 2: Functors & Natural Transformations)

Phase 2 will extend Emdash to handle **functors** and **natural transformations**, guided by the Lambdapi spec and examples like *super\_yoneda\_functor\_1*.  Concrete steps include:

1. **Functor Representation:** Introduce terms for functors.  In the spec, `Functor A B : Cat` and objects of type `Functor A B` are functors from A to B.  In code, we could add a new tag (e.g. `FunctorTerm`) or treat functor types as global constants.  We must allow terms corresponding to `mkFunctor_`, so either implement `MkFunctor_` as a term with fields `(fapp0,fapp1)` similar to `MkCat_`, or else rely on global definitions.

2. **Typing Rules for Functors:** Extend `infer`/`check`:

   * If a term `MkFunctor_(f0,f1)` is given, check that `f0 : Obj A → Obj B` and `f1 : Π X Y (Hom A X Y) → Hom B (f0 X) (f0 Y)`, and that they satisfy functoriality (identities and composition).  We might initially skip checking the laws (they will be enforced by rewrites).  The inferred type should be `Functor A B`.
   * For applying a functor `F : Obj (Functor A B)`, implement `fapp0 F X` and `fapp1 F (f : Hom A X Y)` constructs.  These correspond to applying the object- and morphism-mapping of the functor.  We might encode them as special term forms (like `App(App(Var("fapp0"), F), X)` in the spec).
   * Implicit arguments: Likely `fapp1` will need implicit A,B,F,X,Y inference, similar to how `IdentityMorph` had implicits.

3. **Normalization/Rewrite for Functors:** Add rules analogous to the spec:

   * `fapp0 (mkFunctor_ f0 f1) ↦ f0` and `fapp1 (mkFunctor_ f0 f1) ↦ f1`.  This allows normalization of functor application.
   * Identity and composition laws: e.g., when the functor is applied to an identity or to a composite morphism, normalize using `f1`.
   * For example, a head-reduction in `whnf` could check if `fapp1(F,id)` and `fapp1(F,compose)` and reduce accordingly.  Or simpler, rely on the user rewrite rules (as in spec rules for `fapp1 F (identity X)` and `compose_morph (fapp1 F a') (fapp1 F a) ↦ fapp1 F (compose_morph a' a)`).
   * Add these as `addRewriteRule` in `setupPhase2GlobalsAndRules()`.

4. **Natural Transformations:** Introduce a term tag for natural transformations, perhaps `TransfTerm(F,G,eta)` where `eta` is the component.  The spec uses a constant `Transf F G : TYPE` and `tapp ε X : Hom B (F X) (G X)`.  We can mirror this:

   * Define `TransfTerm(F,G,eta)` whose expected type is something like `Transf F G`.
   * During checking, if given an expected type of `Transf F G`, ensure `eta` is a function with type `Π X:Obj A, Hom B (fapp0 F X) (fapp0 G X)` and that it satisfies naturality.
   * Or simpler: treat a `Transf` as packaging a family of morphisms with appropriate type.  The component `eta(X)` could be a function from `Obj A` to homs.
   * Natural transformation equations (naturality squares) can be encoded as rewrite or unification rules.  The spec shows rules to enforce `(G a) ∘ (ε X) ↦ (ε X') ∘ (F a)`.  We would add these in normalization.

5. **Hole and Implicit Handling:** Expect many implicits: in `fapp1` rules, the category `A` and functor `F,G` may be implicit.  We will likely need code, as in Phase 1, to insert holes or constraints for missing implicits when checking functor or transf terms.

6. **Testing with Examples:** The `super_yoneda_functor_1` example from Phase 2 presumably involves the Yoneda functor.  Steps:

   * Define the category of sets `Set` (already in spec) as a `CatTerm`.
   * Define `hom_cov A W` for some object `W` in a category `A`.
   * The functor `hom_cov W` maps `X` to `Hom(A, X, W)`.  The example likely checks that `ComposeMorph` rewrite and `fapp1/hom_cov` rules interact to show that applying a morphism `(f : Hom(X,Y))` corresponds to pre-composition in the hom-set.
   * Implement the rules from spec: e.g. in code, `addUnificationRule` or rewrite for `(fapp1 (hom_cov W) a) f ≡ compose_morph a f`.  (Spec uses an “unif\_rule”, but in code we might approximate with a rewrite rule `ComposeMorph(f,f')` or direct pattern.)

7. **Roadmap Prioritization:**

   * **Step 1:** Extend the term language and context with `FunctorTerm` and `TransfTerm` (or analogous constructs).  Ensure the context recognizes `Var("Functor")` or introduce built-in Functor in code.
   * **Step 2:** Implement infer/check for functors: check that `MkFunctor_(f0,f1)` produces `Functor A B`.  Handle `fapp0` and `fapp1` applications similarly to `ObjTerm` and `HomTerm`.
   * **Step 3:** Add rewrite rules in `setupPhase2GlobalsAndRules()` for functor projection and for naturality.  Include `ComposeMorph` interaction if needed.
   * **Step 4:** Test simple functor examples: identity functor, composition of functors, and verify their laws.  Then test Yoneda: define `hom_cov` as a special functor, check that `fapp1 (hom_cov W) (compose a b)` rewrites correctly.
   * **Step 5:** Add natural transformation syntax: maybe as a function `tapp(ε, X)` or as a term.  Test with an example: e.g. if there is a trivial natural transformation (identity), check that its type is `Transf F F`.

In writing this plan, we align closely with the Lambdapi spec (the “basic kernel specification”).  We will effectively implement the clauses from *emdash\_specification\_lambdapi.lp* for functors and transformations in TypeScript code.  Correctness and coherence with the theory are more important than performance: each rule or check should faithfully reflect the formal rules (e.g. those given by the spec or by category theory).

```mermaid
flowchart TD
  A[Input Term] --> B{Elaborator}
  B -->|Infer| C(Inferred Type, Constraints)
  B -->|Check| C
  C --> D{Constraint Solver (Unification)}
  D --> E[NHoles Filled, Types Equalized]
  E --> F[NF/WHNF]
  F --> G[Elaborated Term & Type]
```

*Figure: Overview of the elaboration and normalization workflow in Emdash.*
