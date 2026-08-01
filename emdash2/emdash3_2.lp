/*
  m- / emdash3.2
  Directed-family mixed-variance v3.2 migration draft.

  This file began as a fork of the retired v3.1 baseline.  It is now the active
  v3.2 development; the v3.1 file and original HOM/FAM/PI/CONST plan are
  archived historical baselines rather than current design authorities.  This file uses
  directed Cat-valued families directly:

    Functor_cat K Cat_cat ↪ Catd_cat K.

  Canonical surface syntax authority:
    reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md

  Current surface-notation summary:
    A ⊢ B                         = Functor_cat A B
    z :^n Z ; E[z] ⊢ D[z]         = Functord_cat E D
    Π (z :^n Z), D[z]             = Pi_cat D
    a ->^C b                      = Hom_cat C a b
    aa[z^-] ->_[z]^R bb[z]        = Hom_catd R aa bb
    A[z^-] ⊢_[z] B[z]             = Functor_catd A B
    F => G                        = Transf_cat F G
    FF[z^-] =>_[z] GG[z]          = Transf_catd A B FF GG

  Diagnostic `assert` checks live in emdash3_2_checks.lp.

  Table of contents / source section map:

    0. Groupoid universe and equality
    1. Encoded Sigma types for object layers
      1a. Encoded dependent pairs, projections, and Sigma path views
      1b. Minimal groupoid-level dependent products and type equivalences
    2. Core categories
    3. Functor, displayed-family, and universe categories
      3a. Ordinary functor classifier and action
      3b. Ordinary categorical isomorphism evidence
      3c. Universe categories
      3d. Directed-family and displayed-arrow classifiers
      3e. Ordinary identity, composition, opposite, terminal, and constant functors
      3f. Internalized universe-level constructor packages
    4. Ordinary internal hom and hom actions
      4a. Covariant represented hom families and postcomposition action
      4b. Computational isomorphisms under the represented hom-action owner
      4c. Contravariant represented hom families and precomposition action
      4d. Internalized source/target endpoints and variance comparison
    5. Ordinary binary products of categories
      5a. Product categories, projections, and paired functors
      5b. Product symmetry, identities, and composition
      5c. Product and uncurried composition action
      5d. Rigid two-endpoint Hom action
      5e. Product closure for ordinary isomorphism evidence
      5f. Product-pair telescope declaration
    6. Ordinary transformations and functor composition actions
      6a. Transformation classifier, components, and generic projection calculus
      6b. Internalized hom endpoint actions and rigid two-sided projections
      6c. Constant/opposite transfors and Cat-valued composition projections
      6d. Full ordinary naturality and projection-order joins
    7. Product functor packages, evaluation, curry, and ordinary internal action
      7a. Internalized product formation and product maps
      7b. Evaluation and fixed-object evaluation
      7c. Ordinary curry and uncurry
      7d. Adjunctions and opposite adjunctions
      7e. Internal ordinary hom-action packages
    8. Directed Cat-valued family constructors
      8a. Fibre notation, pullback, and base-arrow transport
      8b. Constant, terminal, opposite, and displayed composition
      8c. Section categories and Pi action
      8d. Fibre covariance and dependent-hom endpoint notation
    9. Directed Sigma categories and maps between totals
      9a. Sigma totals, Sigma homs, and projection
      9b. Sigma maps and canonical transport arrows
      9c. Families over Sigma totals and displayed-transfor uncurrying
    10. Mixed-variance family functor
    11. Representables and presheaf-family classifiers
      11a. Representables
      11b. Opposite-edge and presheaf classifiers
    12. Directed homd target and internal homd functor
    13. Dependent-hom projections and covariant fibre transport
    14. Section action over dependent homs
    15. Internal displayed hom-action heads
    16. Displayed components, displayed hom-action, and laxity extraction
      16a. Fibre-level displayed components
      16b. Identity-specialized displayed hom action and Sigma-map action
      16c. Section action and displayed laxity cells
      16d. Arbitrary displayed-transfor hom-action projections
      16e. Strict/cartesian and terminal-source specializations
    17. Generic Sigma/Pi weakening, ordinary structural logic, and delayed projection helpers
      17a. Generic Sigma/Pi introduction and evaluation
      17b. Constant sections and delayed product-pair telescope rules
      17c. Ordinary functor structural logic
      17d. Generic ordinary functor hom-action
      17e. Section pullback and internal Pi action
      17f. Reusable contextual curry basis
      17g. Variance-correct mixed displayed curry
    18. Cat-valued profunctors
      18a. Fixed-endpoint profunctor category and vertical maps
      18b. Opposite profunctors and fixed-endpoint duality
      18c. Endpoint reindexing and product-base action
      18d. Unit hom profunctor and readable representables
      18e. Computational comparison as the profunctor-facing DefIso view
      18f. Shaped profunctor cells and endpoint-changing application
      18g. Internalized reindexing and equipment-style cell composition
      18h. Tensor, shaped introduction, and fixed-endpoint co-Yoneda maps
      18i. Covariant/contravariant implication and vertical closed cores
      18j. Weighted representability and adjunction-mate preservation
      18k. Directed-inductive join and internally natural cross arrows
      18z. Late cross-section normalization bridges
    19. Applications: PathOut, path induction, and transitivity
      19a. Outgoing-path categories and fixed-source path induction
      19b. PathOut motives and fixed-source path induction
      19c. Sigma-total presentation of path induction
      19d. Transitivity benchmark
      19e. Path-induction target transport aliases
      19f. Nested telescope stress examples
      19g. Eckmann-Hilton first computation slice
    20. Equality-local category skeleton and restricted Core inclusion

  Grouped architecture map:
    - Kernel foundations: 0-3.
    - Ordinary category calculus: 4-7.
    - Directed-family and displayed calculus: 8-17.
    - Profunctor, equipment, and DefIso migration machinery: 18.
    - Applications: 19-20.

  The generated reviewer-facing diagnostic map is
  reports/REPORT_EMDASH_CHECK_CATALOG.md; executable checks remain in
  emdash3_2_checks.lp.
*/

flag "eta_equality" on;
flag "print_implicits" on;
flag "print_contexts" on;
flag "print_domains" on;
flag "print_meta_args" on;

/*
  Active kernel working conventions

  This file is intentionally kernel-like: primitives stay small, and
  computational behavior is made explicit by rewrite and unification rules.
  Comments should name the categorical intent, but rules should stay close to
  the stable heads actually used by Lambdapi.

  Surface reading for this directed-family draft:
    - `E[x]` means `Fibre_cat E x`, for `E : Catd Z`.
    - `F[x]` means `fapp0 F x`, for an ordinary functor.
    - `ϵ[x]` means the diagonal component extracted by `tapp0_fapp0 x ϵ`.
    - `homd_int FF`, for `FF : Functord D E`, follows
      `homd_src_func`, `homd_src_sec`, `homd_tgt_func`, then `homd_`.

  Rewrite hygiene:
    - Lambdapi rule LHSs are matched and typechecked modulo conversion.
      Over-specifying inferred/implicit arguments can force expensive
      conversion problems, or make a rule fail to match after the inferred term
      reduces to a canonical expression.
    - Keep inferred/implicit arguments on rule LHSs as `_` unless they are
      essential discriminators.
    - In particular, do not spell defined aliases or reducible compound
      expressions in implicit LHS slots just because the rule typechecks.
      Such a rule can be accepted but later fail to fire when Lambdapi infers
      the same slot through a different normal form. Match on the stable head
      or explicit data argument instead, and let typing/unification recover
      the implicit endpoint.
    - If there are multiple inferred arguments in a nested expression, check
      all of them.  Omitting only one brittle argument is often not enough.
    - Be especially cautious when an implicit argument contains a reducible
      subterm such as `fapp0 F x`, `comp_cat_fapp0 F G`, `Functor_catd ...`,
      `HomPresheaf_catd_func ...`, or `Homd_target_catd ...`, or a compound
      canonical expression such as `Op_cat (Hom_cat ...)`.
    - When an explicit source/target category slot is needed for an assertion
      or rule, prefer the canonical normal form (`Hom_cat ...`,
      `Functord_cat ...`) over a reducible readability wrapper such as
      `Fibre_cat (DefinedAlias ...) k`.  The wrapper may compute in isolation
      but still make conversion search brittle in nested `fapp0` slots.
    - Prefer small projection rules with stable heads over one large nested
      redex. The homd projection path is split into `tapp0_fapp0` and `fapp0`
      folds; surface `piapp0` notation unfolds through `tapp0_fapp0`.
    - Prefer semantic definitions first.  Add a primitive/stable head only
      when a focused probe shows a real discrimination or performance need.
      If the issue is a missing projection rule (for example capped
      `fapp1_fapp0` for a constructor that already has `fapp1_func`), add that
      smaller projection instead of replacing the semantic definition.
    - Cat-specialized semantic heads package extra structure exposed only when
      the ambient category is `Cat_cat`. A generic hom-action arrow may have a
      Cat-specialized transfor normal form where `tapp0_fapp0`, `tapp1_func`,
      and `tapp1_fapp0` become valid projection surfaces. Keep such heads when
      they make the projection ladder stable, but document their generic owner
      and any overlap/join with it.
    - Do not duplicate a semantic body in helper aliases.  Define readable
      aliases through the named semantic constructor so later corrections have
      one source of truth.
    - Probe nontrivial rules in a temporary copy first, with a bounded
      `lambdapi check` and a focused assertion for the expected normal form. A
      rule that typechecks but fails or times out on its intended assertion is
      not ready for this file.
    - During probes and debugging, explicit implicit arguments are useful:
      they make inferred categories, endpoints, and family indices visible in
      error messages. After the rule is stable, prefer the minimal form that
      still typechecks quickly and still matches the intended normal forms.
    - To audit whether an existing rule is still used, first search for likely
      downstream redexes and normal forms, then remove only that rule in a
      temporary copy and run a bounded check. Treat the first failing
      rule/assertion as the concrete dependency to document before deleting the
      temporary file.

  Stable heads and unification helpers:
    - Stable heads are the intended normal forms for operations that later
      rules need to recognize (`comp_cat_fapp0`, `tapp0_fapp0`,
      `homd_src_func`, `homd_src_sec`, `homd_tgt_func`).
    - Classifier wrappers such as `Hom`, `Functor`, `Catd`, `Functord`,
      `Transf`, and `Transfd` are injective heads.  This replaces direct
      wrapper-level unification rules.
    - Controlled `Obj`-inversion unification rules for chosen category heads
      (`Hom_cat`, `Functor_cat`, `Catd_cat`, `Functord_cat`, `Transf_cat`,
      `Transfd_cat`) are elaboration aids.  They are not semantic
      claims that `Obj` is globally injective. Avoid adding this style of rule
      for notation-only heads such as `Fibre_cat`: equality of fibre object
      categories should not force equality of the whole family and base index.
    - If a concrete constructor does not reduce early enough and needs one of
      these unification helpers, that is usually a signal to add a computation
      rule or introduce a smaller stable head.
    - A term already typed as `Functor` or `Transf` inherits identity,
      composition, and naturality from the global `fapp*`/`tapp*` calculus.
      Do not restate those laws on a constructor-specific action head. If a
      named action appears to need such rules, add or expose the more
      internalized functor/transfor owner and make the readable action a
      projection or semantic view of that owner. Concept-specific beta/eta or
      cut-elimination rules remain appropriate when they express additional
      structure rather than ordinary functoriality.

  Omega-friendly normalization:
    - Prefer functor-level folds over capped pointwise rewrites when the result
      must remain iterable to higher cells.  A rule whose RHS is just
      `fapp0 (...) cell` computes one selected cell but can lose the functor
      object that would support another hom-action.
    - Treat formulas such as `E[x] = ...` as object laws only. If `x` varies
      in a category, also identify the action over `p : x ->^C y` before turning
      the formula into a constructor, stable head, or rewrite rule. The same
      applies to transfor sketches: `eta[x] = ...` is only the component law
      until `eta[p]` / `tapp1_func eta` is specified or explicitly deferred.
      Capped projections such as `tapp1_fapp0`, or constructor-specific
      `*_tapp1_*` helpers, may be the practical assertion surface, but they do
      not replace the need to account for the full arrow action. If a later
      consumer needs functorial action in a family argument, keep that as a
      separate design/probe item too.
    - Use pointwise endpoint notation only when the current construction
      genuinely needs an endpoint. Here `homd_` is defined by the semantic
      `hom_con` endpoint; internal rules should discriminate on `homd_int`.

  Naming conventions:
    - Categories use uppercase letters (`A B C K Z`), with `Z` often the base.
    - Directed Cat-valued families use `E D A B` depending on variance; fibre
      objects are usually lowercase `u v`.
    - Ordinary functors use `F G`; transfors use Greek names such as `ϵ η`.
    - Projection/application heads follow the v2 pattern:
      `fapp*` for ordinary functors, `tapp*` for transfors, `piapp0` for a
      section of a `Pi_cat`, and `homd_*` for the dependent-hom projection
      pipeline.
*/

// -------------------------------------------------------------------------------------------------
// 0. Groupoid universe and equality
// -------------------------------------------------------------------------------------------------

/*
  Core object/type universe.

  Surface/formula:
    a : Grpd       is a small groupoidal/type-like object classifier.
    τ a            is the ambient Lambdapi type of elements of a.
    Prop/P         are mapped to Grpd/τ for Lambdapi's inductive interface.
*/
// Universe of small groupoidal/type-like classifiers.
constant symbol Grpd : TYPE;

// Decode a groupoid classifier to its ambient Lambdapi type of elements.
injective symbol τ : Grpd → TYPE;
builtin "T" ≔ τ;
builtin "Prop" ≔ Grpd;
builtin "P" ≔ τ;

/*
  Equality in the groupoid universe.

  Surface/formula:
    x = y          is equality/path type in a groupoid a.
    eq_refl x      is the reflexive path.
    ind_eq p P u   transports u : P y backwards along p : x = y.
    eq_trans p q   composes paths p : x = y and q : y = z.
*/
injective symbol = : Π [a: Grpd], τ a → τ a → Grpd;
notation = infix 10;

// Reflexive path `refl_x : x = x`.
injective symbol eq_refl : Π [a: Grpd], Π x: τ a, τ (x = x);

// Right-based dependent path induction. This supplies the path-dependent
// eliminator needed for contractible identity fibres without assuming UIP.
symbol ind_eqr
  [a : Grpd]
  [y : τ a]
  (P : Π x : τ a, τ (x = y) → Grpd)
  (u : τ (P y (eq_refl y)))
  [x : τ a]
  (p : τ (x = y))
  : τ (P x p);

// Path-induction beta: eliminating reflexivity returns the supplied motive.
// The explicit category and repeated endpoint are subject-reduction guards:
// observational classifiers can otherwise make a foreign `eq_refl` proof
// inhabit the same decoded classifier without identifying its proof index.
rule @ind_eqr $a $y _ $u $y (@eq_refl $a $y) ↪ $u;

// Equality eliminator/transport, derived as the path-independent specialization
// of right-based dependent path induction.
symbol ind_eq : Π [a: Grpd], Π [x: τ a], Π [y: τ a],
  τ (x = y) → Π p: (τ a → Grpd), τ (p y) → τ (p x)
≔ λ a x y p P u,
  @ind_eqr a y
    (λ t : τ a, λ _ : τ (t = y), P t)
    u
    x
    p;

// Equality/path transitivity.
symbol eq_trans : Π [a : Grpd], Π [x : τ a], Π [y : τ a], Π [z : τ a],
  τ (x = y) → τ (y = z) → τ (x = z)
≔ λ a x y z p q, ind_eq p (λ t : τ a, t = z) q;

// Path symmetry: `p : x = y` gives `p^-1 : y = x`.
symbol eq_sym
  [a : Grpd]
  [x y : τ a]
  (p : τ (x = y))
  : τ (y = x)
≔ ind_eq p
    (λ t : τ a, y = t)
    (eq_refl y);

// Nondependent action on paths: `ap(f,p) : f(x) = f(y)`.
symbol eq_ap
  [a b : Grpd]
  (f : τ a → τ b)
  [x y : τ a]
  (p : τ (x = y))
  : τ (f x = f y)
≔ ind_eq p
    (λ t : τ a, f t = f y)
    (eq_refl (f y));

// Heterogeneous path over an equality/path in a family of groupoids. The
// semantic definition uses the kernel's backward equality transport; public
// constructor path views should hide this orientation behind stable heads.
symbol PathOver
  [A : Grpd]
  (P : τ A → Grpd)
  [x y : τ A]
  (p : τ (x = y))
  (u : τ (P x))
  (v : τ (P y))
  : Grpd
≔ u = ind_eq p P v;

// Reflexive dependent path over `refl_x`.
symbol pathover_refl
  [A : Grpd]
  [P : τ A → Grpd]
  [x : τ A]
  (u : τ (P x))
  : τ (@PathOver A P x x (eq_refl x) u u)
≔ eq_refl u;

// Dependent action on paths, derived from right-based path induction.
symbol eq_apd
  [A : Grpd]
  [P : τ A → Grpd]
  (f : Π x : τ A, τ (P x))
  [x y : τ A]
  (p : τ (x = y))
  : τ (@PathOver A P x y p (f x) (f y))
≔ @ind_eqr A y
    (λ x : τ A, λ p : τ (x = y),
      @PathOver A P x y p (f x) (f y))
    (eq_refl (f y))
    x
    p;

builtin "eq"    ≔ =;
builtin "refl"  ≔ eq_refl;
builtin "eqind" ≔ ind_eq;

/*
  Elementary decoded H0 formers.

  The native carriers live in Lambdapi `TYPE`; `*_grpd` classifiers expose
  them through the active `Grpd`/`τ` universe. Their eliminator facades route
  through Lambdapi's generated induction principles. This layer supplies
  formation, introduction, dependent elimination, and constructor beta only;
  observational identity/no-confusion, higher action, canonicity, and
  categorical universal properties are separate obligations.
*/
// Native empty carrier.
inductive empty : TYPE ≔;

// Groupoid classifier whose decoded type is empty.
constant symbol Empty_grpd : Grpd;

// Decoding beta for the empty classifier.
rule τ Empty_grpd ↪ empty;

// Dependent empty elimination, routed through the generated recursor.
symbol empty_elim
  (P : τ Empty_grpd → Grpd)
  (x : τ Empty_grpd)
  : τ (P x)
≔ ind_empty P x;

// Native one-element carrier.
inductive unit : TYPE ≔ | tt : unit;

// Groupoid classifier whose decoded type is the one-element type `unit`.
constant symbol Unit_grpd : Grpd;

// Decoding beta for the unit classifier.
rule τ Unit_grpd ↪ unit;

/*
  Visible-constructor observational equality for Unit.

  The closed constructor path exposes `Unit_grpd`, while open endpoints retain
  primitive equality. Generic `eq_refl` remains the proof normal form; merely
  reducing its classifier does not erase proof provenance to native `tt`.
*/
rule @= Unit_grpd tt tt ↪ Unit_grpd;

// Native Boolean carrier.
inductive bool : TYPE ≔
| false : bool
| true : bool;

// Groupoid classifier whose decoded type is Boolean.
constant symbol Bool_grpd : Grpd;

// Decoding beta for the Boolean classifier.
rule τ Bool_grpd ↪ bool;

/*
  Visible-constructor observational equality for Boolean values.

  Same-constructor paths expose the unit classifier and cross-constructor
  paths expose the empty classifier. Open Boolean endpoints retain primitive
  equality. Generic `eq_refl` remains the reflexivity normal form: reducing
  the classifier to `Unit_grpd` does not erase proof provenance to the native
  singleton constructor `tt`.
*/
rule @= Bool_grpd false false ↪ Unit_grpd
with @= Bool_grpd false true  ↪ Empty_grpd
with @= Bool_grpd true  false ↪ Empty_grpd
with @= Bool_grpd true  true  ↪ Unit_grpd;

// Dependent Boolean elimination, routed through the generated recursor.
symbol bool_elim
  (P : τ Bool_grpd → Grpd)
  (u_false : τ (P false))
  (u_true : τ (P true))
  (b : τ Bool_grpd)
  : τ (P b)
≔ ind_bool P u_false u_true b;

// Native natural-number carrier.
inductive nat : TYPE ≔
| zero : nat
| succ : nat → nat;

// Groupoid classifier whose decoded type is the native natural-number carrier.
constant symbol Nat_grpd : Grpd;

// Decoding beta for the natural-number classifier.
rule τ Nat_grpd ↪ nat;

/*
  Visible-constructor observational equality for natural numbers.

  Zero/successor discrimination exposes Unit or Empty, while successor paths
  recurse to predecessor equality. Generic `eq_refl` retains proof provenance:
  neither zero reflexivity nor successor reflexivity collapses to a proof of
  the reduced classifier.
*/
rule @= Nat_grpd zero zero ↪ Unit_grpd
with @= Nat_grpd zero (succ _) ↪ Empty_grpd
with @= Nat_grpd (succ _) zero ↪ Empty_grpd
with @= Nat_grpd (succ $n) (succ $m) ↪ @= Nat_grpd $n $m;

/*
  Former-specific right-based induction for successor paths.

  The public proof is indexed by `succ m = succ n`, while the active Nat
  classifier exposes exactly `m = n`. Routing that exposed proof through the
  generic `ind_eqr` owner gives a sound beta on component reflexivity without
  adding a generic-J rule, proof-time equation, or fibrancy axiom. Outer
  successor reflexivity remains a distinct form.
*/
symbol nat_succ_ind_eqr
  [n : τ Nat_grpd]
  (P : Π m : τ Nat_grpd,
    τ (@= Nat_grpd (succ m) (succ n)) → Grpd)
  (u : τ (P n (@eq_refl Nat_grpd n)))
  [m : τ Nat_grpd]
  (p : τ (@= Nat_grpd (succ m) (succ n)))
  : τ (P m p)
≔ @ind_eqr
    Nat_grpd
    n
    (λ m : τ Nat_grpd, λ p : τ (@= Nat_grpd m n), P m p)
    u
    m
    p;

// Dependent natural-number elimination, routed through the generated recursor.
symbol nat_elim
  (P : τ Nat_grpd → Grpd)
  (u_zero : τ (P zero))
  (u_succ : Π n : τ Nat_grpd, τ (P n) → τ (P (succ n)))
  (n : τ Nat_grpd)
  : τ (P n)
≔ ind_nat P u_zero u_succ n;

/*
  Canonical finite dependent-record representative.

  `PathRecord_grpd(A)` packages `src,dst : A` and a dependent field
  `witness : src = dst`. The native carrier is a parametrized one-constructor
  inductive, while the public projections and eliminator retain the decoded
  classifier in their signatures. Constructor/projection/eliminator beta is
  active; record eta and observational record equality are deliberately not.
*/
(A : Grpd) inductive PathRecordData : TYPE ≔
| Struct_path_record
    (src dst : τ A)
    (witness : τ (src = dst))
    : PathRecordData A;

// Decoded classifier for the named dependent path record.
constant symbol PathRecord_grpd (A : Grpd) : Grpd;

// Decoding beta for the path-record classifier.
rule τ (PathRecord_grpd $A) ↪ PathRecordData $A;

// Named source projection.
symbol path_record_src
  [A : Grpd]
  (r : τ (PathRecord_grpd A))
  : τ A;

// Source-projection constructor beta.
rule path_record_src
  (@Struct_path_record _ $src _ _)
  ↪ $src;

// Named target projection.
symbol path_record_dst
  [A : Grpd]
  (r : τ (PathRecord_grpd A))
  : τ A;

// Target-projection constructor beta.
rule path_record_dst
  (@Struct_path_record _ _ $dst _)
  ↪ $dst;

// Dependent witness projection `src(r) = dst(r)`.
symbol path_record_witness
  [A : Grpd]
  (r : τ (PathRecord_grpd A))
  : τ (path_record_src r = path_record_dst r);

// Witness-projection constructor beta.
rule path_record_witness
  (@Struct_path_record _ _ _ $witness)
  ↪ $witness;

// Reviewed dependent eliminator facade over the generated record induction.
symbol path_record_ind
  [A : Grpd]
  (Q : τ (PathRecord_grpd A) → Grpd)
  (c : Π (src dst : τ A),
       Π witness : τ (src = dst),
       τ (Q (@Struct_path_record A src dst witness)))
  (r : τ (PathRecord_grpd A))
  : τ (Q r)
≔ @ind_PathRecordData A Q c r;

// -------------------------------------------------------------------------------------------------
// 1. Encoded Sigma types for object layers
// -------------------------------------------------------------------------------------------------

// 1a. Encoded dependent pairs, projections, and Sigma path views

// Decoded dependent-pair representation for the groupoid code `Σ_ P`.
inductive τΣ_ [a : Grpd] (P : τ a → Grpd) : TYPE ≔
| Struct_sigma [a P] : Π (sigma_Fst : τ a) (sigma_Snd : τ (P sigma_Fst)), @τΣ_ a P;
notation τΣ_ quantifier;

/*
  Encoded dependent pair type used for object-level Sigma data.

  Surface/formula:
    Σ x : a, P(x)
    Struct_sigma x u = (x,u)
    sigma_Fst(x,u)   = x
    sigma_Snd(x,u)   = u
*/
constant symbol Σ_ [a : Grpd] (P : τ a → Grpd) : Grpd;
notation Σ_ quantifier;

// Decoding beta: elements of `Σ_ P` are encoded dependent pairs.
rule τ (Σ_ $P) ↪ τΣ_ $P;

// First projection of an encoded dependent pair.
injective symbol sigma_Fst [a P] (s : @τΣ_ a P) : τ a;

// First-projection beta: `fst(x,u) = x`.
rule sigma_Fst (Struct_sigma $1 _) ↪ $1;

// Second projection of an encoded dependent pair.
injective symbol sigma_Snd [a P] (s : @τΣ_ a P) : τ (P (sigma_Fst s));

// Second-projection beta: `snd(x,u) = u`.
rule sigma_Snd (Struct_sigma _ $2) ↪ $2;

// Fixed-parameter eliminator for encoded Sigma objects. The generated
// `ind_τΣ_` is fully parameter-polymorphic; this wrapper is the stable local
// eliminator used by low-level groupoid equivalence proofs.
symbol sigma_ind
  [A : Grpd]
  [P : τ A → Grpd]
  (Q : @τΣ_ A P → Grpd)
  (c : Π x : τ A, Π u : τ (P x), τ (Q (@Struct_sigma A P x u)))
  (s : @τΣ_ A P)
  : τ (Q s);

// Sigma elimination beta: the constructor branch receives both components.
rule sigma_ind _ $c (Struct_sigma $x $u) ↪ $c $x $u;

// Observational path view for encoded Sigma objects. A path between dependent
// pairs is observed as a base path plus a dependent path over that base path.
symbol SigmaPathView
  [A : Grpd]
  (P : τ A → Grpd)
  (u v : @τΣ_ A P)
  : Grpd
≔ `Σ_ p : τ (sigma_Fst u = sigma_Fst v),
   @PathOver A P (sigma_Fst u) (sigma_Fst v) p (sigma_Snd u) (sigma_Snd v);

// Base-path projection of a Sigma path view.
symbol sigma_path_base
  [A : Grpd]
  [P : τ A → Grpd]
  [u v : @τΣ_ A P]
  (w : τ (@SigmaPathView A P u v))
  : τ (sigma_Fst u = sigma_Fst v)
≔ sigma_Fst w;

// Dependent fibre-path projection over `sigma_path_base`.
symbol sigma_path_fibre
  [A : Grpd]
  [P : τ A → Grpd]
  [u v : @τΣ_ A P]
  (w : τ (@SigmaPathView A P u v))
  : τ (@PathOver A P
      (sigma_Fst u)
      (sigma_Fst v)
      (sigma_path_base w)
      (sigma_Snd u)
      (sigma_Snd v))
≔ sigma_Snd w;

// Reflexive Sigma path view: the pair of reflexive base and fibre paths.
symbol sigma_path_refl
  [A : Grpd]
  [P : τ A → Grpd]
  (u : @τΣ_ A P)
  : τ (@SigmaPathView A P u u)
≔ @Struct_sigma
    (sigma_Fst u = sigma_Fst u)
    (λ p : τ (sigma_Fst u = sigma_Fst u),
      @PathOver A P (sigma_Fst u) (sigma_Fst u) p (sigma_Snd u) (sigma_Snd u))
    (eq_refl (sigma_Fst u))
    (@pathover_refl A P (sigma_Fst u) (sigma_Snd u));

// Sigma equality unfolds to its observational base-plus-fibre path view.
rule @= (@Σ_ $A $P) $u $v
  ↪ @SigmaPathView $A $P $u $v;

// First projection of Sigma reflexivity is base reflexivity.
rule sigma_Fst (@eq_refl (@Σ_ $A _) $u)
  ↪ @eq_refl $A (sigma_Fst $u);

// Second projection of Sigma reflexivity is reflexive pathover.
rule sigma_Snd (@eq_refl (@Σ_ $A $P) $u)
  ↪ @pathover_refl $A $P (sigma_Fst $u) (sigma_Snd $u);

// Proof-time Sigma reflexivity eta for the specialized `eq_refl` head. This
// does not make `eq_refl` runtime-convertible with `sigma_path_refl`; it only
// lets reflexivity proofs elaborate between the generic reflexive path and the
// Sigma path-view pair.
unif_rule
  @eq_refl (@Σ_ $A $P) $u
  ≡ @Struct_sigma _ _ $x $y
  ↪ [
      $x ≡ @eq_refl $A (@sigma_Fst $A $P $u);
      $y ≡ @pathover_refl $A $P (@sigma_Fst $A $P $u) (@sigma_Snd $A $P $u)
    ];

// Encode a generic Sigma equality into the observational Sigma path view.
symbol sigma_path_encode
  [A : Grpd]
  [P : τ A → Grpd]
  [u v : @τΣ_ A P]
  (p : τ (u = v))
  : τ (@SigmaPathView A P u v)
≔ ind_eq
    p
    (λ s : @τΣ_ A P, @SigmaPathView A P s v)
    (sigma_path_refl v);

// -------------------------------------------------------------------------------------------------
// 1b. Minimal groupoid-level dependent products and type equivalences
// -------------------------------------------------------------------------------------------------

/*
  Groupoid-level dependent products are initially only a decoded object
  former. Observational Pi path computation is owned by later path-view
  infrastructure, not by this first formation rule.
*/
constant symbol Pi_grpd
  [A : Grpd]
  (B : τ A → Grpd)
  : Grpd;

// Decoding beta for the groupoid-level dependent function classifier.
rule τ (@Pi_grpd $A $B) ↪ Π x : τ $A, τ ($B x);

// Constant-family pathover bridge: an ordinary fibre path can be viewed over
// any base path when the family is definitionally constant.
symbol const_pathover
  [A B : Grpd]
  [x y : τ A]
  [u v : τ B]
  (p : τ (x = y))
  (q : τ (u = v))
  : τ (@PathOver A (λ _ : τ A, B) x y p u v)
≔ @ind_eqr A y
    (λ x : τ A, λ p : τ (x = y),
      @Pi_grpd B (λ u : τ B,
        @Pi_grpd B (λ v : τ B,
          @Pi_grpd (@= B u v)
            (λ _ : τ (@= B u v),
              @PathOver A (λ _ : τ A, B) x y p u v))))
    (λ u : τ B, λ v : τ B, λ q : τ (u = v), q)
    x
    p
    u
    v
    q;

// Constant-family pathover elimination: the fibre component of a path over a
// constant family can be read back as an ordinary path in the constant fibre.
symbol const_pathover_path
  [A B : Grpd]
  [x y : τ A]
  [u v : τ B]
  (p : τ (x = y))
  (q : τ (@PathOver A (λ _ : τ A, B) x y p u v))
  : τ (u = v)
≔ @ind_eqr A y
    (λ x : τ A, λ p : τ (x = y),
      @Pi_grpd B (λ u : τ B,
        @Pi_grpd B (λ v : τ B,
          @Pi_grpd (@PathOver A (λ _ : τ A, B) x y p u v)
            (λ _ : τ (@PathOver A (λ _ : τ A, B) x y p u v),
              u = v))))
    (λ u : τ B, λ v : τ B, λ q : τ (@PathOver A (λ _ : τ A, B) y y (eq_refl y) u v), q)
    x
    p
    u
    v
    q;

// Nondependent function classifier `A -> B` as a constant-family Pi.
symbol Function_grpd
  (A B : Grpd)
  : Grpd
≔ @Pi_grpd A (λ _ : τ A, B);

// Build equality of dependent pairs from a base path and fibre pathover.
symbol sigma_path_intro
  [A : Grpd]
  [P : τ A → Grpd]
  [x y : τ A]
  [a : τ (P x)]
  [b : τ (P y)]
  (p : τ (x = y))
  (q : τ (@PathOver A P x y p a b))
  : τ (@Struct_sigma A P x a = @Struct_sigma A P y b)
≔ @ind_eqr A y
    (λ x : τ A, λ p : τ (x = y),
      @Pi_grpd (P x) (λ a : τ (P x),
        @Pi_grpd (P y) (λ b : τ (P y),
          @Pi_grpd (@PathOver A P x y p a b)
            (λ _ : τ (@PathOver A P x y p a b),
              @Struct_sigma A P x a = @Struct_sigma A P y b))))
    (λ a : τ (P y), λ b : τ (P y), λ q : τ (@PathOver A P y y (eq_refl y) a b),
      @eq_ap
        (P y)
        (@Σ_ A P)
        (λ z : τ (P y), @Struct_sigma A P y z)
        a
        b
        q)
    x
    p
    a
    b
    q;

// Decode the observational Sigma path view back to pair equality.
symbol sigma_path_decode
  [A : Grpd]
  [P : τ A → Grpd]
  [u v : @τΣ_ A P]
  (w : τ (@SigmaPathView A P u v))
  : τ (u = v)
≔ @sigma_ind A P
    (λ u : @τΣ_ A P,
      @Pi_grpd (@Σ_ A P) (λ v : @τΣ_ A P,
        @Pi_grpd (@SigmaPathView A P u v)
          (λ _ : τ (@SigmaPathView A P u v), u = v)))
    (λ x : τ A, λ a : τ (P x),
      @sigma_ind A P
        (λ v : @τΣ_ A P,
          @Pi_grpd (@SigmaPathView A P (@Struct_sigma A P x a) v)
            (λ _ : τ (@SigmaPathView A P (@Struct_sigma A P x a) v),
              @Struct_sigma A P x a = v))
        (λ y : τ A, λ b : τ (P y), λ w : τ (@SigmaPathView A P (@Struct_sigma A P x a) (@Struct_sigma A P y b)),
          @sigma_path_intro A P x y a b
            (sigma_path_base w)
            (sigma_path_fibre w)))
    u
    v
    w;

// Decoding the canonical reflexive Sigma view returns generic reflexivity.
// This is propositional for a variable pair and computes after Sigma
// elimination exposes its constructor.
symbol sigma_path_decode_refl
  [A : Grpd]
  [P : τ A → Grpd]
  (u : @τΣ_ A P)
  : τ (
      @sigma_path_decode A P u u (@sigma_path_refl A P u)
      = @eq_refl (@Σ_ A P) u)
≔ @sigma_ind A P
    (λ u : @τΣ_ A P,
      @sigma_path_decode A P u u (@sigma_path_refl A P u)
      = @eq_refl (@Σ_ A P) u)
    (λ x : τ A, λ a : τ (P x),
      @eq_refl
        (@= (@Σ_ A P)
          (@Struct_sigma A P x a)
          (@Struct_sigma A P x a))
        (@eq_refl (@Σ_ A P) (@Struct_sigma A P x a)))
    u;

// Decoding after encoding is propositionally the original arbitrary path.
symbol sigma_path_decode_encode
  [A : Grpd]
  [P : τ A → Grpd]
  [u v : @τΣ_ A P]
  (p : τ (u = v))
  : τ (
      @sigma_path_decode A P u v (@sigma_path_encode A P u v p)
      = p)
≔ @ind_eqr
    (@Σ_ A P)
    v
    (λ u : @τΣ_ A P, λ p : τ (u = v),
      @sigma_path_decode A P u v (@sigma_path_encode A P u v p)
      = p)
    (@sigma_path_decode_refl A P v)
    u
    p;

// Re-encoding a decoded canonical reflexive view returns that view.
symbol sigma_path_encode_decode_refl
  [A : Grpd]
  [P : τ A → Grpd]
  (u : @τΣ_ A P)
  : τ (
      @sigma_path_encode A P u u
        (@sigma_path_decode A P u u (@sigma_path_refl A P u))
      = @sigma_path_refl A P u)
≔ @sigma_ind A P
    (λ u : @τΣ_ A P,
      @sigma_path_encode A P u u
        (@sigma_path_decode A P u u (@sigma_path_refl A P u))
      = @sigma_path_refl A P u)
    (λ x : τ A, λ a : τ (P x),
      @eq_refl
        (@SigmaPathView
          A P
          (@Struct_sigma A P x a)
          (@Struct_sigma A P x a))
        (@sigma_path_refl A P (@Struct_sigma A P x a)))
    u;

// Literal-reflexivity base needed by generic J. This is kept separate from
// the canonical-view theorem above because proof-time Sigma reflexivity does
// not propagate transitively through the nested decode application.
symbol sigma_path_encode_decode_eq_refl
  [A : Grpd]
  [P : τ A → Grpd]
  (u : @τΣ_ A P)
  : τ (
      @sigma_path_encode A P u u
        (@sigma_path_decode A P u u (@eq_refl (@Σ_ A P) u))
      = @eq_refl (@Σ_ A P) u)
≔ @sigma_ind A P
    (λ u : @τΣ_ A P,
      @sigma_path_encode A P u u
        (@sigma_path_decode A P u u (@eq_refl (@Σ_ A P) u))
      = @eq_refl (@Σ_ A P) u)
    (λ x : τ A, λ a : τ (P x),
      @eq_refl
        (@= (@Σ_ A P)
          (@Struct_sigma A P x a)
          (@Struct_sigma A P x a))
        (@eq_refl (@Σ_ A P) (@Struct_sigma A P x a)))
    u;

// Encoding after decoding is propositionally the original arbitrary view.
symbol sigma_path_encode_decode
  [A : Grpd]
  [P : τ A → Grpd]
  [u v : @τΣ_ A P]
  (w : τ (@SigmaPathView A P u v))
  : τ (
      @sigma_path_encode A P u v (@sigma_path_decode A P u v w)
      = w)
≔ @ind_eqr
    (@Σ_ A P)
    v
    (λ u : @τΣ_ A P, λ w : τ (u = v),
      @sigma_path_encode A P u v (@sigma_path_decode A P u v w)
      = w)
    (@sigma_path_encode_decode_eq_refl A P v)
    u
    w;

// Identity action agrees propositionally with generic action on every path.
symbol eq_ap_id
  [A : Grpd]
  [x y : τ A]
  (p : τ (@= A x y))
  : τ (@= (@= A x y)
      p
      (@eq_ap A A (λ z : τ A, z) x y p))
≔ @ind_eqr A y
    (λ x : τ A, λ p : τ (@= A x y),
      @= (@= A x y)
        p
        (@eq_ap A A (λ z : τ A, z) x y p))
    (@eq_refl (@= A y y) (@eq_refl A y))
    x
    p;

// Generic path action respects composition propositionally.
symbol eq_ap_comp
  [A B C : Grpd]
  (f : τ A → τ B)
  (g : τ B → τ C)
  [x y : τ A]
  (p : τ (@= A x y))
  : τ (@= (@= C (g (f x)) (g (f y)))
      (@eq_ap B C g (f x) (f y) (@eq_ap A B f x y p))
      (@eq_ap A C (λ z : τ A, g (f z)) x y p))
≔ @ind_eqr A y
    (λ x : τ A, λ p : τ (@= A x y),
      @= (@= C (g (f x)) (g (f y)))
        (@eq_ap B C g (f x) (f y) (@eq_ap A B f x y p))
        (@eq_ap A C (λ z : τ A, g (f z)) x y p))
    (@eq_refl
      (@= C (g (f y)) (g (f y)))
      (@eq_refl C (g (f y))))
    x
    p;


// Cancel p^-1 against p on the left of an arbitrary tail path.
symbol eq_trans_inv_left
  [X : Grpd]
  [x y : τ X]
  (p : τ (@= X x y))
  [z : τ X]
  (r : τ (@= X y z))
  : τ (@=
      (@= X y z)
      (@eq_trans
        X y x z
        (@eq_sym X x y p)
        (@eq_trans X x y z p r))
      r)
≔ @ind_eqr
    X
    y
    (λ x : τ X,
      λ p : τ (@= X x y),
      @Pi_grpd
        X
        (λ z : τ X,
          @Pi_grpd
            (@= X y z)
            (λ r : τ (@= X y z),
              @=
                (@= X y z)
                (@eq_trans
                  X y x z
                  (@eq_sym X x y p)
                  (@eq_trans X x y z p r))
                r)))
    (λ z : τ X,
      λ r : τ (@= X y z),
      @eq_refl (@= X y z) r)
    x
    p
    z
    r;


// Propositional right unit for J-derived path composition.
symbol eq_trans_right_unit
  [X : Grpd]
  [x y : τ X]
  (p : τ (@= X x y))
  : τ (@=
      (@= X x y)
      (@eq_trans X x y y p (@eq_refl X y))
      p)
≔ @ind_eqr
    X
    y
    (λ x : τ X,
      λ p : τ (@= X x y),
      @=
        (@= X x y)
        (@eq_trans X x y y p (@eq_refl X y))
        p)
    (@eq_refl (@= X y y) (@eq_refl X y))
    x
    p;

// Right cancellation of a common path suffix, proved by J on that suffix.
symbol eq_trans_right_cancel
  [X : Grpd]
  [x y : τ X]
  (p q : τ (@= X x y))
  [z : τ X]
  (r : τ (@= X y z))
  (s : τ (@=
      (@= X x z)
      (@eq_trans X x y z p r)
      (@eq_trans X x y z q r)))
  : τ (@= (@= X x y) p q)
≔ @ind_eqr
    X
    z
    (λ y : τ X,
      λ r : τ (@= X y z),
      @Pi_grpd
        (@= X x y)
        (λ p : τ (@= X x y),
          @Pi_grpd
            (@= X x y)
            (λ q : τ (@= X x y),
              @Pi_grpd
                (@=
                  (@= X x z)
                  (@eq_trans X x y z p r)
                  (@eq_trans X x y z q r))
                (λ _ : τ (@=
                    (@= X x z)
                    (@eq_trans X x y z p r)
                    (@eq_trans X x y z q r)),
                  @= (@= X x y) p q))))
    (λ p : τ (@= X x z),
      λ q : τ (@= X x z),
      λ s : τ (@=
          (@= X x z)
          (@eq_trans X x z z p (@eq_refl X z))
          (@eq_trans X x z z q (@eq_refl X z))),
      @eq_trans
        (@= X x z)
        p
        (@eq_trans X x z z p (@eq_refl X z))
        q
        (@eq_sym
          (@= X x z)
          (@eq_trans X x z z p (@eq_refl X z))
          p
          (@eq_trans_right_unit X x z p))
        (@eq_trans
          (@= X x z)
          (@eq_trans X x z z p (@eq_refl X z))
          (@eq_trans X x z z q (@eq_refl X z))
          q
          s
          (@eq_trans_right_unit X x z q)))
    y
    r
    p
    q
    s;

// Naturality of a homotopy h(z) = z, specialized to the identity target so
// the selected right-hand action is the literal path p.
symbol retraction_homotopy_naturality
  [X : Grpd]
  (h : τ X → τ X)
  (eta : Π z : τ X, τ (@= X (h z) z))
  [x y : τ X]
  (p : τ (@= X x y))
  : τ (@=
      (@= X (h x) y)
      (@eq_trans
        X (h x) (h y) y
        (@eq_ap X X h x y p)
        (eta y))
      (@eq_trans X (h x) x y (eta x) p))
≔ @ind_eqr
    X
    y
    (λ x : τ X,
      λ p : τ (@= X x y),
      @=
        (@= X (h x) y)
        (@eq_trans
          X (h x) (h y) y
          (@eq_ap X X h x y p)
          (eta y))
        (@eq_trans X (h x) x y (eta x) p))
    (@eq_sym
      (@= X (h y) y)
      (@eq_trans X (h y) y y (eta y) (@eq_refl X y))
      (eta y)
      (@eq_trans_right_unit X (h y) y (eta y)))
    x
    p;

// A retraction homotopy is natural with itself:
// eta(h x) = ap(h,eta x).
symbol retraction_homotopy_self_naturality
  [X : Grpd]
  (h : τ X → τ X)
  (eta : Π z : τ X, τ (@= X (h z) z))
  (x : τ X)
  : τ (@=
      (@= X (h (h x)) (h x))
      (eta (h x))
      (@eq_ap X X h (h x) x (eta x)))
≔ @eq_sym
    (@= X (h (h x)) (h x))
    (@eq_ap X X h (h x) x (eta x))
    (eta (h x))
    (@eq_trans_right_cancel
      X
      (h (h x))
      (h x)
      (@eq_ap X X h (h x) x (eta x))
      (eta (h x))
      x
      (eta x)
      (@retraction_homotopy_naturality
        X h eta (h x) x (eta x)));

// Standard adjusted counit
//   epsilon'(b) = epsilon(f(l b))^-1 ; ap(f,eta(l b)) ; epsilon(b).
symbol half_adjoint_counit
  [A B : Grpd]
  (f : τ A → τ B)
  (l : τ B → τ A)
  (eta : Π x : τ A, τ (@= A (l (f x)) x))
  (epsilon : Π b : τ B, τ (@= B (f (l b)) b))
  (b : τ B)
  : τ (@= B (f (l b)) b)
≔ @eq_trans
    B
    (f (l b))
    (f (l (f (l b))))
    b
    (@eq_sym
      B
      (f (l (f (l b))))
      (f (l b))
      (epsilon (f (l b))))
    (@eq_trans
      B
      (f (l (f (l b))))
      (f (l b))
      b
      (@eq_ap
        A B f
        (l (f (l b)))
        (l b)
        (eta (l b)))
      (epsilon b));

// The adjusted middle path agrees with naturality's ap(f o l) presentation.
symbol half_adjoint_middle
  [A B : Grpd]
  (f : τ A → τ B)
  (l : τ B → τ A)
  (eta : Π x : τ A, τ (@= A (l (f x)) x))
  (x : τ A)
  : τ (@=
      (@= B
        (f (l (f (l (f x)))))
        (f (l (f x))))
      (@eq_ap
        A B f
        (l (f (l (f x))))
        (l (f x))
        (eta (l (f x))))
      (@eq_ap
        B B
        (λ b : τ B, f (l b))
        (f (l (f x)))
        (f x)
        (@eq_ap A B f (l (f x)) x (eta x))))
≔ @eq_trans
    (@= B
      (f (l (f (l (f x)))))
      (f (l (f x))))
    (@eq_ap A B f
      (l (f (l (f x))))
      (l (f x))
      (eta (l (f x))))
    (@eq_ap
      A B f
      (l (f (l (f x))))
      (l (f x))
      (@eq_ap
        A A
        (λ z : τ A, l (f z))
        (l (f x))
        x
        (eta x)))
    (@eq_ap
      B B
      (λ b : τ B, f (l b))
      (f (l (f x)))
      (f x)
      (@eq_ap A B f (l (f x)) x (eta x)))
    (@eq_ap
      (@= A (l (f (l (f x)))) (l (f x)))
      (@= B (f (l (f (l (f x))))) (f (l (f x))))
      (λ p : τ (@= A (l (f (l (f x)))) (l (f x))),
        @eq_ap A B f
          (l (f (l (f x))))
          (l (f x))
          p)
      (eta (l (f x)))
      (@eq_ap
        A A
        (λ z : τ A, l (f z))
        (l (f x))
        x
        (eta x))
      (@retraction_homotopy_self_naturality
        A
        (λ z : τ A, l (f z))
        eta
        x))
    (@eq_trans
      (@= B
        (f (l (f (l (f x)))))
        (f (l (f x))))
      (@eq_ap
        A B f
        (l (f (l (f x))))
        (l (f x))
        (@eq_ap
          A A
          (λ z : τ A, l (f z))
          (l (f x))
          x
          (eta x)))
      (@eq_ap
        A B
        (λ z : τ A, f (l (f z)))
        (l (f x))
        x
        (eta x))
      (@eq_ap
        B B
        (λ b : τ B, f (l b))
        (f (l (f x)))
        (f x)
        (@eq_ap A B f (l (f x)) x (eta x)))
      (@eq_ap_comp
        A A B
        (λ z : τ A, l (f z))
        f
        (l (f x))
        x
        (eta x))
      (@eq_sym
        (@= B
          (f (l (f (l (f x)))))
          (f (l (f x))))
        (@eq_ap
          B B
          (λ b : τ B, f (l b))
          (f (l (f x)))
          (f x)
          (@eq_ap A B f (l (f x)) x (eta x)))
        (@eq_ap
          A B
          (λ z : τ A, f (l (f z)))
          (l (f x))
          x
          (eta x))
        (@eq_ap_comp
          A B B
          f
          (λ b : τ B, f (l b))
          (l (f x))
          x
          (eta x))));

// Standard half-adjoint triangle ap(f,eta(x)) = epsilon'(f x).

// Adjusted counit after replacing its middle path by ap(f o l,ap(f,eta)).
symbol half_adjoint_adjusted_middle
  [A B : Grpd]
  (f : τ A → τ B)
  (l : τ B → τ A)
  (epsilon : Π b : τ B, τ (@= B (f (l b)) b))
  (x : τ A)
  (p : τ (@= B (f (l (f x))) (f x)))
  : τ (@= B (f (l (f x))) (f x))
≔ @eq_trans
    B
    (f (l (f x)))
    (f (l (f (l (f x)))))
    (f x)
    (@eq_sym
      B
      (f (l (f (l (f x)))))
      (f (l (f x)))
      (epsilon (f (l (f x)))))
    (@eq_trans
      B
      (f (l (f (l (f x)))))
      (f (l (f x)))
      (f x)
      (@eq_ap
        B B
        (λ b : τ B, f (l b))
        (f (l (f x)))
        (f x)
        p)
      (epsilon (f x)));

// Naturality exposes the cancellable epsilon^-1 ; epsilon prefix.
symbol half_adjoint_adjusted_natural
  [A B : Grpd]
  (f : τ A → τ B)
  (l : τ B → τ A)
  (epsilon : Π b : τ B, τ (@= B (f (l b)) b))
  (x : τ A)
  (p : τ (@= B (f (l (f x))) (f x)))
  : τ (@= B (f (l (f x))) (f x))
≔ @eq_trans
    B
    (f (l (f x)))
    (f (l (f (l (f x)))))
    (f x)
    (@eq_sym
      B
      (f (l (f (l (f x)))))
      (f (l (f x)))
      (epsilon (f (l (f x)))))
    (@eq_trans
      B
      (f (l (f (l (f x)))))
      (f (l (f x)))
      (f x)
      (epsilon (f (l (f x))))
      p);

symbol half_adjoint_counit_middle
  [A B : Grpd]
  (f : τ A → τ B)
  (l : τ B → τ A)
  (eta : Π a : τ A, τ (@= A (l (f a)) a))
  (epsilon : Π b : τ B, τ (@= B (f (l b)) b))
  (x : τ A)
  : τ (@=
      (@= B (f (l (f x))) (f x))
      (@half_adjoint_counit
        A B f l eta epsilon (f x))
      (@half_adjoint_adjusted_middle
        A B f l epsilon x
        (@eq_ap A B f (l (f x)) x (eta x))))
≔ @eq_ap
    (@= B
      (f (l (f (l (f x)))))
      (f (l (f x))))
    (@= B (f (l (f x))) (f x))
    (λ m : τ (@= B
        (f (l (f (l (f x)))))
        (f (l (f x)))),
      @eq_trans
        B
        (f (l (f x)))
        (f (l (f (l (f x)))))
        (f x)
        (@eq_sym
          B
          (f (l (f (l (f x)))))
          (f (l (f x)))
          (epsilon (f (l (f x)))))
        (@eq_trans
          B
          (f (l (f (l (f x)))))
          (f (l (f x)))
          (f x)
          m
          (epsilon (f x))))
    (@eq_ap A B f
      (l (f (l (f x))))
      (l (f x))
      (eta (l (f x))))
    (@eq_ap
      B B
      (λ b : τ B, f (l b))
      (f (l (f x)))
      (f x)
      (@eq_ap A B f (l (f x)) x (eta x)))
    (@half_adjoint_middle A B f l eta x);

symbol half_adjoint_middle_natural
  [A B : Grpd]
  (f : τ A → τ B)
  (l : τ B → τ A)
  (eta : Π a : τ A, τ (@= A (l (f a)) a))
  (epsilon : Π b : τ B, τ (@= B (f (l b)) b))
  (x : τ A)
  : τ (@=
      (@= B (f (l (f x))) (f x))
      (@half_adjoint_adjusted_middle
        A B f l epsilon x
        (@eq_ap A B f (l (f x)) x (eta x)))
      (@half_adjoint_adjusted_natural
        A B f l epsilon x
        (@eq_ap A B f (l (f x)) x (eta x))))
≔ @eq_ap
    (@= B
      (f (l (f (l (f x)))))
      (f x))
    (@= B (f (l (f x))) (f x))
    (λ t : τ (@= B
        (f (l (f (l (f x)))))
        (f x)),
      @eq_trans
        B
        (f (l (f x)))
        (f (l (f (l (f x)))))
        (f x)
        (@eq_sym
          B
          (f (l (f (l (f x)))))
          (f (l (f x)))
          (epsilon (f (l (f x)))))
        t)
    (@eq_trans
      B
      (f (l (f (l (f x)))))
      (f (l (f x)))
      (f x)
      (@eq_ap
        B B
        (λ b : τ B, f (l b))
        (f (l (f x)))
        (f x)
        (@eq_ap A B f (l (f x)) x (eta x)))
      (epsilon (f x)))
    (@eq_trans
      B
      (f (l (f (l (f x)))))
      (f (l (f x)))
      (f x)
      (epsilon (f (l (f x))))
      (@eq_ap A B f (l (f x)) x (eta x)))
    (@retraction_homotopy_naturality
      B
      (λ b : τ B, f (l b))
      epsilon
      (f (l (f x)))
      (f x)
      (@eq_ap A B f (l (f x)) x (eta x)));

// Standard half-adjoint triangle ap(f,eta(x)) = epsilon'(f x), now factored.
symbol half_adjoint_triangle
  [A B : Grpd]
  (f : τ A → τ B)
  (l : τ B → τ A)
  (eta : Π a : τ A, τ (@= A (l (f a)) a))
  (epsilon : Π b : τ B, τ (@= B (f (l b)) b))
  (x : τ A)
  : τ (@=
      (@= B (f (l (f x))) (f x))
      (@eq_ap A B f (l (f x)) x (eta x))
      (@half_adjoint_counit
        A B f l eta epsilon (f x)))
≔ @eq_sym
    (@= B (f (l (f x))) (f x))
    (@half_adjoint_counit A B f l eta epsilon (f x))
    (@eq_ap A B f (l (f x)) x (eta x))
    (@eq_trans
      (@= B (f (l (f x))) (f x))
      (@half_adjoint_counit A B f l eta epsilon (f x))
      (@half_adjoint_adjusted_middle
        A B f l epsilon x
        (@eq_ap A B f (l (f x)) x (eta x)))
      (@eq_ap A B f (l (f x)) x (eta x))
      (@half_adjoint_counit_middle
        A B f l eta epsilon x)
      (@eq_trans
        (@= B (f (l (f x))) (f x))
        (@half_adjoint_adjusted_middle
          A B f l epsilon x
          (@eq_ap A B f (l (f x)) x (eta x)))
        (@half_adjoint_adjusted_natural
          A B f l epsilon x
          (@eq_ap A B f (l (f x)) x (eta x)))
        (@eq_ap A B f (l (f x)) x (eta x))
        (@half_adjoint_middle_natural
          A B f l eta epsilon x)
        (@eq_trans_inv_left
          B
          (f (l (f (l (f x)))))
          (f (l (f x)))
          (epsilon (f (l (f x))))
          (f x)
          (@eq_ap A B f (l (f x)) x (eta x)))));


/*
  Shaped observational paths for the canonical dependent PathRecord.

  A record is viewed as a source field followed by the genuinely dependent
  tail `Σ dst : A, src = dst`. Its path classifier is therefore the existing
  Sigma path view over that nested tail. Literal record reflexivity has one
  stable former-specific head; projections, J, and the closed generic-
  consumer registry below decide how that head computes.
*/

// Dependent tail classifier of a path record with fixed source.
symbol PathRecordTail_grpd
  [A : Grpd]
  (src : τ A)
  : Grpd
≔ @Σ_ A (λ dst : τ A, src = dst);

// Read a path record's target and witness as its dependent tail.
symbol path_record_tail
  [A : Grpd]
  (r : τ (PathRecord_grpd A))
  : τ (PathRecordTail_grpd (path_record_src r))
≔ @Struct_sigma
    A
    (λ dst : τ A, path_record_src r = dst)
    (path_record_dst r)
    (path_record_witness r);

// Nested-Sigma structural view of the named record.
symbol path_record_as_sigma
  [A : Grpd]
  (r : τ (PathRecord_grpd A))
  : @τΣ_ A (λ src : τ A, PathRecordTail_grpd src)
≔ @Struct_sigma
    A
    (λ src : τ A, PathRecordTail_grpd src)
    (path_record_src r)
    (path_record_tail r);

// Structural path classifier: a source path plus a path over the tail family.
symbol PathRecordPathView
  [A : Grpd]
  (r s : τ (PathRecord_grpd A))
  : Grpd
≔ @SigmaPathView
    A
    (λ src : τ A, PathRecordTail_grpd src)
    (path_record_as_sigma r)
    (path_record_as_sigma s);

// Source component of a structural record path.
symbol path_record_path_src
  [A : Grpd]
  [r s : τ (PathRecord_grpd A)]
  (p : τ (@PathRecordPathView A r s))
  : τ (path_record_src r = path_record_src s)
≔ @sigma_path_base
    A
    (λ src : τ A, PathRecordTail_grpd src)
    (path_record_as_sigma r)
    (path_record_as_sigma s)
    p;

// Dependent tail component over the source path.
symbol path_record_path_tail
  [A : Grpd]
  [r s : τ (PathRecord_grpd A)]
  (p : τ (@PathRecordPathView A r s))
  : τ (@PathOver
      A
      (λ src : τ A, PathRecordTail_grpd src)
      (path_record_src r)
      (path_record_src s)
      (@path_record_path_src A r s p)
      (path_record_tail r)
      (path_record_tail s))
≔ @sigma_path_fibre
    A
    (λ src : τ A, PathRecordTail_grpd src)
    (path_record_as_sigma r)
    (path_record_as_sigma s)
    p;

// Stable shaped reflexivity for the PathRecord former.
injective symbol PathRecordPathRefl
  [A : Grpd]
  (r : τ (PathRecord_grpd A))
  : τ (@PathRecordPathView A r r);

// PathRecord equality exposes its structural nested-Sigma view.
rule @= (PathRecord_grpd $A) $r $s
  ↪ @PathRecordPathView $A $r $s;

// Literal PathRecord reflexivity selects the stable shaped head.
rule @eq_refl (PathRecord_grpd $A) $r
  ↪ @PathRecordPathRefl $A $r;

// Shaped source and dependent-tail projection betas.
rule sigma_Fst (@PathRecordPathRefl $A $r)
  ↪ @eq_refl $A (path_record_src $r);

// The dependent tail beta follows the source beta so its PathOver index is
// already in the canonical reflexive form during subject-reduction checking.
rule sigma_Snd (@PathRecordPathRefl $A $r)
  ↪ @pathover_refl
      $A
      (λ src : τ $A, PathRecordTail_grpd src)
      (path_record_src $r)
      (path_record_tail $r);

// Closed shaped-reflexivity registration for the generic J owner. This beta
// is reflexive only; arbitrary structural path constructors remain stuck.
// lhs-audit: keep 1,2 -- the rigid former and repeated endpoint select the
// exact shaped motive after inner eq_refl has exposed PathRecordPathRefl.
rule @ind_eqr
      (PathRecord_grpd $A)
      $r
      _
      $u
      $r
      (@PathRecordPathRefl $A $r)
  ↪ $u;

/*
  PathRecord path-characterization maps.

  Public PathRecord equality already reduces directly to PathRecordPathView,
  so these are transparent identity views rather than a second normalization
  through the nested Sigma encode/decode functions. This preserves shaped
  reflexivity while giving the ordinary HoTT-facing round trips stable names.
*/

// Observe a PathRecord equality as its structural path view.
symbol path_record_path_encode
  [A : Grpd]
  [r s : τ (PathRecord_grpd A)]
  (p : τ (r = s))
  : τ (@PathRecordPathView A r s)
≔ p;

// Read a structural PathRecord view as public PathRecord equality.
symbol path_record_path_decode
  [A : Grpd]
  [r s : τ (PathRecord_grpd A)]
  (w : τ (@PathRecordPathView A r s))
  : τ (r = s)
≔ w;

// PathRecord decode after encode is pointwise reflexivity.
symbol path_record_path_decode_encode
  [A : Grpd]
  [r s : τ (PathRecord_grpd A)]
  (p : τ (r = s))
  : τ (
      @path_record_path_decode A r s
        (@path_record_path_encode A r s p)
      = p)
≔ eq_refl p;

// PathRecord encode after decode is pointwise reflexivity.
symbol path_record_path_encode_decode
  [A : Grpd]
  [r s : τ (PathRecord_grpd A)]
  (w : τ (@PathRecordPathView A r s))
  : τ (
      @path_record_path_encode A r s
        (@path_record_path_decode A r s w)
      = w)
≔ eq_refl w;

// Canonical dependent action of the witness field over a record path.
symbol path_record_witness_action
  [A : Grpd]
  [r s : τ (PathRecord_grpd A)]
  (p : τ (@PathRecordPathView A r s))
  : τ (@PathOver
      (PathRecord_grpd A)
      (λ t : τ (PathRecord_grpd A),
        @= A (path_record_src t) (path_record_dst t))
      r
      s
      p
      (path_record_witness r)
      (path_record_witness s))
≔ @eq_apd
    (PathRecord_grpd A)
    (λ t : τ (PathRecord_grpd A),
      @= A (path_record_src t) (path_record_dst t))
    (λ t : τ (PathRecord_grpd A),
      path_record_witness t)
    r
    s
    p;

// Observational Pi path view: dependent pointwise action over every base path.
symbol PiPathView
  [A : Grpd]
  (B : τ A → Grpd)
  (f g : Π x : τ A, τ (B x))
  : Grpd
≔ @Pi_grpd A
    (λ x0 : τ A,
      @Pi_grpd A
        (λ x1 : τ A,
          @Pi_grpd (x0 = x1)
            (λ p : τ (x0 = x1),
              @PathOver A B x0 x1 p (f x0) (g x1))));

// Pi equality unfolds to its observational dependent pointwise path view.
rule @= (@Pi_grpd $A $B) $f $g
  ↪ @PiPathView $A $B $f $g;

// Reflexive Pi path view of a dependent function.
symbol pi_path_refl
  [A : Grpd]
  [B : τ A → Grpd]
  (f : Π x : τ A, τ (B x))
  : τ (@PiPathView A B f f)
≔ @eq_refl (@Pi_grpd A B) f;

// Pi reflexivity evaluated over p is dependent action `apd(f,p)`.
rule @eq_refl (@Pi_grpd $A $B) $f $x0 $x1 $p
  ↪ @eq_apd $A $B $f $x0 $x1 $p;

// Encode Pi equality into the observational view (definitionally the path).
symbol pi_path_encode
  [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  (p : τ (@= (@Pi_grpd A B) f g))
  : τ (@PiPathView A B f g)
≔ p;

/*
  Ordinary HoTT-facing Pi extensionality over the related-input PiPathView.

  PiHapply observes a structured function path on the diagonal. PiFunext
  extends diagonal pointwise paths to arbitrary related inputs by base-path
  induction. Their forward composite computes pointwise at runtime; the
  reverse composite is propositional and uses one selected proof-time
  reflexive coherence equation as the base of generic J.
*/

// Classifier of diagonal pointwise paths between dependent functions.
symbol PiPointwisePath
  [A : Grpd]
  (B : τ A → Grpd)
  (f g : Π x : τ A, τ (B x))
  : Grpd
≔ @Pi_grpd A (λ x : τ A, f x = g x);

// Diagonal observation of a structured Pi path.
injective symbol PiHapply
  [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  (p : τ (f = g))
  : τ (@PiPointwisePath A B f g);

// Point application of happly exposes the diagonal related-input component.
rule @PiHapply _ _ _ _ $p $x
  ↪ $p $x $x (@eq_refl _ $x);

// Function-valued map used by equivalence packaging and path action.
symbol PiHapplyMap
  [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  : τ (@= (@Pi_grpd A B) f g) → τ (@PiPointwisePath A B f g)
≔ λ p : τ (@= (@Pi_grpd A B) f g), @PiHapply A B f g p;

// Stable introduction of a structured Pi path from pointwise paths.
injective symbol PiFunext
  [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  (h : τ (@PiPointwisePath A B f g))
  : τ (f = g);

// Function-valued inverse used by the equivalence package.
symbol PiFunextMap
  [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  : τ (@PiPointwisePath A B f g) → τ (@= (@Pi_grpd A B) f g)
≔ λ h : τ (@PiPointwisePath A B f g), @PiFunext A B f g h;

// Related-input action extends diagonal data by ordinary base-path induction.
rule @PiFunext $A $B $f $g $h $x0 $x1 $p
  ↪ @ind_eqr $A $x1
      (λ x0 : τ $A, λ p : τ (x0 = $x1),
        @PathOver $A $B x0 $x1 p ($f x0) ($g $x1))
      ($h $x1)
      $x0
      $p;

// Pointwise runtime beta is owned by the two projection rules above:
// PiHapply(PiFunext(h))[x] reduces to h[x]. The whole function is not given a
// second eta-like runtime fold.

// Proof-time Pi reflexive eta coherence. This is a semantically justified
// selected structural law: the transparent lambda presentation reduces to
// the same equation, while neither stable path head is a runtime alias. Typed
// eq_refl below tests firing; it is not independent semantic validation.
unif_rule
  @PiFunext $A $B $f $f
    (@PiHapply $A $B $f $f (@eq_refl (@Pi_grpd $A $B) $f))
  ≡ @eq_refl (@Pi_grpd $A $B) $f
  ↪ [ tt ≡ tt ];

// Propositional reverse composite, derived by retained generic path induction.
symbol pi_funext_eta
  [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  (p : τ (f = g))
  : τ (@PiFunext A B f g (@PiHapply A B f g p) = p)
≔ @ind_eqr (@Pi_grpd A B) g
    (λ f : τ (@Pi_grpd A B), λ p : τ (f = g),
      @PiFunext A B f g (@PiHapply A B f g p) = p)
    (@eq_refl
      (@= (@Pi_grpd A B) g g)
      (@eq_refl (@Pi_grpd A B) g))
    f
    p;

// Propositional forward composite, constructed through the same related-input
// PiFunext owner. It is proof data, not a whole-function runtime fold.
symbol pi_happly_beta
  [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  (h : τ (@PiPointwisePath A B f g))
  : τ (
      @PiHapply A B f g (@PiFunext A B f g h)
      = h)
≔ @PiFunext
    A
    (λ x : τ A, @= (B x) (f x) (g x))
    (@PiHapply A B f g (@PiFunext A B f g h))
    h
    (λ x : τ A,
      @eq_refl
        (@= (B x) (f x) (g x))
        (h x));

// Contractibility: a chosen centre together with a path to every point.
symbol IsContr
  (X : Grpd)
  : Grpd
≔ `Σ_ centre : τ X,
   @Pi_grpd X (λ x : τ X, centre = x);

// Centre projection of contractibility evidence.
symbol is_contr_center
  [X : Grpd]
  (c : τ (IsContr X))
  : τ X
≔ sigma_Fst c;

// Contraction path from the selected centre to a point.
symbol is_contr_path
  [X : Grpd]
  (c : τ (IsContr X))
  (x : τ X)
  : τ (is_contr_center c = x)
≔ sigma_Snd c x;

/*
  Homotopy truncation properties.

  `TruncLevel` starts at -2. `IsTruncGrpd(-2,A)` is contractibility, while
  `IsTruncGrpd(n+1,A)` says every identity type of A is n-truncated. This is a
  property of an existing classifier, not a truncation reflector and not the
  later universe that packages truncated classifiers.
*/
inductive TruncLevel : TYPE ≔
| trunc_minus_two : TruncLevel
| trunc_succ : TruncLevel → TruncLevel;

// Readable level -1.
symbol trunc_minus_one : TruncLevel
≔ trunc_succ trunc_minus_two;

// Readable level 0.
symbol trunc_zero : TruncLevel
≔ trunc_succ trunc_minus_one;

// Readable level 1.
symbol trunc_one : TruncLevel
≔ trunc_succ trunc_zero;

// Recursive predicate that A is n-truncated.
symbol IsTruncGrpd
  (n : TruncLevel)
  (A : Grpd)
  : Grpd;

// Truncation recursion: contractibility at -2 and truncated path spaces at
// the successor level.
rule IsTruncGrpd trunc_minus_two $A
  ↪ IsContr $A
with IsTruncGrpd (trunc_succ $n) $A
  ↪ @Pi_grpd $A
      (λ x : τ $A,
        @Pi_grpd $A
          (λ y : τ $A,
            IsTruncGrpd $n (@= $A x y)));

// Proposition-valued classifier view (-1-truncated).
symbol IsPropGrpd
  (A : Grpd)
  : Grpd
≔ IsTruncGrpd trunc_minus_one A;

// Set-valued classifier view (0-truncated).
symbol IsSetGrpd
  (A : Grpd)
  : Grpd
≔ IsTruncGrpd trunc_zero A;

// Ordinary-groupoid classifier view (1-truncated).
symbol IsGroupoidGrpd
  (A : Grpd)
  : Grpd
≔ IsTruncGrpd trunc_one A;

/*
  Truncation monotonicity.

  The base proves that every path space of a contractible classifier is
  contractible. The native level eliminator then raises truncation one step at
  a time; no global weakening rewrite or proof erasure is installed.
*/
// Path cancellation used by the contractible base: p^-1 followed by p = refl.
symbol eq_sym_trans_self
  [A : Grpd]
  [x y : τ A]
  (p : τ (@= A x y))
  : τ (@=
      (@= A y y)
      (@eq_trans A y x y (@eq_sym A x y p) p)
      (@eq_refl A y))
≔ @ind_eqr
    A
    y
    (λ x : τ A, λ p : τ (@= A x y),
      @=
        (@= A y y)
        (@eq_trans A y x y (@eq_sym A x y p) p)
        (@eq_refl A y))
    (@eq_refl (@= A y y) (@eq_refl A y))
    x
    p;

// Chosen path x -> centre -> y in a contractible classifier.
symbol contractible_path_center
  [A : Grpd]
  (c : τ (IsContr A))
  (x y : τ A)
  : τ (@= A x y)
≔ @eq_trans
    A
    x
    (is_contr_center c)
    y
    (@eq_sym A (is_contr_center c) x (is_contr_path c x))
    (is_contr_path c y);

// Every path equals the chosen path through the contractible centre.
symbol contractible_path_contract
  [A : Grpd]
  (c : τ (IsContr A))
  [x y : τ A]
  (p : τ (@= A x y))
  : τ (@=
      (@= A x y)
      (@contractible_path_center A c x y)
      p)
≔ @ind_eqr
    A
    y
    (λ x : τ A, λ p : τ (@= A x y),
      @=
        (@= A x y)
        (@contractible_path_center A c x y)
        p)
    (@eq_sym_trans_self
      A
      (is_contr_center c)
      y
      (is_contr_path c y))
    x
    p;

// The -2 -> -1 base: every contractible classifier is proposition-valued.
symbol is_contr_is_prop
  [A : Grpd]
  (c : τ (IsContr A))
  : τ (IsPropGrpd A)
≔ λ x : τ A, λ y : τ A,
    Struct_sigma
      (contractible_path_center c x y)
      (λ p : τ (@= A x y), contractible_path_contract c p);

/*
  Property-valued truncation evidence: the contractibility and Pi bases.

  Equality of contractibility witnesses follows the active dependent Sigma
  path view. The second contraction function is transported along the first
  centre path; PiFunext then compares the functions pointwise in contractible
  path spaces. This is propositional structure, not proof erasure.
*/
// Transport a contraction function along the chosen path between centres.
symbol is_contr_evidence_transport
  [A : Grpd]
  (c d : τ (IsContr A))
  : τ (@Pi_grpd A
      (λ x : τ A, @= A (is_contr_center c) x))
≔ @ind_eq
    A
    (is_contr_center c)
    (is_contr_center d)
    (is_contr_path c (is_contr_center d))
    (λ centre : τ A,
      @Pi_grpd A (λ x : τ A, @= A centre x))
    (λ x : τ A, is_contr_path d x);

// Dependent fibre path between the two contraction functions.
symbol is_contr_evidence_pathover
  [A : Grpd]
  (c d : τ (IsContr A))
  : τ (@PathOver
      A
      (λ centre : τ A,
        @Pi_grpd A (λ x : τ A, @= A centre x))
      (is_contr_center c)
      (is_contr_center d)
      (is_contr_path c (is_contr_center d))
      (λ x : τ A, is_contr_path c x)
      (λ x : τ A, is_contr_path d x))
≔ @PiFunext
    A
    (λ x : τ A, @= A (is_contr_center c) x)
    (λ x : τ A, is_contr_path c x)
    (@is_contr_evidence_transport A c d)
    (λ x : τ A,
      @contractible_path_center
        (@= A (is_contr_center c) x)
        (@is_contr_is_prop A c (is_contr_center c) x)
        (is_contr_path c x)
        (@is_contr_evidence_transport A c d x));

// Canonical propositional path between two contractibility witnesses.
symbol is_contr_evidence_path
  [A : Grpd]
  (c d : τ (IsContr A))
  : τ (@= (IsContr A) c d)
≔ Struct_sigma
    (is_contr_path c (is_contr_center d))
    (@is_contr_evidence_pathover A c d);

// An inhabited contractibility-evidence classifier is contractible.
symbol is_contr_evidence_is_contr
  [A : Grpd]
  (c : τ (IsContr A))
  : τ (IsContr (IsContr A))
≔ Struct_sigma
    c
    (λ d : τ (IsContr A), @is_contr_evidence_path A c d);

// Contractibility evidence is proposition-valued even when uninhabited.
symbol is_contr_evidence_is_prop
  [A : Grpd]
  : τ (IsPropGrpd (IsContr A))
≔ λ c : τ (IsContr A), λ d : τ (IsContr A),
    @is_contr_is_prop
      (IsContr A)
      (@is_contr_evidence_is_contr A c)
      c
      d;

// Dependent products of contractible classifiers are contractible.
symbol is_contr_pi
  [A : Grpd]
  [B : τ A → Grpd]
  (h : Π x : τ A, τ (IsContr (B x)))
  : τ (IsContr (@Pi_grpd A B))
≔ Struct_sigma
    (λ x : τ A, is_contr_center (h x))
    (λ f : τ (@Pi_grpd A B),
      @PiFunext
        A
        B
        (λ x : τ A, is_contr_center (h x))
        f
        (λ x : τ A, is_contr_path (h x) (f x)));

// Contractible base and contractible fibres have a contractible total space.
symbol is_contr_sigma
  [A : Grpd]
  [B : τ A → Grpd]
  (hA : τ (IsContr A))
  (hB : Π x : τ A, τ (IsContr (B x)))
  : τ (IsContr (@Σ_ A B))
≔ @Struct_sigma
    (@Σ_ A B)
    (λ c : @τΣ_ A B,
      @Pi_grpd (@Σ_ A B)
        (λ z : @τΣ_ A B, @= (@Σ_ A B) c z))
    (@Struct_sigma
      A
      B
      (is_contr_center hA)
      (is_contr_center (hB (is_contr_center hA))))
    (λ z : @τΣ_ A B,
      @Struct_sigma
        (@= A (is_contr_center hA) (sigma_Fst z))
        (λ p : τ (@= A (is_contr_center hA) (sigma_Fst z)),
          @PathOver
            A
            B
            (is_contr_center hA)
            (sigma_Fst z)
            p
            (is_contr_center (hB (is_contr_center hA)))
            (sigma_Snd z))
        (is_contr_path hA (sigma_Fst z))
        (is_contr_path
          (hB (is_contr_center hA))
          (@ind_eq
            A
            (is_contr_center hA)
            (sigma_Fst z)
            (is_contr_path hA (sigma_Fst z))
            B
            (sigma_Snd z))));

/*
  Universe of n-truncated ambient classifiers.

  `TruncGrpdU(n)` packages `carrier : Grpd` with evidence that the carrier is
  n-truncated. The evidence is retained data: this slice supplies record
  decoding and projection beta only, not proof erasure, package equality,
  subuniverse univalence, or a theorem that the package universe is itself
  n-truncated (its expected level under univalence is generally n+1).
*/
(n : TruncLevel) inductive TruncGrpdData : TYPE ≔
| Struct_trunc_grpd
    (carrier : Grpd)
    (evidence : τ (IsTruncGrpd n carrier))
    : TruncGrpdData n;

// Decoded classifier of n-truncated ambient classifiers.
constant symbol TruncGrpdU
  (n : TruncLevel)
  : Grpd;

// Decoding beta for the packaged truncated universe.
rule τ (TruncGrpdU $n)
  ↪ TruncGrpdData $n;

// Carrier projection from a packaged truncated classifier.
symbol trunc_grpd_carrier
  [n : TruncLevel]
  (X : τ (TruncGrpdU n))
  : Grpd;

// Carrier-projection constructor beta.
rule trunc_grpd_carrier
  (@Struct_trunc_grpd _ $carrier _)
  ↪ $carrier;

// Truncation-evidence projection for the selected carrier.
symbol trunc_grpd_evidence
  [n : TruncLevel]
  (X : τ (TruncGrpdU n))
  : τ (IsTruncGrpd n (trunc_grpd_carrier X));

// Evidence-projection constructor beta; evidence is exposed, not erased.
rule trunc_grpd_evidence
  (@Struct_trunc_grpd _ _ $evidence)
  ↪ $evidence;

// Reviewed eliminator facade for the native truncated-universe package.
symbol trunc_grpd_ind
  [n : TruncLevel]
  (Q : τ (TruncGrpdU n) → Grpd)
  (c : Π carrier : Grpd,
       Π evidence : τ (IsTruncGrpd n carrier),
       τ (Q (@Struct_trunc_grpd n carrier evidence)))
  (X : τ (TruncGrpdU n))
  : τ (Q X)
≔ @ind_TruncGrpdData n Q c X;

// Universe of proposition-valued classifiers (-1-types).
symbol PropU_grpd : Grpd
≔ TruncGrpdU trunc_minus_one;

// Universe of set-valued classifiers (0-types).
symbol SetU_grpd : Grpd
≔ TruncGrpdU trunc_zero;

// Universe of ordinary-groupoid classifiers (1-types).
symbol GroupoidU_grpd : Grpd
≔ TruncGrpdU trunc_one;

// Homotopy fibre of f over b: pairs `(a,p)` with `p : f(a) = b`.
symbol HFiber
  [A B : Grpd]
  (f : τ A → τ B)
  (b : τ B)
  : Grpd
≔ `Σ_ a : τ A, f a = b;

// Domain-point projection of a homotopy-fibre element.
symbol hfiber_point
  [A B : Grpd]
  [f : τ A → τ B]
  [b : τ B]
  (h : τ (@HFiber A B f b))
  : τ A
≔ sigma_Fst h;

// Equality-witness projection of a homotopy-fibre element.
symbol hfiber_path
  [A B : Grpd]
  [f : τ A → τ B]
  [b : τ B]
  (h : τ (@HFiber A B f b))
  : τ (f (hfiber_point h) = b)
≔ sigma_Snd h;

// A function is an equivalence when each homotopy fibre is contractible.
symbol IsEquivMap
  [A B : Grpd]
  (f : τ A → τ B)
  : Grpd
≔ @Pi_grpd B
    (λ b : τ B, IsContr (@HFiber A B f b));

// Contractible-fibre projection of equivalence evidence at b.
symbol is_equiv_fiber
  [A B : Grpd]
  [f : τ A → τ B]
  (e : τ (@IsEquivMap A B f))
  (b : τ B)
  : τ (IsContr (@HFiber A B f b))
≔ e b;

// Type/groupoid equivalence: a function with contractible homotopy fibres.
symbol TypeEquiv
  (A B : Grpd)
  : Grpd
≔ `Σ_ f : τ (Function_grpd A B),
   @IsEquivMap A B f;

// Forward map of a type equivalence.
symbol type_equiv_to
  [A B : Grpd]
  (e : τ (TypeEquiv A B))
  : τ A → τ B
≔ sigma_Fst e;

// Fibrewise-equivalence evidence carried by `TypeEquiv`.
symbol type_equiv_is_equiv
  [A B : Grpd]
  (e : τ (TypeEquiv A B))
  : τ (@IsEquivMap A B (type_equiv_to e))
≔ sigma_Snd e;

// Contractible homotopy fibre of an equivalence over b.
symbol type_equiv_fiber
  [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (b : τ B)
  : τ (IsContr (@HFiber A B (type_equiv_to e) b))
≔ type_equiv_is_equiv e b;

// Selected inverse map: the centre of the contractible fibre over b.
symbol type_equiv_from
  [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (b : τ B)
  : τ A
≔ @hfiber_point A B (type_equiv_to e) b
    (is_contr_center (type_equiv_fiber e b));

// Right inverse path: `to(from(b)) = b`.
symbol type_equiv_right
  [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (b : τ B)
  : τ (type_equiv_to e (type_equiv_from e b) = b)
≔ @hfiber_path A B (type_equiv_to e) b
    (is_contr_center (type_equiv_fiber e b));

// Left inverse path: `from(to(a)) = a`.
symbol type_equiv_left
  [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (a : τ A)
  : τ (type_equiv_from e (type_equiv_to e a) = a)
≔ @eq_ap
    (@HFiber A B (type_equiv_to e) (type_equiv_to e a))
    A
    (λ h : τ (@HFiber A B (type_equiv_to e) (type_equiv_to e a)),
      @hfiber_point A B (type_equiv_to e) (type_equiv_to e a) h)
    (is_contr_center (type_equiv_fiber e (type_equiv_to e a)))
    (@Struct_sigma A (λ x : τ A, type_equiv_to e x = type_equiv_to e a)
      a
      (eq_refl (type_equiv_to e a)))
    (is_contr_path
      (type_equiv_fiber e (type_equiv_to e a))
      (@Struct_sigma A (λ x : τ A, type_equiv_to e x = type_equiv_to e a)
        a
        (eq_refl (type_equiv_to e a))));

// Every point of the identity homotopy fibre equals its reflexive centre.
symbol hfiber_id_path
  [A : Grpd]
  [b a : τ A]
  (p : τ (a = b))
  : τ (
      @Struct_sigma A (λ x : τ A, x = b) b (eq_refl b)
      =
      @Struct_sigma A (λ x : τ A, x = b) a p)
≔ @ind_eqr A b
    (λ x : τ A, λ q : τ (x = b),
      @Struct_sigma A (λ t : τ A, t = b) b (eq_refl b)
      =
      @Struct_sigma A (λ t : τ A, t = b) x q)
    (eq_refl (@Struct_sigma A (λ t : τ A, t = b) b (eq_refl b)))
    a
    p;

// Contraction path proving the identity homotopy fibre contractible.
symbol hfiber_id_contr_path
  [A : Grpd]
  [b : τ A]
  (h : τ (@HFiber A A (λ x : τ A, x) b))
  : τ (
      @Struct_sigma A (λ x : τ A, x = b) b (eq_refl b)
      =
      h)
≔ @sigma_ind A
    (λ x : τ A, x = b)
    (λ h : @τΣ_ A (λ x : τ A, x = b),
      @Struct_sigma A (λ x : τ A, x = b) b (eq_refl b)
      =
      h)
    (λ a : τ A, λ p : τ (a = b), hfiber_id_path p)
    h;

// Reflexive type equivalence on A.
injective symbol type_equiv_refl
  [A : Grpd]
  : τ (TypeEquiv A A);

// Forward map of reflexive equivalence is the identity function.
rule sigma_Fst (@type_equiv_refl $A)
  ↪ λ x : τ $A, x;

// Equivalence evidence for reflexivity is identity-fibre contraction.
rule sigma_Snd (@type_equiv_refl $A)
  ↪ λ b : τ $A,
      @Struct_sigma
        (@HFiber $A $A (λ x : τ $A, x) b)
        (λ centre : τ (@HFiber $A $A (λ x : τ $A, x) b),
          @Pi_grpd
            (@HFiber $A $A (λ x : τ $A, x) b)
            (λ h : τ (@HFiber $A $A (λ x : τ $A, x) b), centre = h))
        (@Struct_sigma $A (λ x : τ $A, x = b) b (eq_refl b))
        (λ h : τ (@HFiber $A $A (λ x : τ $A, x) b),
          hfiber_id_contr_path h);

// The identity function has contractible homotopy fibres.
symbol type_equiv_refl_is_equiv
  [A : Grpd]
  : τ (@IsEquivMap A A (λ x : τ A, x))
≔ @type_equiv_is_equiv A A (@type_equiv_refl A);

/*
  Constructor-specific TypeEquiv skeletons.

  These are the first computational-univalence closure entries. The
  equivalence packages are transparent Sigma values, so `type_equiv_to`
  computes by ordinary constructor projection. The `*_is_equiv` witnesses are
  isolated proof capabilities: they do not own runtime computation and should
  later be replaced or refined by derived fibre-contractibility proofs as the
  Sigma/Pi observational path algebra matures.
*/

injective symbol Product_grpd
  (A B : Grpd)
  : Grpd;

// Product decoding is the constant-family dependent-pair representation.
rule τ (Product_grpd $A $B)
  ↪ @τΣ_ $A (λ _ : τ $A, $B);

/*
  Stable path classifier for groupoid-level products.

  The classifier head remains rigid for proof-time comparison, while its
  carrier decodes to the already-established constant-family Sigma path data.
  The named constructor/projections/eliminator below preserve the existing
  computational base-plus-fibre interface.
*/
injective symbol ProductPathView
  [A B : Grpd]
  (p q : τ (Product_grpd A B))
  : Grpd;

// Product path data decode to the existing constant-family Sigma path data.
rule τ (@ProductPathView $A $B $p $q)
  ↪ τ (@SigmaPathView $A (λ _ : τ $A, $B) $p $q);

/*
  Transparent carrier adapters between the stable Product classifier and the
  established constant-family Sigma presentation. Their bodies are literal
  identities because both carriers reduce to the same decoded type; the
  classifier heads themselves intentionally remain distinct.
*/
symbol product_path_to_sigma_view
  [A B : Grpd]
  [p q : τ (Product_grpd A B)]
  (w : τ (@ProductPathView A B p q))
  : τ (@SigmaPathView A (λ _ : τ A, B) p q)
≔ w;

symbol sigma_view_to_product_path
  [A B : Grpd]
  [p q : τ (Product_grpd A B)]
  (w : τ (@SigmaPathView A (λ _ : τ A, B) p q))
  : τ (@ProductPathView A B p q)
≔ w;

// Stable Product-path introduction from base and constant-fibre paths.
symbol product_path_intro
  [A B : Grpd]
  [p q : τ (Product_grpd A B)]
  (base : τ (@= A (sigma_Fst p) (sigma_Fst q)))
  (fibre : τ (@PathOver
    A
    (λ _ : τ A, B)
    (sigma_Fst p)
    (sigma_Fst q)
    base
    (sigma_Snd p)
    (sigma_Snd q)))
  : τ (@ProductPathView A B p q)
≔ @Struct_sigma
    (@= A (sigma_Fst p) (sigma_Fst q))
    (λ r : τ (@= A (sigma_Fst p) (sigma_Fst q)),
      @PathOver
        A
        (λ _ : τ A, B)
        (sigma_Fst p)
        (sigma_Fst q)
        r
        (sigma_Snd p)
        (sigma_Snd q))
    base
    fibre;

// Base component of a stable Product path.
symbol product_path_base
  [A B : Grpd]
  [p q : τ (Product_grpd A B)]
  (w : τ (@ProductPathView A B p q))
  : τ (@= A (sigma_Fst p) (sigma_Fst q))
≔ sigma_Fst w;

// Constant-fibre component of a stable Product path.
symbol product_path_fibre
  [A B : Grpd]
  [p q : τ (Product_grpd A B)]
  (w : τ (@ProductPathView A B p q))
  : τ (@PathOver
      A
      (λ _ : τ A, B)
      (sigma_Fst p)
      (sigma_Fst q)
      (product_path_base w)
      (sigma_Snd p)
      (sigma_Snd q))
≔ sigma_Snd w;

// Fixed-endpoint eliminator for the stable Product path carrier.
symbol product_path_ind
  [A B : Grpd]
  [p q : τ (Product_grpd A B)]
  (Q : τ (@ProductPathView A B p q) → Grpd)
  (c : Π base : τ (@= A (sigma_Fst p) (sigma_Fst q)),
       Π fibre : τ (@PathOver
         A
         (λ _ : τ A, B)
         (sigma_Fst p)
         (sigma_Fst q)
         base
         (sigma_Snd p)
         (sigma_Snd q)),
       τ (Q (@product_path_intro A B p q base fibre)))
  (w : τ (@ProductPathView A B p q))
  : τ (Q w)
≔ @sigma_ind
    (@= A (sigma_Fst p) (sigma_Fst q))
    (λ base : τ (@= A (sigma_Fst p) (sigma_Fst q)),
      @PathOver
        A
        (λ _ : τ A, B)
        (sigma_Fst p)
        (sigma_Fst q)
        base
        (sigma_Snd p)
        (sigma_Snd q))
    Q
    c
    w;

// Stable Product reflexivity uses the established Sigma reflexivity data.
symbol product_path_refl
  [A B : Grpd]
  (p : τ (Product_grpd A B))
  : τ (@ProductPathView A B p p)
≔ @sigma_path_refl A (λ _ : τ A, B) p;

// Product equality uses the stable Product path classifier.
rule @= (Product_grpd $A $B) $p $q
  ↪ @ProductPathView $A $B $p $q;

// First component of product reflexivity.
rule sigma_Fst (@eq_refl (Product_grpd $A _) $u)
  ↪ @eq_refl $A (sigma_Fst $u);

// Second component of product reflexivity as constant-family pathover.
rule sigma_Snd (@eq_refl (Product_grpd $A $B) $u)
  ↪ @pathover_refl $A (λ _ : τ $A, $B) (sigma_Fst $u) (sigma_Snd $u);

// Pair constructor for the groupoid-level product.
symbol Product_pair_grpd
  [A B : Grpd]
  (x : τ A)
  (y : τ B)
  : τ (Product_grpd A B)
≔ @Struct_sigma A (λ _ : τ A, B) x y;

// Product of equivalence maps has contractible homotopy fibres.
symbol product_type_equiv_is_equiv
  [A A' B B' : Grpd]
  (eA : τ (TypeEquiv A A'))
  (eB : τ (TypeEquiv B B'))
  : τ (@IsEquivMap
      (Product_grpd A B)
      (Product_grpd A' B')
      (λ p : τ (Product_grpd A B),
        @Product_pair_grpd A' B'
          (type_equiv_to eA (sigma_Fst p))
          (type_equiv_to eB (sigma_Snd p))));

// Componentwise product of two type equivalences.
injective symbol product_type_equiv
  [A A' B B' : Grpd]
  (eA : τ (TypeEquiv A A'))
  (eB : τ (TypeEquiv B B'))
  : τ (TypeEquiv (Product_grpd A B) (Product_grpd A' B'));

// Forward map of product equivalence acts componentwise.
rule sigma_Fst (@product_type_equiv $A $A' $B $B' $eA $eB)
  ↪ λ p : τ (Product_grpd $A $B),
      @Product_pair_grpd $A' $B'
        (type_equiv_to $eA (sigma_Fst p))
        (type_equiv_to $eB (sigma_Snd p));

// Equivalence-evidence projection of the product equivalence.
rule sigma_Snd (@product_type_equiv $A $A' $B $B' $eA $eB)
  ↪ @product_type_equiv_is_equiv $A $A' $B $B' $eA $eB;

// Fibrewise equivalences induce an equivalence map on Sigma totals.
symbol sigma_type_equiv_same_base_is_equiv
  [A : Grpd]
  [P Q : τ A → Grpd]
  (e : Π x : τ A, τ (TypeEquiv (P x) (Q x)))
  : τ (@IsEquivMap
      (@Σ_ A P)
      (@Σ_ A Q)
      (λ s : τ (@Σ_ A P),
        @Struct_sigma A Q
          (sigma_Fst s)
          (type_equiv_to (e (sigma_Fst s)) (sigma_Snd s))));

// Type equivalence between Sigma types over one fixed base.
symbol sigma_type_equiv_same_base
  [A : Grpd]
  [P Q : τ A → Grpd]
  (e : Π x : τ A, τ (TypeEquiv (P x) (Q x)))
  : τ (TypeEquiv (@Σ_ A P) (@Σ_ A Q))
≔ @Struct_sigma
    (Function_grpd (@Σ_ A P) (@Σ_ A Q))
    (λ f : τ (Function_grpd (@Σ_ A P) (@Σ_ A Q)),
      @IsEquivMap (@Σ_ A P) (@Σ_ A Q) f)
    (λ s : τ (@Σ_ A P),
      @Struct_sigma A Q
        (sigma_Fst s)
        (type_equiv_to (e (sigma_Fst s)) (sigma_Snd s)))
    (@sigma_type_equiv_same_base_is_equiv A P Q e);

// Pointwise equivalences induce an equivalence map on dependent functions.
symbol pi_type_equiv_same_domain_is_equiv
  [A : Grpd]
  [B C : τ A → Grpd]
  (e : Π x : τ A, τ (TypeEquiv (B x) (C x)))
  : τ (@IsEquivMap
      (@Pi_grpd A B)
      (@Pi_grpd A C)
      (λ f : τ (@Pi_grpd A B),
        λ x : τ A, type_equiv_to (e x) (f x)));

// Type equivalence between Pi types over one fixed domain.
symbol pi_type_equiv_same_domain
  [A : Grpd]
  [B C : τ A → Grpd]
  (e : Π x : τ A, τ (TypeEquiv (B x) (C x)))
  : τ (TypeEquiv (@Pi_grpd A B) (@Pi_grpd A C))
≔ @Struct_sigma
    (Function_grpd (@Pi_grpd A B) (@Pi_grpd A C))
    (λ f : τ (Function_grpd (@Pi_grpd A B) (@Pi_grpd A C)),
      @IsEquivMap (@Pi_grpd A B) (@Pi_grpd A C) f)
    (λ f : τ (@Pi_grpd A B),
      λ x : τ A, type_equiv_to (e x) (f x))
    (@pi_type_equiv_same_domain_is_equiv A B C e);

/*
  Specified-inverse equivalence capability.

  This keeps the operational inverse map explicit.  The proof fields are
  capabilities, not runtime rewrite owners.
*/
symbol EquivByInverse
  [A B : Grpd]
  (f : τ A → τ B)
  (g : τ B → τ A)
  : Grpd
≔ @Product_grpd
    (@Pi_grpd A (λ a : τ A, @= A (g (f a)) a))
    (@Pi_grpd B (λ b : τ B, @= B (f (g b)) b));

/*
  Transparent quasi-inverse-to-contractible-fibre theorem.

  Left-based J reduces an arbitrary fibre path to the half-adjoint
  triangle. The resulting adjusted contraction is re-centred at the
  originally supplied right-inverse witness, preserving the historical
  selected-centre normal form without a rewrite rule or theorem axiom.
*/
// Double symmetry is propositionally identity.
symbol eq_sym_sym
  [A : Grpd]
  [x y : τ A]
  (p : τ (@= A x y))
  : τ (@=
      (@= A x y)
      (@eq_sym A y x (@eq_sym A x y p))
      p)
≔ @ind_eqr
    A y
    (λ x : τ A,
      λ p : τ (@= A x y),
        @=
          (@= A x y)
          (@eq_sym A y x (@eq_sym A x y p))
          p)
    (@eq_refl (@= A y y) (@eq_refl A y))
    x
    p;

// Left-based path induction derived from the primitive right-based owner.
symbol ind_eql
  [A : Grpd]
  [x : τ A]
  (P : Π y : τ A, τ (@= A x y) → Grpd)
  (u : τ (P x (@eq_refl A x)))
  [y : τ A]
  (p : τ (@= A x y))
  : τ (P y p)
≔ @ind_eq
    (@= A x y)
    p
    (@eq_sym A y x (@eq_sym A x y p))
    (@eq_sym
      (@= A x y)
      (@eq_sym A y x (@eq_sym A x y p))
      p
      (@eq_sym_sym A x y p))
    (λ q : τ (@= A x y), P y q)
    (@ind_eqr
      A x
      (λ y : τ A,
        λ q : τ (@= A y x),
          P y (@eq_sym A y x q))
      u
      y
      (@eq_sym A x y p));

// Base point in the fibre contraction selected by a quasi-inverse.
symbol qinv_fibre_base_path
  [A B : Grpd]
  (f : τ A → τ B)
  (g : τ B → τ A)
  (eta : Π a : τ A, τ (@= A (g (f a)) a))
  [a : τ A]
  [b : τ B]
  (p : τ (@= B (f a) b))
  : τ (@= A (g b) a)
≔ @eq_trans
    A
    (g b)
    (g (f a))
    a
    (@eq_ap B A g b (f a) (@eq_sym B (f a) b p))
    (eta a);

// The half-adjoint triangle is exactly the dependent fibre-path base case.
symbol qinv_fibre_pathover
  [A B : Grpd]
  (f : τ A → τ B)
  (g : τ B → τ A)
  (eta : Π a : τ A, τ (@= A (g (f a)) a))
  (epsilon : Π b : τ B, τ (@= B (f (g b)) b))
  [a : τ A]
  [b : τ B]
  (p : τ (@= B (f a) b))
  : τ (@PathOver
      A
      (λ z : τ A, @= B (f z) b)
      (g b)
      a
      (@qinv_fibre_base_path A B f g eta a b p)
      (@half_adjoint_counit A B f g eta epsilon b)
      p)
≔ @ind_eql
    B
    (f a)
    (λ b : τ B,
      λ p : τ (@= B (f a) b),
        @PathOver
          A
          (λ z : τ A, @= B (f z) b)
          (g b)
          a
          (@qinv_fibre_base_path A B f g eta a b p)
          (@half_adjoint_counit A B f g eta epsilon b)
          p)
    (@eq_sym
      (@= B (f (g (f a))) (f a))
      (@eq_ap A B f (g (f a)) a (eta a))
      (@half_adjoint_counit A B f g eta epsilon (f a))
      (@half_adjoint_triangle A B f g eta epsilon a))
    b
    p;

// Every fibre point equals the adjusted half-adjoint centre.
symbol qinv_fibre_contr_path
  [A B : Grpd]
  (f : τ A → τ B)
  (g : τ B → τ A)
  (eta : Π a : τ A, τ (@= A (g (f a)) a))
  (epsilon : Π b : τ B, τ (@= B (f (g b)) b))
  [b : τ B]
  (h : τ (@HFiber A B f b))
  : τ (@=
      (@HFiber A B f b)
      (@Struct_sigma
        A
        (λ a : τ A, @= B (f a) b)
        (g b)
        (@half_adjoint_counit A B f g eta epsilon b))
      h)
≔ @sigma_ind
    A
    (λ a : τ A, @= B (f a) b)
    (λ h : τ (@HFiber A B f b),
      @=
        (@HFiber A B f b)
        (@Struct_sigma
          A
          (λ a : τ A, @= B (f a) b)
          (g b)
          (@half_adjoint_counit A B f g eta epsilon b))
        h)
    (λ a : τ A,
      λ p : τ (@= B (f a) b),
        @Struct_sigma
          (@= A (g b) a)
          (λ q : τ (@= A (g b) a),
            @PathOver
              A
              (λ z : τ A, @= B (f z) b)
              (g b)
              a q
              (@half_adjoint_counit A B f g eta epsilon b)
              p)
          (@qinv_fibre_base_path A B f g eta a b p)
          (@qinv_fibre_pathover A B f g eta epsilon a b p))
    h;

// Fully transparent quasi-inverse-to-contractible-fibre theorem.
symbol is_equiv_map_by_inverse_adjusted
  [A B : Grpd]
  [f : τ A → τ B]
  [g : τ B → τ A]
  (q : τ (@EquivByInverse A B f g))
  : τ (@IsEquivMap A B f)
≔ λ b : τ B,
    @Struct_sigma
      (@HFiber A B f b)
      (λ centre : τ (@HFiber A B f b),
        @Pi_grpd
          (@HFiber A B f b)
          (λ h : τ (@HFiber A B f b),
            @= (@HFiber A B f b) centre h))
      (@Struct_sigma
        A
        (λ a : τ A, @= B (f a) b)
        (g b)
        (@half_adjoint_counit
          A B f g (sigma_Fst q) (sigma_Snd q) b))
      (λ h : τ (@HFiber A B f b),
        @qinv_fibre_contr_path
          A B f g (sigma_Fst q) (sigma_Snd q) b h);

// Re-centre a contractible classifier at any specified point.
symbol is_contr_recenter
  [X : Grpd]
  (c : τ (IsContr X))
  (x : τ X)
  : τ (IsContr X)
≔ @Struct_sigma
    X
    (λ centre : τ X,
      @Pi_grpd X (λ y : τ X, @= X centre y))
    x
    (λ y : τ X,
      @eq_trans
        X
        x
        (is_contr_center c)
        y
        (@eq_sym X (is_contr_center c) x (is_contr_path c x))
        (is_contr_path c y));

// Transparent theorem with the legacy selected centre preserved exactly.
symbol is_equiv_map_by_inverse
  [A B : Grpd]
  [f : τ A → τ B]
  [g : τ B → τ A]
  (q : τ (@EquivByInverse A B f g))
  : τ (@IsEquivMap A B f)
≔ λ b : τ B,
    @is_contr_recenter
      (@HFiber A B f b)
      (@is_equiv_map_by_inverse_adjusted A B f g q b)
      (@Struct_sigma
        A
        (λ a : τ A, @= B (f a) b)
        (g b)
        ((sigma_Snd q) b));


/*
  Ordinary algebra of type equivalences.

  Symmetry and composition derive their contractible-fibre evidence from the
  selected inverse maps and propositional round trips already exposed by
  TypeEquiv. The public packages are transparent Sigma values. Therefore
  forward maps and selected inverse/right-path projections compute, while no
  package eta or inverse-law runtime cancellation is introduced.
*/

// Specified inverse data for the inverse of a type equivalence.
symbol type_equiv_sym_by_inverse
  [A B : Grpd]
  (e : τ (TypeEquiv A B))
  : τ (@EquivByInverse
      B
      A
      (λ b : τ B, type_equiv_from e b)
      (λ a : τ A, type_equiv_to e a))
≔ @Product_pair_grpd
    (@Pi_grpd B
      (λ b : τ B,
        type_equiv_to e (type_equiv_from e b) = b))
    (@Pi_grpd A
      (λ a : τ A,
        type_equiv_from e (type_equiv_to e a) = a))
    (λ b : τ B, type_equiv_right e b)
    (λ a : τ A, type_equiv_left e a);

// The selected inverse map of an equivalence is itself an equivalence map.
symbol type_equiv_sym_is_equiv
  [A B : Grpd]
  (e : τ (TypeEquiv A B))
  : τ (@IsEquivMap
      B
      A
      (λ b : τ B, type_equiv_from e b))
≔ @is_equiv_map_by_inverse
    B
    A
    (λ b : τ B, type_equiv_from e b)
    (λ a : τ A, type_equiv_to e a)
    (@type_equiv_sym_by_inverse A B e);

// Symmetry/inversion of a type equivalence.
symbol type_equiv_sym
  [A B : Grpd]
  (e : τ (TypeEquiv A B))
  : τ (TypeEquiv B A)
≔ @Struct_sigma
    (Function_grpd B A)
    (λ f : τ (Function_grpd B A), @IsEquivMap B A f)
    (λ b : τ B, type_equiv_from e b)
    (@type_equiv_sym_is_equiv A B e);

// Left inverse path for a composite eBC o eAB.
symbol type_equiv_comp_left
  [A B C : Grpd]
  (eBC : τ (TypeEquiv B C))
  (eAB : τ (TypeEquiv A B))
  (a : τ A)
  : τ (
      type_equiv_from eAB
        (type_equiv_from eBC
          (type_equiv_to eBC (type_equiv_to eAB a)))
      = a)
≔ @eq_trans
    A
    (type_equiv_from eAB
      (type_equiv_from eBC
        (type_equiv_to eBC (type_equiv_to eAB a))))
    (type_equiv_from eAB (type_equiv_to eAB a))
    a
    (@eq_ap
      B
      A
      (λ b : τ B, type_equiv_from eAB b)
      (type_equiv_from eBC
        (type_equiv_to eBC (type_equiv_to eAB a)))
      (type_equiv_to eAB a)
      (type_equiv_left eBC (type_equiv_to eAB a)))
    (type_equiv_left eAB a);

// Right inverse path for a composite eBC o eAB.
symbol type_equiv_comp_right
  [A B C : Grpd]
  (eBC : τ (TypeEquiv B C))
  (eAB : τ (TypeEquiv A B))
  (c : τ C)
  : τ (
      type_equiv_to eBC
        (type_equiv_to eAB
          (type_equiv_from eAB (type_equiv_from eBC c)))
      = c)
≔ @eq_trans
    C
    (type_equiv_to eBC
      (type_equiv_to eAB
        (type_equiv_from eAB (type_equiv_from eBC c))))
    (type_equiv_to eBC (type_equiv_from eBC c))
    c
    (@eq_ap
      B
      C
      (λ b : τ B, type_equiv_to eBC b)
      (type_equiv_to eAB
        (type_equiv_from eAB (type_equiv_from eBC c)))
      (type_equiv_from eBC c)
      (type_equiv_right eAB (type_equiv_from eBC c)))
    (type_equiv_right eBC c);

// Specified inverse data for composition, in categorical order eBC o eAB.
symbol type_equiv_comp_by_inverse
  [A B C : Grpd]
  (eBC : τ (TypeEquiv B C))
  (eAB : τ (TypeEquiv A B))
  : τ (@EquivByInverse
      A
      C
      (λ a : τ A,
        type_equiv_to eBC (type_equiv_to eAB a))
      (λ c : τ C,
        type_equiv_from eAB (type_equiv_from eBC c)))
≔ @Product_pair_grpd
    (@Pi_grpd A
      (λ a : τ A,
        type_equiv_from eAB
          (type_equiv_from eBC
            (type_equiv_to eBC (type_equiv_to eAB a)))
        = a))
    (@Pi_grpd C
      (λ c : τ C,
        type_equiv_to eBC
          (type_equiv_to eAB
            (type_equiv_from eAB (type_equiv_from eBC c)))
        = c))
    (λ a : τ A, @type_equiv_comp_left A B C eBC eAB a)
    (λ c : τ C, @type_equiv_comp_right A B C eBC eAB c);

// A composite of equivalence maps is an equivalence map.
symbol type_equiv_comp_is_equiv
  [A B C : Grpd]
  (eBC : τ (TypeEquiv B C))
  (eAB : τ (TypeEquiv A B))
  : τ (@IsEquivMap
      A
      C
      (λ a : τ A,
        type_equiv_to eBC (type_equiv_to eAB a)))
≔ @is_equiv_map_by_inverse
    A
    C
    (λ a : τ A,
      type_equiv_to eBC (type_equiv_to eAB a))
    (λ c : τ C,
      type_equiv_from eAB (type_equiv_from eBC c))
    (@type_equiv_comp_by_inverse A B C eBC eAB);

// Composition of type equivalences, in categorical order eBC o eAB.
symbol type_equiv_comp
  [A B C : Grpd]
  (eBC : τ (TypeEquiv B C))
  (eAB : τ (TypeEquiv A B))
  : τ (TypeEquiv A C)
≔ @Struct_sigma
    (Function_grpd A C)
    (λ f : τ (Function_grpd A C), @IsEquivMap A C f)
    (λ a : τ A,
      type_equiv_to eBC (type_equiv_to eAB a))
    (@type_equiv_comp_is_equiv A B C eBC eAB);

// The Pi happly/funext round trips as specified-inverse evidence.
symbol pi_happly_by_inverse
  [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  : τ (@EquivByInverse
      (@= (@Pi_grpd A B) f g)
      (@PiPointwisePath A B f g)
      (@PiHapplyMap A B f g)
      (@PiFunextMap A B f g))
≔ @Product_pair_grpd
    (@Pi_grpd
      (@= (@Pi_grpd A B) f g)
      (λ p : τ (@= (@Pi_grpd A B) f g),
        @PiFunext A B f g (@PiHapply A B f g p) = p))
    (@Pi_grpd
      (@PiPointwisePath A B f g)
      (λ h : τ (@PiPointwisePath A B f g),
        @PiHapply A B f g (@PiFunext A B f g h) = h))
    (λ p : τ (@= (@Pi_grpd A B) f g),
      @pi_funext_eta A B f g p)
    (λ h : τ (@PiPointwisePath A B f g),
      @pi_happly_beta A B f g h);

// Contractible-fibre evidence for the diagonal Pi path observation.
symbol pi_happly_is_equiv
  [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  : τ (@IsEquivMap
      (@= (@Pi_grpd A B) f g)
      (@PiPointwisePath A B f g)
      (@PiHapplyMap A B f g))
≔ @is_equiv_map_by_inverse
    (@= (@Pi_grpd A B) f g)
    (@PiPointwisePath A B f g)
    (@PiHapplyMap A B f g)
    (@PiFunextMap A B f g)
    (@pi_happly_by_inverse A B f g);

// Ordinary HoTT-facing equivalence between structured and pointwise Pi paths.
symbol pi_happly_type_equiv
  [A : Grpd]
  [B : τ A → Grpd]
  [f g : Π x : τ A, τ (B x)]
  : τ (TypeEquiv
      (@= (@Pi_grpd A B) f g)
      (@PiPointwisePath A B f g))
≔ @Struct_sigma
    (Function_grpd
      (@= (@Pi_grpd A B) f g)
      (@PiPointwisePath A B f g))
    (λ m : τ (Function_grpd
        (@= (@Pi_grpd A B) f g)
        (@PiPointwisePath A B f g)),
      @IsEquivMap
        (@= (@Pi_grpd A B) f g)
        (@PiPointwisePath A B f g)
        m)
    (@PiHapplyMap A B f g)
    (@pi_happly_is_equiv A B f g);

// -------------------------------------------------------------------------------------------------
// 2. Core categories
// -------------------------------------------------------------------------------------------------

/*
  Core category interface.

  Surface/formula:
    A : Cat
    Obj(A)                    object classifier of A
    Hom_cat(A,x,y)            hom-category Hom_A(x,y), also written x ->^A y
    Hom(A,x,y)                object/type classifier of Hom_cat(A,x,y)
    id_A(x)                   identity arrow
    comp_fapp0(g,f)           composite g ∘ f
    Op_cat(A)                 A^op
*/
// Meta-level type of categories in the encoded omega-categorical hierarchy.
constant symbol Cat : TYPE;

// Object groupoid/classifier of a category.
symbol Obj : Cat → Grpd;

// Iterated hom-category `Hom_A(X,Y)`.
injective symbol Hom_cat : Π (A : Cat) (X_A Y_A : τ (Obj A)), Cat;

// Object/type classifier of a hom-category.
injective symbol Hom (A : Cat) (X_A Y_A : τ (Obj A)) : Grpd
≔ Obj (Hom_cat A X_A Y_A);

/*
  Inference-helper policy:
  These unification rules are local elaboration aids for chosen heads such as
  `Hom_cat`, `Functor_cat`, and `Transf_cat`. They should be read as controlled
  "associativity of Obj" hints, not as global semantic injectivity claims for
  arbitrary category constructors.
*/
// Proof-time inversion for object classifiers of two rigid hom-category heads.
unif_rule Obj (Hom_cat $A $X $Y) ≡ Obj (Hom_cat $A' $X' $Y') ↪ [ $A ≡ $A'; $X ≡ $X'; $Y ≡ $Y' ];

// Identity arrow `id_X : Hom_A(X,X)`.
injective symbol id : Π (A : Cat), Π (X_A: τ (Obj A)), τ (Hom A X_A X_A);

// Ordinary composition `g o f : Hom_A(X,Z)`.
symbol comp_fapp0 : Π [A : Cat], Π [X_A Y_A : τ (Obj A)], Π [Z_A: τ (Obj A)],
  Π (g: τ (Hom A Y_A Z_A)), Π (f: τ (Hom A X_A Y_A)),
  τ (Hom A X_A Z_A);

/*
  Proof-time associativity of ordinary categorical composition.

  This unification equation guides elaboration between the two bracketings; it
  is not a runtime arrow rewrite. Keep inferred endpoint slots anonymous in
  generic composition rules below: explicit reducible endpoints can interact
  badly with this proof-time equation even when they are semantically
  reconstructible from the action terms.
*/
unif_rule @comp_fapp0 $C $w $y $z $h
    (@comp_fapp0 $C $w $x $y $g $f)
  ≡ @comp_fapp0 $C $w $x $z
    (@comp_fapp0 $C $x $y $z $h $g)
    $f
  ↪ [ tt ≡ tt ];

// Propositional associativity witness, implemented by the proof-time equation.
symbol comp_assoc
  [C : Cat]
  [w x y z : τ (Obj C)]
  (h : τ (Hom C y z))
  (g : τ (Hom C x y))
  (f : τ (Hom C w x))
  : τ (
      @comp_fapp0 C w y z h
        (@comp_fapp0 C w x y g f)
      =
      @comp_fapp0 C w x z
        (@comp_fapp0 C x y z h g)
        f)
≔ eq_refl
    (@comp_fapp0 C w y z h
      (@comp_fapp0 C w x y g f));

// Opposite category.
injective symbol Op_cat : Cat → Cat;

// Opposite involution: `(A^op)^op = A`.
rule Op_cat (Op_cat $A) ↪ $A;

// Opposite preserves the object classifier.
rule Obj (Op_cat $A) ↪ Obj $A;

// Opposite reverses hom endpoints.
rule Hom_cat (Op_cat $A) $X $Y ↪ Hom_cat $A $Y $X;

// Identity is unchanged under the opposite presentation.
rule @id (Op_cat $A) $X ↪ @id $A $X;

// Opposite composition reverses the ordered pair of factors.
rule @comp_fapp0 (Op_cat $A) $X $Y $Z $g $f ↪ @comp_fapp0 $A $Z $Y $X $f $g;

// Path categories internalize HoTT equality as a groupoidal category.
//
// Surface/formula:
//   Path_cat(A) has objects x : A and arrows p : x = y.
injective symbol Path_cat : Grpd → Cat;

// Objects of `Path(A)` are elements of A.
rule Obj (Path_cat $A) ↪ $A;

// Hom categories in `Path(A)` are path categories of equality groupoids.
rule Hom_cat (Path_cat $A) $x $y ↪ Path_cat ($x = $y);

// Path-category identity is reflexivity.
rule @id (Path_cat $A) $x ↪ eq_refl $x;

// Path-category composition retains the shared generic `comp_fapp0` head.
// J-derived `eq_trans` is a propositionally agreeing operation, not its
// runtime normal form.

// `Path_cat(A)^op` remains a genuine opposite presentation. A later symmetry
// functor supplies endpoint reversal without collapsing the category heads.

// Core groupoid of objects of a category.
//
// Surface/formula:
//   Core_cat(C) = Path_cat(Obj(C)).
symbol Core_cat (C : Cat) : Cat ≔ Path_cat (Obj C);

/*
  Path-category computation laws.

  Surface/formula:
    Obj(Path(A)) = A
    Hom_Path(A)(x,y) = Path(x,y)
    id_x = refl_x
    q ∘ p is owned by generic category composition and propositionally
            agrees with eq_trans(p,q)
*/

// -------------------------------------------------------------------------------------------------
// 3. Functor, displayed-family, and universe categories
// -------------------------------------------------------------------------------------------------

// 3a. Ordinary functor classifier and action
/*
  Ordinary functor category and classifier.

  Surface/formula:
    Functor_cat(A,B)       = A ⊢ B
    Functor(A,B)           = Obj(A ⊢ B)
    F[x]                   = fapp0 F x
    F[X,Y]                 = fapp1_func F : Hom_A(X,Y) ⊢ Hom_B(F[X],F[Y])
    F[f]                   = fapp1_fapp0 F f
*/
injective symbol Functor_cat : Π (A B : Cat), Cat;

// Object/type classifier of the ordinary functor category.
injective symbol Functor (A B : Cat) : Grpd
≔ Obj (Functor_cat A B);

// Proof-time inversion for object classifiers of two rigid functor categories.
unif_rule Obj (Functor_cat $A $B) ≡ Obj (Functor_cat $A' $B') ↪ [ $A ≡ $A'; $B ≡ $B' ];

/*
  Mathematical notation:
    F : A ⊢ B                 means F : Functor(A,B)
    F[x]                      = fapp0 F x
    F₁[X,Y]                   = fapp1_func F : Hom_A(X,Y) ⊢ Hom_B(F[X],F[Y])
    F[f]                      = fapp1_fapp0 F f
*/
symbol fapp0 : Π [A B : Cat], Π (F_AB : τ (Functor A B)),
  τ (Obj A) → τ (Obj B);

// Full hom-category action `F_1[X,Y]` before capping at one arrow.
symbol fapp1_func : Π [A B : Cat], Π (F_AB : τ (Functor A B)),
  Π [X_A Y_A : τ (Obj A)],
  τ (Functor (Hom_cat A X_A Y_A) (Hom_cat B (fapp0 F_AB X_A) (fapp0 F_AB Y_A)));

// Capped arrow action of a functor: F[f].
symbol fapp1_fapp0 : Π [A B : Cat], Π (F_AB : τ (Functor A B)),
  Π [X_A Y_A : τ (Obj A)],
  Π (f : τ (Hom A X_A Y_A)),
  τ (Hom B (fapp0 F_AB X_A) (fapp0 F_AB Y_A));

// Projection beta: applying the full hom action yields capped arrow action.
rule fapp0 (fapp1_func $F_AB) $f ↪ fapp1_fapp0 $F_AB $f;

// Strict functoriality, oriented as cut elimination.
rule @fapp1_fapp0 $A $B $F $X $X (@id $A $X)
  ↪ @id $B (@fapp0 $A $B $F $X);

// Projection-order bridge for the canonicalized identity of an opposite
// source category: id_(K^op) has already reduced to id_K.
// lhs-audit: keep 1 -- Op_cat is the measured source discriminator after the
// identity argument loses its literal opposite-category owner.
rule @fapp1_fapp0
      (Op_cat $K) $D $F $x $x (@id $K $x)
  ↪ @id $D (@fapp0 (Op_cat $K) $D $F $x);

// Strict composition cut: `F[g] o F[f] -> F[g o f]`.
rule @comp_fapp0
      $B
      _
      _
      _
      (@fapp1_fapp0 $A $B $F $Y $Z $g)
      (@fapp1_fapp0 $A $B $F $X $Y $f)
  ↪ @fapp1_fapp0
      $A
      $B
      $F
      $X
      $Z
      (@comp_fapp0 $A $X $Y $Z $g $f);

// Typed equality view of the generic strict composition cut.
symbol fapp1_comp_path
  [A B : Cat]
  (F : τ (Functor A B))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y))
  : τ (@=
      (Hom B (@fapp0 A B F X) (@fapp0 A B F Z))
      (@fapp1_fapp0 A B F X Z
        (@comp_fapp0 A X Y Z g f))
      (@comp_fapp0
        B
        (@fapp0 A B F X)
        (@fapp0 A B F Y)
        (@fapp0 A B F Z)
        (@fapp1_fapp0 A B F Y Z g)
        (@fapp1_fapp0 A B F X Y f)))
≔ @eq_refl
    (Hom B (@fapp0 A B F X) (@fapp0 A B F Z))
    (@fapp1_fapp0 A B F X Z
      (@comp_fapp0 A X Y Z g f));

/*
  Path-symmetry functor owner.

  The functor, rather than a second standalone composition calculus, owns
  strict path reversal. Generic functoriality therefore supplies the
  anti-composition computation after `path_sym` unfolds to arrow action.
*/
injective symbol Path_sym_func
  (A : Grpd)
  : τ (Functor (Op_cat (Path_cat A)) (Path_cat A));

// Path symmetry fixes objects.
rule @fapp0 _ _ (Path_sym_func _) $x ↪ $x;

// Stable path-symmetry view of the functor's arrow action.
symbol path_sym
  [A : Grpd]
  [x y : τ A]
  (p : τ (x = y))
  : τ (y = x)
≔ @fapp1_fapp0
    (Op_cat (Path_cat A))
    (Path_cat A)
    (Path_sym_func A)
    y x p;

// Projection-order identity bridge after Path_cat identity exposes eq_refl.
// lhs-audit: keep 1,2 -- measured opposite/path category discriminators reduce
// four downstream overlap reports versus inferred slots.
rule @fapp1_fapp0
      (Op_cat (Path_cat $A))
      (Path_cat $A)
      (Path_sym_func $A)
      $x $x
      (@eq_refl $A $x)
  ↪ @eq_refl $A $x;

// Closed shaped-reflexivity registration for PathSym. Keep the rigid source
// and target categories: as for the literal-reflexivity bridge above, they
// exclude ill-typed displayed/product target matches from the overlap set.
// lhs-audit: keep 1,2 -- measured rigid PathSym categories are warning guards.
rule @fapp1_fapp0
      (Op_cat (Path_cat (PathRecord_grpd $A)))
      (Path_cat (PathRecord_grpd $A))
      (Path_sym_func (PathRecord_grpd $A))
      $r $r
      (@PathRecordPathRefl $A $r)
  ↪ @PathRecordPathRefl $A $r;

// J-derived symmetry is a propositional semantic reference, not a runtime
// fold for the strict functor action.
symbol path_sym_agrees_eq_sym
  [A : Grpd]
  [x y : τ A]
  (p : τ (x = y))
  : τ (@path_sym A x y p = @eq_sym A x y p)
≔ @ind_eqr A y
    (λ x : τ A, λ p : τ (x = y),
      @path_sym A x y p = @eq_sym A x y p)
    (eq_refl (eq_refl y))
    x p;

// Initial involution is propositional; no broad runtime
// path_sym(path_sym(p)) cancellation is selected.
symbol path_sym_invol
  [A : Grpd]
  [x y : τ A]
  (p : τ (x = y))
  : τ (
      @path_sym A y x (@path_sym A x y p)
      = p)
≔ @ind_eqr A y
    (λ x : τ A, λ p : τ (x = y),
      @path_sym A y x (@path_sym A x y p) = p)
    (eq_refl (eq_refl y))
    x p;

/*
  Core inclusion and path-to-arrow.

  `Core_incl_func(C) : Core_cat(C) ⊢ C` owns the computational map from
  non-directed object paths to directed arrows. Composition is deliberately
  not restated here: the generic `fapp1_fapp0` functoriality rule folds
  path_to_hom(q) ∘ path_to_hom(p) to path_to_hom(q ∘ p), retaining the
  shared `comp_fapp0(Path_cat(...))` source-composition head.

  The reflexivity bridge is a measured projection-ladder join. `Path_cat`
  reduces identity arrows to `eq_refl` before the generic functor-identity
  rule can see the literal `id`, so this focused rule restores the intended
  normal form without adding a second composition owner.
*/
injective symbol Core_incl_func
  (C : Cat)
  : τ (Functor (Core_cat C) C);

// Object beta for the inclusion of the path core.
rule @fapp0 _ _ (Core_incl_func _) $x ↪ $x;

// Reflexive path maps to the categorical identity arrow.
rule @fapp1_fapp0 _ _ (Core_incl_func $C) $x $x (eq_refl $x)
  ↪ @id $C $x;

// Closed shaped-reflexivity registration for the generic Core inclusion.
rule @fapp1_fapp0
      _ _
      (Core_incl_func $C)
      $r $r
      (@PathRecordPathRefl _ $r)
  ↪ @id $C $r;

// Read a path in `Obj(C)` as the corresponding arrow through the core inclusion.
symbol path_to_hom
  [C : Cat]
  [x y : τ (Obj C)]
  (p : τ (x = y))
  : τ (Hom C x y)
≔ @fapp1_fapp0
    (Core_cat C)
    C
    (Core_incl_func C)
    x y p;

// Pointwise arrow form of the Core-inclusion/opposite square. Functor-level
// packaging is deliberately deferred; the computational owner remains the
// generic action of Core_incl_func and Path_sym_func.
symbol path_sym_core_incl_agreement
  [C : Cat]
  [x y : τ (Obj C)]
  (p : τ (x = y))
  : τ (@=
      (Hom C x y)
      (@path_to_hom (Op_cat C) y x
        (@path_sym (Obj C) x y p))
      (@path_to_hom C x y p))
≔ @ind_eqr (Obj C) y
    (λ x : τ (Obj C), λ p : τ (x = y),
      @=
        (Hom C x y)
        (@path_to_hom (Op_cat C) y x
          (@path_sym (Obj C) x y p))
        (@path_to_hom C x y p))
    (eq_refl (@id C y))
    x p;

// -------------------------------------------------------------------------------------------------
// 3b. Ordinary categorical isomorphism evidence
// -------------------------------------------------------------------------------------------------

/*
  Ordinary categorical isomorphism evidence.

  This is propositional data: a forward arrow, an inverse arrow, and equality
  paths witnessing both inverse equations. It does not claim judgmental
  cancellation.
*/
symbol IsoEvidence
  (C : Cat)
  (x y : τ (Obj C))
  : Grpd
≔ `Σ_ to : τ (Hom C x y),
   `Σ_ from : τ (Hom C y x),
   `Σ_ _ : τ (
      @comp_fapp0 C x y x from to
        =
      @id C x),
      @comp_fapp0 C y x y to from
        =
      @id C y;

// Forward-arrow projection of ordinary isomorphism evidence.
symbol iso_evidence_to
  [C : Cat]
  [x y : τ (Obj C)]
  (i : τ (IsoEvidence C x y))
  : τ (Hom C x y)
≔ sigma_Fst i;

// Inverse-arrow projection of ordinary isomorphism evidence.
symbol iso_evidence_from
  [C : Cat]
  [x y : τ (Obj C)]
  (i : τ (IsoEvidence C x y))
  : τ (Hom C y x)
≔ sigma_Fst (sigma_Snd i);

// Left inverse path: `from(i) o to(i) = id_x`.
symbol iso_evidence_left
  [C : Cat]
  [x y : τ (Obj C)]
  (i : τ (IsoEvidence C x y))
  : τ (
      @comp_fapp0 C x y x
        (iso_evidence_from i)
        (iso_evidence_to i)
      =
      @id C x)
≔ sigma_Fst (sigma_Snd (sigma_Snd i));

// Right inverse path: `to(i) o from(i) = id_y`.
symbol iso_evidence_right
  [C : Cat]
  [x y : τ (Obj C)]
  (i : τ (IsoEvidence C x y))
  : τ (
      @comp_fapp0 C y x y
        (iso_evidence_to i)
        (iso_evidence_from i)
      =
      @id C y)
≔ sigma_Snd (sigma_Snd (sigma_Snd i));

// Symmetry swaps the two arrows and the two inverse witnesses.
symbol iso_evidence_sym
  [C : Cat]
  [x y : τ (Obj C)]
  (i : τ (IsoEvidence C x y))
  : τ (IsoEvidence C y x)
≔ Struct_sigma
    (iso_evidence_from i)
    (Struct_sigma
      (iso_evidence_to i)
      (Struct_sigma
        (iso_evidence_right i)
        (iso_evidence_left i)));

// 3c. Universe categories
/*
  Universe classifiers and their category structures.

  Surface/formula:
    Grpd_cat has Obj(Grpd_cat) = Grpd and homs are ordinary functions.
    Cat_cat  has Obj(Cat_cat)  = Cat  and Hom(A,B) = A ⊢ B.
*/

// Category of groupoid/type classifiers.
constant symbol Grpd_cat : Cat;

// Object classifier of `Grpd_cat`, definitionally the groupoid universe.
injective symbol Grpd_grpd : Grpd ≔ Obj Grpd_cat;

// Universe-object decoding: `Obj(Grpd_cat)` decodes to `Grpd`.
rule τ (Obj Grpd_cat) ↪ Grpd;

/*
  Function-path hom boundary for the groupoid universe.

  The whole hom-category is the path category of ordinary functions. Stable
  semantic heads expose pointwise identity/composition computation; the
  category-level owners compare with them only at proof time.
*/
rule Hom_cat Grpd_cat $A $B
  ↪ Path_cat (@Function_grpd $A $B);

// Pointwise identity function as the stable comparison target.
injective symbol grpd_id_function
  (A : Grpd)
  : τ (@Function_grpd A A);

rule @grpd_id_function _ $a ↪ $a;

// Pointwise composition as the stable comparison target.
injective symbol grpd_comp_function
  [A B C : Grpd]
  (g : τ (@Function_grpd B C))
  (f : τ (@Function_grpd A B))
  : τ (@Function_grpd A C);

rule @grpd_comp_function _ _ _ $g $f $a ↪ $g ($f $a);

// Proof-time comparisons; neither side is selected as the other's runtime
// normal form.
unif_rule
  @id Grpd_cat $A
  ≡ @grpd_id_function $A
  ↪ [ tt ≡ tt ];

unif_rule
  @comp_fapp0 Grpd_cat $A $B $C $g $f
  ≡ @grpd_comp_function $A $B $C $g $f
  ↪ [ tt ≡ tt ];

// Capped evaluation of categorical function composition. No whole-term fold
// to grpd_comp_function is installed; application computes pointwise. Under
// eta_equality, conversion can consequently observe the same lambda function.
rule @comp_fapp0 Grpd_cat _ _ _ $g $f $x
  ↪ $g ($f $x);

/*
  Named groupoid-universe identity view.

  This is the finite fallback boundary for Phase 13: public universe equality
  remains opaque, while the view exposes exactly the existing TypeEquiv data.
  Encode/decode below route through the canonical groupoid decoder.
*/
symbol GrpdPathView
  (A B : Grpd)
  : Grpd
≔ TypeEquiv A B;

// Canonical reflexivity of the universe identity view.
symbol grpd_path_refl
  (A : Grpd)
  : τ (GrpdPathView A A)
≔ @type_equiv_refl A;

// Classifier of one-step truncation weakening at a fixed level.
symbol TruncMonotonicity
  (n : TruncLevel)
  : Grpd
≔ @Pi_grpd
    Grpd_grpd
    (λ A : Grpd,
      @Function_grpd
        (IsTruncGrpd n A)
        (IsTruncGrpd (trunc_succ n) A));

// Level-recursive monotonicity: n-truncated implies (n+1)-truncated.
symbol is_trunc_grpd_succ
  (n : TruncLevel)
  : τ (TruncMonotonicity n)
≔ @ind_TruncLevel
    (λ n : TruncLevel, TruncMonotonicity n)
    (λ A : Grpd, λ h : τ (IsTruncGrpd trunc_minus_two A),
      @is_contr_is_prop A h)
    (λ n : TruncLevel,
      λ ih : τ (TruncMonotonicity n),
      λ A : Grpd,
      λ h : τ (IsTruncGrpd (trunc_succ n) A),
      λ x : τ A,
      λ y : τ A,
        ih (@= A x y) (h x y))
    n;

// Homs in `Grpd_cat` decode to ordinary functions.
rule τ (Obj (Hom_cat Grpd_cat $X $Y)) ↪ (τ $X → τ $Y);

// Transport an element along equality of groupoid classifiers.
symbol coe_grpd
  [A B : Grpd]
  (p : τ (@= Grpd_grpd A B))
  (a : τ A)
  : τ B;

// Transport along reflexivity is the identity on elements.
rule @coe_grpd $A $A (eq_refl $A) $a ↪ $a;

// Convert equality of groupoid classifiers to a type equivalence.
symbol idtoequiv_grpd
  [A B : Grpd]
  (p : τ (@= Grpd_grpd A B))
  : τ (TypeEquiv A B);

// Reflexive universe equality decodes to reflexive type equivalence.
rule @idtoequiv_grpd $A $A (eq_refl $A)
  ↪ @type_equiv_refl $A;

// Observe a public universe path through the named identity view.
symbol grpd_path_encode
  [A B : Grpd]
  (p : τ (@= Grpd_grpd A B))
  : τ (GrpdPathView A B)
≔ @idtoequiv_grpd A B p;

// Transport along any universe path agrees propositionally with the forward
// map of its canonical idtoequiv image.
symbol coe_grpd_idtoequiv
  [A B : Grpd]
  (p : τ (@= Grpd_grpd A B))
  (a : τ A)
  : τ (
      @coe_grpd A B p a
      = type_equiv_to (@idtoequiv_grpd A B p) a)
≔ @ind_eqr
    Grpd_grpd
    B
    (λ A : Grpd, λ p : τ (@= Grpd_grpd A B),
      @Pi_grpd A
        (λ a : τ A,
          @coe_grpd A B p a
          = type_equiv_to (@idtoequiv_grpd A B p) a))
    (λ b : τ B, @eq_refl B b)
    A
    p
    a;

// Componentwise path view between two groupoid-level product classifiers.
symbol ProductGrpdPathView
  [A A' B B' : Grpd]
  : Grpd
≔ `Σ_ pA : τ (@= Grpd_grpd A A'),
   @PathOver Grpd_grpd (λ _ : Grpd, Grpd_grpd) A A' pA B B';

// A componentwise product-universe path is an introduction form. It is not an
// eliminator for arbitrary univalent paths
// Product_grpd(A,B) = Product_grpd(A',B').
symbol product_grpd_path
  [A A' B B' : Grpd]
  (pA : τ (@= Grpd_grpd A A'))
  (pB : τ (@PathOver Grpd_grpd (λ _ : Grpd, Grpd_grpd) A A' pA B B'))
  : τ (@= Grpd_grpd (Product_grpd A B) (Product_grpd A' B'));

// Univalence capability: `idtoequiv_grpd` is an equivalence for all A,B.
symbol GrpdUnivalence : Grpd
≔ @Pi_grpd Grpd_grpd
    (λ A : Grpd,
      @Pi_grpd Grpd_grpd
        (λ B : Grpd,
          @IsEquivMap
            (@= Grpd_grpd A B)
            (TypeEquiv A B)
            (λ p : τ (@= Grpd_grpd A B), @idtoequiv_grpd A B p)));

// Decode a type equivalence to universe equality using a univalence capability.
symbol ua_grpd
  (U : τ GrpdUnivalence)
  [A B : Grpd]
  (e : τ (TypeEquiv A B))
  : τ (@= Grpd_grpd A B);

// Computational univalence beta: transport along `ua(e)` applies `e.to`.
rule @coe_grpd $A $B (@ua_grpd _ $A $B $e) $a
  ↪ type_equiv_to $e $a;

// Selected decoder from type equivalence to groupoid-universe equality.
symbol grpd_equiv_path
  [A B : Grpd]
  (e : τ (TypeEquiv A B))
  : τ (@= Grpd_grpd A B);

// Decoder beta on reflexive type equivalence.
rule @grpd_equiv_path $A $A (@type_equiv_refl $A)
  ↪ eq_refl $A;

// Decoder for product equivalence builds the componentwise product path.
rule @grpd_equiv_path
      (Product_grpd $A $B)
      (Product_grpd $A' $B')
      (@product_type_equiv $A $A' $B $B' $eA $eB)
  ↪ @product_grpd_path
      $A
      $A'
      $B
      $B'
      (@grpd_equiv_path $A $A' $eA)
      (@const_pathover
        Grpd_grpd
        Grpd_grpd
        $A
        $A'
        $B
        $B'
        (@grpd_equiv_path $A $A' $eA)
        (@grpd_equiv_path $B $B' $eB));

// Encoding a componentwise product path yields the componentwise equivalence.
rule @idtoequiv_grpd
      (Product_grpd $A $B)
      (Product_grpd $A' $B')
      (@product_grpd_path $A $A' $B $B' $pA $pB)
  ↪ @product_type_equiv
      $A
      $A'
      $B
      $B'
      (@idtoequiv_grpd $A $A' $pA)
      (@idtoequiv_grpd
        $B
        $B'
        (@const_pathover_path
          Grpd_grpd
          Grpd_grpd
          $A
          $A'
          $B
          $B'
          $pA
          $pB));

// Reconstruct public universe equality through the canonical decoder owner.
symbol grpd_path_decode
  [A B : Grpd]
  (e : τ (GrpdPathView A B))
  : τ (@= Grpd_grpd A B)
≔ @grpd_equiv_path A B e;

// Specified-inverse presentation of groupoid univalence via the selected decoder.
symbol GrpdUnivalenceByDecoder : Grpd
≔ @Pi_grpd Grpd_grpd
    (λ A : Grpd,
      @Pi_grpd Grpd_grpd
        (λ B : Grpd,
          @EquivByInverse
            (@= Grpd_grpd A B)
            (TypeEquiv A B)
            (λ p : τ (@= Grpd_grpd A B), @idtoequiv_grpd A B p)
            (λ e : τ (TypeEquiv A B), @grpd_equiv_path A B e)));

// Global decoder-oriented groupoid-univalence capability.
symbol grpd_univalence_by_decoder
  : τ GrpdUnivalenceByDecoder;

/*
  Groupoid decoder coherence.

  The global decoder-oriented capability is the proof authority for the two
  round trips. It also derives a canonical contractible-fibre univalence
  capability whose selected inverse is definitionally grpd_equiv_path. The
  legacy ua_grpd(U,e) head remains an arbitrary-capability compatibility
  facade; new coherence consumers use the one operational decoder instead of
  postulating agreement for every unrelated U.
*/

// Contractible-fibre univalence derived from the operational decoder package.
symbol grpd_univalence_from_decoder
  : τ GrpdUnivalence
≔ λ A : Grpd, λ B : Grpd,
    @is_equiv_map_by_inverse
      (@= Grpd_grpd A B)
      (TypeEquiv A B)
      (λ p : τ (@= Grpd_grpd A B), @idtoequiv_grpd A B p)
      (λ e : τ (TypeEquiv A B), @grpd_equiv_path A B e)
      (grpd_univalence_by_decoder A B);

// Ordinary TypeEquiv packaging of the canonical ambient decoder capability.
symbol grpd_univalence_type_equiv
  [A B : Grpd]
  : τ (TypeEquiv (@= Grpd_grpd A B) (TypeEquiv A B))
≔ @Struct_sigma
    (Function_grpd (@= Grpd_grpd A B) (TypeEquiv A B))
    (λ f : τ (Function_grpd (@= Grpd_grpd A B) (TypeEquiv A B)),
      @IsEquivMap (@= Grpd_grpd A B) (TypeEquiv A B) f)
    (λ p : τ (@= Grpd_grpd A B), @idtoequiv_grpd A B p)
    (grpd_univalence_from_decoder A B);

// The inverse selected by the derived capability is the operational decoder.
symbol grpd_univalence_selected_path
  [A B : Grpd]
  (e : τ (TypeEquiv A B))
  : τ (@= Grpd_grpd A B)
≔ @hfiber_point
    (@= Grpd_grpd A B)
    (TypeEquiv A B)
    (λ p : τ (@= Grpd_grpd A B), @idtoequiv_grpd A B p)
    e
    (@is_contr_center
      (@HFiber
        (@= Grpd_grpd A B)
        (TypeEquiv A B)
        (λ p : τ (@= Grpd_grpd A B), @idtoequiv_grpd A B p)
        e)
      (@is_equiv_fiber
        (@= Grpd_grpd A B)
        (TypeEquiv A B)
        (λ p : τ (@= Grpd_grpd A B), @idtoequiv_grpd A B p)
        (grpd_univalence_from_decoder A B)
        e));

// Decoder after encoder is propositionally the original universe path.
symbol grpd_equiv_path_idtoequiv
  [A B : Grpd]
  (p : τ (@= Grpd_grpd A B))
  : τ (
      @grpd_equiv_path A B (@idtoequiv_grpd A B p)
      = p)
≔ (sigma_Fst (grpd_univalence_by_decoder A B)) p;

// Encoder after decoder is propositionally the original type equivalence.
symbol idtoequiv_grpd_equiv_path
  [A B : Grpd]
  (e : τ (TypeEquiv A B))
  : τ (
      @idtoequiv_grpd A B (@grpd_equiv_path A B e)
      = e)
≔ (sigma_Snd (grpd_univalence_by_decoder A B)) e;

// Transport along the operational decoder agrees propositionally with e.to.
// This is not a runtime rule: the rejected orientation competes with the
// existing Product decoder path before Product-path transport is available.
symbol grpd_equiv_path_coe
  [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (a : τ A)
  : τ (
      @coe_grpd A B (@grpd_equiv_path A B e) a
      = type_equiv_to e a)
≔ @eq_trans
    B
    (@coe_grpd A B (@grpd_equiv_path A B e) a)
    (type_equiv_to
      (@idtoequiv_grpd A B (@grpd_equiv_path A B e))
      a)
    (type_equiv_to e a)
    (@coe_grpd_idtoequiv
      A B
      (@grpd_equiv_path A B e)
      a)
    (@eq_ap
      (TypeEquiv A B)
      B
      (λ d : τ (TypeEquiv A B), type_equiv_to d a)
      (@idtoequiv_grpd A B (@grpd_equiv_path A B e))
      e
      (@idtoequiv_grpd_equiv_path A B e));

// Nontrivial Pi-universe action induced by the decoder transport square.
symbol grpd_equiv_path_pi_action
  [A : Grpd]
  [B C : τ A → Grpd]
  (e : Π x : τ A, τ (TypeEquiv (B x) (C x)))
  (f : τ (@Pi_grpd A B))
  (x : τ A)
  : τ (
      (@coe_grpd
        (@Pi_grpd A B)
        (@Pi_grpd A C)
        (@grpd_equiv_path
          (@Pi_grpd A B)
          (@Pi_grpd A C)
          (@pi_type_equiv_same_domain A B C e))
        f)
        x
      = type_equiv_to (e x) (f x))
≔ @eq_ap
    (@Pi_grpd A C)
    (C x)
    (λ h : τ (@Pi_grpd A C), h x)
    (@coe_grpd
      (@Pi_grpd A B)
      (@Pi_grpd A C)
      (@grpd_equiv_path
        (@Pi_grpd A B)
        (@Pi_grpd A C)
        (@pi_type_equiv_same_domain A B C e))
      f)
    (type_equiv_to (@pi_type_equiv_same_domain A B C e) f)
    (@grpd_equiv_path_coe
      (@Pi_grpd A B)
      (@Pi_grpd A C)
      (@pi_type_equiv_same_domain A B C e)
      f);

// Decoding after encoding is propositionally the original universe path.
symbol grpd_path_decode_encode
  [A B : Grpd]
  (p : τ (@= Grpd_grpd A B))
  : τ (
      @grpd_path_decode A B (@grpd_path_encode A B p)
      = p)
≔ @grpd_equiv_path_idtoequiv A B p;

// Encoding after decoding is propositionally the original identity view.
symbol grpd_path_encode_decode
  [A B : Grpd]
  (e : τ (GrpdPathView A B))
  : τ (
      @grpd_path_encode A B (@grpd_path_decode A B e)
      = e)
≔ @idtoequiv_grpd_equiv_path A B e;

// Transport along a decoded identity view agrees propositionally with its
// forward map; the existing decoder square remains the semantic owner.
symbol grpd_path_decode_coe
  [A B : Grpd]
  (e : τ (GrpdPathView A B))
  (a : τ A)
  : τ (
      @coe_grpd A B (@grpd_path_decode A B e) a
      = type_equiv_to e a)
≔ @grpd_equiv_path_coe A B e a;

/*
  Truncation invariance under ordinary type equivalence.

  The promoted operational decoder turns `e : A ~= B` into one universe path.
  Applying `IsTruncGrpd(n,-)` to that path and decoding it again supplies a
  canonical equivalence between the two evidence classifiers. This is general
  groupoid/type equivalence invariance only; categorical/OmegaEquiv invariance
  and the recursive IsNCat object-truncation theorem remain separate.
*/
// Universe path between truncation-evidence classifiers induced by e.
symbol is_trunc_grpd_equiv_path
  [n : TruncLevel]
  [A B : Grpd]
  (e : τ (TypeEquiv A B))
  : τ (@= Grpd_grpd (IsTruncGrpd n A) (IsTruncGrpd n B))
≔ @eq_ap
    Grpd_grpd
    Grpd_grpd
    (λ X : Grpd, IsTruncGrpd n X)
    A
    B
    (@grpd_equiv_path A B e);

// Canonical equivalence between truncation-evidence classifiers.
symbol is_trunc_grpd_type_equiv
  [n : TruncLevel]
  [A B : Grpd]
  (e : τ (TypeEquiv A B))
  : τ (TypeEquiv (IsTruncGrpd n A) (IsTruncGrpd n B))
≔ @idtoequiv_grpd
    (IsTruncGrpd n A)
    (IsTruncGrpd n B)
    (@is_trunc_grpd_equiv_path n A B e);

// Transport truncation evidence forward along an ordinary type equivalence.
symbol is_trunc_grpd_equiv_to
  [n : TruncLevel]
  [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (h : τ (IsTruncGrpd n A))
  : τ (IsTruncGrpd n B)
≔ type_equiv_to (@is_trunc_grpd_type_equiv n A B e) h;

// Transport truncation evidence backward along an ordinary type equivalence.
symbol is_trunc_grpd_equiv_from
  [n : TruncLevel]
  [A B : Grpd]
  (e : τ (TypeEquiv A B))
  (h : τ (IsTruncGrpd n B))
  : τ (IsTruncGrpd n A)
≔ type_equiv_from (@is_trunc_grpd_type_equiv n A B e) h;

/*
  Arbitrary-level dependent-Pi truncation closure.

  Contractible Pi is the base. At a successor, the recursive theorem truncates
  the pointwise path Pi and general TypeEquiv invariance transports that result
  back along PiHapply/PiFunext. A stable recursive head exposes only bounded
  base/successor consumer equations.
*/
// Classifier of dependent-Pi preservation at one truncation level.
symbol PiTruncClosure
  (n : TruncLevel)
  : Grpd
≔ @Pi_grpd Grpd_grpd
    (λ A : Grpd,
      @Pi_grpd
        (@Pi_grpd A (λ _ : τ A, Grpd_grpd))
        (λ B : τ A → Grpd,
          @Function_grpd
            (@Pi_grpd A
              (λ x : τ A,
                IsTruncGrpd n (B x)))
            (IsTruncGrpd n (@Pi_grpd A B))));

// Successor closure through the pointwise Pi path equivalence.
symbol trunc_pi_succ
  (n : TruncLevel)
  (rec : τ (PiTruncClosure n))
  (A : Grpd)
  (B : τ A → Grpd)
  (h : Π x : τ A, τ (IsTruncGrpd (trunc_succ n) (B x)))
  : τ (IsTruncGrpd (trunc_succ n) (@Pi_grpd A B))
≔ λ f : τ (@Pi_grpd A B), λ g : τ (@Pi_grpd A B),
    @is_trunc_grpd_equiv_from
      n
      (@= (@Pi_grpd A B) f g)
      (@PiPointwisePath A B f g)
      (@pi_happly_type_equiv A B f g)
      (rec
        A
        (λ x : τ A, @= (B x) (f x) (g x))
        (λ x : τ A, h x (f x) (g x)));

// Stable recursive owner for arbitrary-level dependent-Pi preservation.
injective symbol is_trunc_pi
  (n : TruncLevel)
  : τ (PiTruncClosure n);

// Compute only when the closure theorem is consumed by a family/evidence.
rule @is_trunc_pi trunc_minus_two $A $B $h
  ↪ @is_contr_pi $A $B $h
with @is_trunc_pi (trunc_succ $n) $A $B $h
  ↪ @trunc_pi_succ
      $n
      (@is_trunc_pi $n)
      $A
      $B
      $h;

/*
  Same-level dependent-Sigma truncation closure.

  Contractible total space is the base. At a successor, Sigma equality is the
  base-path/fibre-PathOver total; the recursive theorem applies because base
  paths and transported fibre paths are both truncated one level lower. A
  stable recursive head exposes only bounded base/successor consumers.
*/
// Classifier of same-level dependent-Sigma preservation.
symbol SigmaTruncClosure
  (n : TruncLevel)
  : Grpd
≔ @Pi_grpd Grpd_grpd
    (λ A : Grpd,
      @Pi_grpd
        (@Pi_grpd A (λ _ : τ A, Grpd_grpd))
        (λ B : τ A → Grpd,
          @Function_grpd
            (IsTruncGrpd n A)
            (@Function_grpd
              (@Pi_grpd A
                (λ x : τ A, IsTruncGrpd n (B x)))
              (IsTruncGrpd n (@Σ_ A B)))));

// Successor closure through the base-path/fibre-PathOver Sigma view.
symbol trunc_sigma_succ
  (n : TruncLevel)
  (rec : τ (SigmaTruncClosure n))
  (A : Grpd)
  (B : τ A → Grpd)
  (hA : τ (IsTruncGrpd (trunc_succ n) A))
  (hB : Π x : τ A, τ (IsTruncGrpd (trunc_succ n) (B x)))
  : τ (IsTruncGrpd (trunc_succ n) (@Σ_ A B))
≔ λ u : @τΣ_ A B, λ v : @τΣ_ A B,
    rec
      (@= A (sigma_Fst u) (sigma_Fst v))
      (λ p : τ (@= A (sigma_Fst u) (sigma_Fst v)),
        @PathOver
          A
          B
          (sigma_Fst u)
          (sigma_Fst v)
          p
          (sigma_Snd u)
          (sigma_Snd v))
      (hA (sigma_Fst u) (sigma_Fst v))
      (λ p : τ (@= A (sigma_Fst u) (sigma_Fst v)),
        hB
          (sigma_Fst u)
          (sigma_Snd u)
          (@ind_eq
            A
            (sigma_Fst u)
            (sigma_Fst v)
            p
            B
            (sigma_Snd v)));

// Stable recursive owner for same-level dependent-Sigma preservation.
injective symbol is_trunc_sigma
  (n : TruncLevel)
  : τ (SigmaTruncClosure n);

// Compute only when the closure theorem is consumed by both hypotheses.
rule @is_trunc_sigma trunc_minus_two $A $B $hA $hB
  ↪ @is_contr_sigma $A $B $hA $hB
with @is_trunc_sigma (trunc_succ $n) $A $B $hA $hB
  ↪ @trunc_sigma_succ
      $n
      (@is_trunc_sigma $n)
      $A
      $B
      $hA
      $hB;

/*
  Property-valued truncation evidence: Pi closure and level recursion.

  The transparent generated TruncLevel recursor inhabits the theorem, but a
  successor conversion probe exceeds the bounded check because it unfolds the
  reducible Pi/equivalence motive. The selected stable theorem head therefore
  owns two disjoint consumer equations. They expose only the intended base or
  successor helper and add no proof-time equation.
*/
// Proposition-valued dependent products from pointwise proposition evidence.
symbol is_prop_pi
  [A : Grpd]
  [B : τ A → Grpd]
  (h : Π x : τ A, τ (IsPropGrpd (B x)))
  : τ (IsPropGrpd (@Pi_grpd A B))
≔ @is_trunc_pi trunc_minus_one A B h;

/*
  Same-level truncation of ordinary type equivalences.

  For the contractible base, every function between contractible classifiers
  has the constant inverse at the source centre. Equivalence-map evidence is
  proposition-valued, so the function space and its evidence fibres are both
  contractible. At a successor level, the function space inherits the target
  bound and the evidence fibre is raised from proposition-valuedness. Source
  truncation is therefore used only by the contractible base.
*/
// Any map between contractible classifiers has a specified constant inverse.
symbol contractible_map_by_inverse
  [A B : Grpd]
  (hA : τ (IsContr A))
  (hB : τ (IsContr B))
  (f : τ A → τ B)
  : τ (@EquivByInverse
      A B f (λ _ : τ B, is_contr_center hA))
≔ @Product_pair_grpd
    (@Pi_grpd A
      (λ a : τ A,
        @= A (is_contr_center hA) a))
    (@Pi_grpd B
      (λ b : τ B,
        @= B (f (is_contr_center hA)) b))
    (λ a : τ A, is_contr_path hA a)
    (λ b : τ B,
      @contractible_path_center B hB (f (is_contr_center hA)) b);

// Every map between contractible classifiers is an equivalence map.
symbol contractible_map_is_equiv
  [A B : Grpd]
  (hA : τ (IsContr A))
  (hB : τ (IsContr B))
  (f : τ A → τ B)
  : τ (@IsEquivMap A B f)
≔ @is_equiv_map_by_inverse
    A B f
    (λ _ : τ B, is_contr_center hA)
    (@contractible_map_by_inverse A B hA hB f);

// Equivalence-map evidence is proposition-valued for every map.
symbol is_equiv_map_evidence_is_prop
  [A B : Grpd]
  (f : τ A → τ B)
  : τ (IsPropGrpd (@IsEquivMap A B f))
≔ @is_prop_pi
    B
    (λ b : τ B, IsContr (@HFiber A B f b))
    (λ b : τ B,
      @is_contr_evidence_is_prop (@HFiber A B f b));

// For contractible endpoints, equivalence-map evidence is contractible.
symbol is_equiv_map_evidence_is_contr
  [A B : Grpd]
  (hA : τ (IsContr A))
  (hB : τ (IsContr B))
  (f : τ A → τ B)
  : τ (IsContr (@IsEquivMap A B f))
≔ @Struct_sigma
    (@IsEquivMap A B f)
    (λ e : τ (@IsEquivMap A B f),
      @Pi_grpd
        (@IsEquivMap A B f)
        (λ d : τ (@IsEquivMap A B f),
          @= (@IsEquivMap A B f) e d))
    (@contractible_map_is_equiv A B hA hB f)
    (λ e : τ (@IsEquivMap A B f),
      is_contr_center
        (@is_equiv_map_evidence_is_prop A B f
          (@contractible_map_is_equiv A B hA hB f)
          e));

// TypeEquiv(A,B) is contractible when both endpoints are contractible.
symbol contractible_type_equiv
  [A B : Grpd]
  (hA : τ (IsContr A))
  (hB : τ (IsContr B))
  : τ (IsContr (TypeEquiv A B))
≔ @is_contr_sigma
    (Function_grpd A B)
    (λ f : τ (Function_grpd A B), @IsEquivMap A B f)
    (@is_contr_pi A (λ _ : τ A, B) (λ _ : τ A, hB))
    (λ f : τ A → τ B,
      @is_equiv_map_evidence_is_contr A B hA hB f);

// Proposition-valued classifiers remain truncated at every successor level.
symbol prop_is_trunc_succ
  (n : TruncLevel)
  [A : Grpd]
  (h : τ (IsPropGrpd A))
  : τ (IsTruncGrpd (trunc_succ n) A)
≔ @ind_TruncLevel
    (λ n : TruncLevel,
      @Function_grpd
        (IsPropGrpd A)
        (IsTruncGrpd (trunc_succ n) A))
    (λ h : τ (IsPropGrpd A), h)
    (λ n : TruncLevel,
      λ ih : τ (@Function_grpd
          (IsPropGrpd A)
          (IsTruncGrpd (trunc_succ n) A)),
      λ h : τ (IsPropGrpd A),
        @is_trunc_grpd_succ
          (trunc_succ n)
          A
          (ih h))
    n
    h;

// Successor TypeEquiv closure uses target truncation and evidence property.
symbol trunc_type_equiv_succ
  (n : TruncLevel)
  [A B : Grpd]
  (hB : τ (IsTruncGrpd (trunc_succ n) B))
  : τ (IsTruncGrpd
      (trunc_succ n)
      (TypeEquiv A B))
≔ @is_trunc_sigma
    (trunc_succ n)
    (Function_grpd A B)
    (λ f : τ (Function_grpd A B), @IsEquivMap A B f)
    (@is_trunc_pi
      (trunc_succ n)
      A
      (λ _ : τ A, B)
      (λ _ : τ A, hB))
    (λ f : τ A → τ B,
      @prop_is_trunc_succ
        n
        (@IsEquivMap A B f)
        (@is_equiv_map_evidence_is_prop A B f));

// Classifier of same-level truncation closure for ordinary type equivalence.
symbol TypeEquivTruncClosure
  (n : TruncLevel)
  : Grpd
≔ @Pi_grpd Grpd_grpd
    (λ A : Grpd,
      @Pi_grpd Grpd_grpd
        (λ B : Grpd,
          @Function_grpd
            (IsTruncGrpd n A)
            (@Function_grpd
              (IsTruncGrpd n B)
              (IsTruncGrpd n (TypeEquiv A B)))));

// Stable recursive owner for TypeEquiv truncation at every level.
injective symbol is_trunc_type_equiv
  (n : TruncLevel)
  : τ (TypeEquivTruncClosure n);

// The contractible base uses both endpoints; the successor needs only B.
rule @is_trunc_type_equiv trunc_minus_two $A $B $hA $hB
  ↪ @contractible_type_equiv $A $B $hA $hB
with @is_trunc_type_equiv (trunc_succ $n) $A $B _ $hB
  ↪ @trunc_type_equiv_succ $n $A $B $hB;

// Classifier of the level-indexed evidence-property theorem.
symbol TruncEvidenceProp
  (n : TruncLevel)
  : Grpd
≔ @Pi_grpd Grpd_grpd
    (λ A : Grpd,
      IsPropGrpd (IsTruncGrpd n A));

// Successor helper: apply proposition-valued Pi closure at both path indices.
symbol trunc_evidence_prop_succ
  (n : TruncLevel)
  (ih : τ (TruncEvidenceProp n))
  (A : Grpd)
  : τ (IsPropGrpd (IsTruncGrpd (trunc_succ n) A))
≔ @is_prop_pi
    A
    (λ x : τ A,
      @Pi_grpd A
        (λ y : τ A,
          IsTruncGrpd n (@= A x y)))
    (λ x : τ A,
      @is_prop_pi
        A
        (λ y : τ A,
          IsTruncGrpd n (@= A x y))
        (λ y : τ A,
          ih (@= A x y)));

// Stable recursive owner: truncation evidence is proposition-valued.
injective symbol is_trunc_grpd_evidence_is_prop
  (n : TruncLevel)
  : τ (TruncEvidenceProp n);

// The theorem computes only when consumed at a classifier.
rule @is_trunc_grpd_evidence_is_prop trunc_minus_two $A
  ↪ @is_contr_evidence_is_prop $A
with @is_trunc_grpd_evidence_is_prop (trunc_succ $n) $A
  ↪ @trunc_evidence_prop_succ
      $n
      (@is_trunc_grpd_evidence_is_prop $n)
      $A;

/*
  Paths in the packaged truncated universes.

  A package path is observed by a carrier path plus a dependent path between
  the retained evidence fields. Since truncation evidence is proposition-
  valued, every carrier path supplies that second component. The resulting
  carrier-path projection is an ordinary TypeEquiv; its round trips remain
  propositional and no package eta or restricted-univalence rule is added.
*/
// Carrier path together with the dependent path between retained evidence.
symbol TruncGrpdPathView
  (n : TruncLevel)
  (X Y : τ (TruncGrpdU n))
  : Grpd
≔ `Σ_ p : τ (@= Grpd_grpd
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y)),
    @PathOver
      Grpd_grpd
      (λ A : Grpd, IsTruncGrpd n A)
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y)
      p
      (trunc_grpd_evidence X)
      (trunc_grpd_evidence Y);

// Reflexive carrier/evidence path view.
symbol trunc_grpd_path_refl
  [n : TruncLevel]
  (X : τ (TruncGrpdU n))
  : τ (TruncGrpdPathView n X X)
≔ @Struct_sigma
    (@= Grpd_grpd
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier X))
    (λ p : τ (@= Grpd_grpd
        (trunc_grpd_carrier X)
        (trunc_grpd_carrier X)),
      @PathOver
        Grpd_grpd
        (λ A : Grpd, IsTruncGrpd n A)
        (trunc_grpd_carrier X)
        (trunc_grpd_carrier X)
        p
        (trunc_grpd_evidence X)
        (trunc_grpd_evidence X))
    (@eq_refl Grpd_grpd (trunc_grpd_carrier X))
    (@pathover_refl
      Grpd_grpd
      (λ A : Grpd, IsTruncGrpd n A)
      (trunc_grpd_carrier X)
      (trunc_grpd_evidence X));

// Build equality of constructor packages from both field paths.
symbol trunc_grpd_path_intro
  [n : TruncLevel]
  [A B : Grpd]
  [hA : τ (IsTruncGrpd n A)]
  [hB : τ (IsTruncGrpd n B)]
  (p : τ (@= Grpd_grpd A B))
  (q : τ (@PathOver
      Grpd_grpd
      (λ X : Grpd, IsTruncGrpd n X)
      A
      B
      p
      hA
      hB))
  : τ (@= (TruncGrpdU n)
      (@Struct_trunc_grpd n A hA)
      (@Struct_trunc_grpd n B hB))
≔ @ind_eqr
    Grpd_grpd
    B
    (λ A : Grpd, λ p : τ (@= Grpd_grpd A B),
      @Pi_grpd (IsTruncGrpd n A)
        (λ hA : τ (IsTruncGrpd n A),
          @Pi_grpd (IsTruncGrpd n B)
            (λ hB : τ (IsTruncGrpd n B),
              @Pi_grpd
                (@PathOver
                  Grpd_grpd
                  (λ X : Grpd, IsTruncGrpd n X)
                  A
                  B
                  p
                  hA
                  hB)
                (λ _ : τ (@PathOver
                    Grpd_grpd
                    (λ X : Grpd, IsTruncGrpd n X)
                    A
                    B
                    p
                    hA
                    hB),
                  @= (TruncGrpdU n)
                    (@Struct_trunc_grpd n A hA)
                    (@Struct_trunc_grpd n B hB)))))
    (λ hA : τ (IsTruncGrpd n B),
      λ hB : τ (IsTruncGrpd n B),
      λ q : τ (@= (IsTruncGrpd n B) hA hB),
        @eq_ap
          (IsTruncGrpd n B)
          (TruncGrpdU n)
          (λ h : τ (IsTruncGrpd n B),
            @Struct_trunc_grpd n B h)
          hA
          hB
          q)
    A
    p
    hA
    hB
    q;

// Decode the carrier/evidence view to package equality.
symbol trunc_grpd_path_decode
  [n : TruncLevel]
  [X Y : τ (TruncGrpdU n)]
  (w : τ (TruncGrpdPathView n X Y))
  : τ (@= (TruncGrpdU n) X Y)
≔ @trunc_grpd_ind
    n
    (λ X : τ (TruncGrpdU n),
      @Pi_grpd (TruncGrpdU n)
        (λ Y : τ (TruncGrpdU n),
          @Pi_grpd (TruncGrpdPathView n X Y)
            (λ _ : τ (TruncGrpdPathView n X Y),
              @= (TruncGrpdU n) X Y)))
    (λ A : Grpd,
      λ hA : τ (IsTruncGrpd n A),
        @trunc_grpd_ind
          n
          (λ Y : τ (TruncGrpdU n),
            @Pi_grpd
              (TruncGrpdPathView
                n
                (@Struct_trunc_grpd n A hA)
                Y)
              (λ _ : τ (TruncGrpdPathView
                  n
                  (@Struct_trunc_grpd n A hA)
                  Y),
                @= (TruncGrpdU n)
                  (@Struct_trunc_grpd n A hA)
                  Y))
          (λ B : Grpd,
            λ hB : τ (IsTruncGrpd n B),
            λ w : τ (TruncGrpdPathView
                n
                (@Struct_trunc_grpd n A hA)
                (@Struct_trunc_grpd n B hB)),
              @trunc_grpd_path_intro
                n
                A
                B
                hA
                hB
                (sigma_Fst w)
                (sigma_Snd w)))
    X
    Y
    w;

// Encode a generic package equality into its carrier/evidence path view.
symbol trunc_grpd_path_encode
  [n : TruncLevel]
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= (TruncGrpdU n) X Y))
  : τ (TruncGrpdPathView n X Y)
≔ @ind_eqr
    (TruncGrpdU n)
    Y
    (λ X : τ (TruncGrpdU n),
      λ _ : τ (@= (TruncGrpdU n) X Y),
        TruncGrpdPathView n X Y)
    (@trunc_grpd_path_refl n Y)
    X
    p;

// Decoding the reflexive view gives generic package reflexivity.
symbol trunc_grpd_path_decode_refl
  [n : TruncLevel]
  (X : τ (TruncGrpdU n))
  : τ (@=
      (@= (TruncGrpdU n) X X)
      (@trunc_grpd_path_decode
        n
        X
        X
        (@trunc_grpd_path_refl n X))
      (@eq_refl (TruncGrpdU n) X))
≔ @trunc_grpd_ind
    n
    (λ X : τ (TruncGrpdU n),
      @=
        (@= (TruncGrpdU n) X X)
        (@trunc_grpd_path_decode
          n
          X
          X
          (@trunc_grpd_path_refl n X))
        (@eq_refl (TruncGrpdU n) X))
    (λ A : Grpd,
      λ h : τ (IsTruncGrpd n A),
        @eq_refl
          (@= (TruncGrpdU n)
            (@Struct_trunc_grpd n A h)
            (@Struct_trunc_grpd n A h))
          (@eq_refl
            (TruncGrpdU n)
            (@Struct_trunc_grpd n A h)))
    X;

// Decoding after encoding is propositionally the original package path.
symbol trunc_grpd_path_decode_encode
  [n : TruncLevel]
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= (TruncGrpdU n) X Y))
  : τ (@=
      (@= (TruncGrpdU n) X Y)
      (@trunc_grpd_path_decode
        n
        X
        Y
        (@trunc_grpd_path_encode n X Y p))
      p)
≔ @ind_eqr
    (TruncGrpdU n)
    Y
    (λ X : τ (TruncGrpdU n),
      λ p : τ (@= (TruncGrpdU n) X Y),
        @=
          (@= (TruncGrpdU n) X Y)
          (@trunc_grpd_path_decode
            n
            X
            Y
            (@trunc_grpd_path_encode n X Y p))
          p)
    (@trunc_grpd_path_decode_refl n Y)
    X
    p;

// Carrier projection of a package equality.
symbol trunc_grpd_carrier_path
  [n : TruncLevel]
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= (TruncGrpdU n) X Y))
  : τ (@= Grpd_grpd
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y))
≔ @eq_ap
    (TruncGrpdU n)
    Grpd_grpd
    (λ Z : τ (TruncGrpdU n), trunc_grpd_carrier Z)
    X
    Y
    p;

// Constructor decoding projects back to its supplied carrier path.
symbol trunc_grpd_path_intro_carrier
  [n : TruncLevel]
  [A B : Grpd]
  [hA : τ (IsTruncGrpd n A)]
  [hB : τ (IsTruncGrpd n B)]
  (p : τ (@= Grpd_grpd A B))
  (q : τ (@PathOver
      Grpd_grpd
      (λ X : Grpd, IsTruncGrpd n X)
      A B p hA hB))
  : τ (@=
      (@= Grpd_grpd A B)
      (@trunc_grpd_carrier_path
        n
        (@Struct_trunc_grpd n A hA)
        (@Struct_trunc_grpd n B hB)
        (@trunc_grpd_path_intro n A B hA hB p q))
      p)
≔ @ind_eqr
    Grpd_grpd
    B
    (λ A : Grpd, λ p : τ (@= Grpd_grpd A B),
      @Pi_grpd (IsTruncGrpd n A) (λ hA : τ (IsTruncGrpd n A),
        @Pi_grpd (IsTruncGrpd n B) (λ hB : τ (IsTruncGrpd n B),
          @Pi_grpd
            (@PathOver
              Grpd_grpd
              (λ X : Grpd, IsTruncGrpd n X)
              A B p hA hB)
            (λ q : τ (@PathOver
                Grpd_grpd
                (λ X : Grpd, IsTruncGrpd n X)
                A B p hA hB),
              @=
                (@= Grpd_grpd A B)
                (@trunc_grpd_carrier_path
                  n
                  (@Struct_trunc_grpd n A hA)
                  (@Struct_trunc_grpd n B hB)
                  (@trunc_grpd_path_intro
                    n A B hA hB p q))
                p))))
    (λ hA : τ (IsTruncGrpd n B),
      λ hB : τ (IsTruncGrpd n B),
      λ q : τ (@= (IsTruncGrpd n B) hA hB),
        @ind_eqr
          (IsTruncGrpd n B)
          hB
          (λ hA : τ (IsTruncGrpd n B),
            λ q : τ (@= (IsTruncGrpd n B) hA hB),
              @=
                (@= Grpd_grpd B B)
                (@trunc_grpd_carrier_path
                  n
                  (@Struct_trunc_grpd n B hA)
                  (@Struct_trunc_grpd n B hB)
                  (@trunc_grpd_path_intro
                    n
                    B
                    B
                    hA
                    hB
                    (@eq_refl Grpd_grpd B)
                    q))
                (@eq_refl Grpd_grpd B))
          (@eq_refl
            (@= Grpd_grpd B B)
            (@eq_refl Grpd_grpd B))
          hA
          q)
    A
    p
    hA
    hB
    q;

// Decoding any path view projects to its base carrier path.
symbol trunc_grpd_path_decode_carrier
  [n : TruncLevel]
  [X Y : τ (TruncGrpdU n)]
  (w : τ (TruncGrpdPathView n X Y))
  : τ (@=
      (@= Grpd_grpd
        (trunc_grpd_carrier X)
        (trunc_grpd_carrier Y))
      (@trunc_grpd_carrier_path
        n
        X
        Y
        (@trunc_grpd_path_decode n X Y w))
      (sigma_Fst w))
≔ @trunc_grpd_ind
    n
    (λ X : τ (TruncGrpdU n),
      @Pi_grpd (TruncGrpdU n) (λ Y : τ (TruncGrpdU n),
        @Pi_grpd (TruncGrpdPathView n X Y)
          (λ w : τ (TruncGrpdPathView n X Y),
            @=
              (@= Grpd_grpd
                (trunc_grpd_carrier X)
                (trunc_grpd_carrier Y))
              (@trunc_grpd_carrier_path
                n X Y (@trunc_grpd_path_decode n X Y w))
              (sigma_Fst w))))
    (λ A : Grpd,
      λ hA : τ (IsTruncGrpd n A),
        @trunc_grpd_ind
          n
          (λ Y : τ (TruncGrpdU n),
            @Pi_grpd
              (TruncGrpdPathView
                n
                (@Struct_trunc_grpd n A hA)
                Y)
              (λ w : τ (TruncGrpdPathView
                  n
                  (@Struct_trunc_grpd n A hA)
                  Y),
                @=
                  (@= Grpd_grpd A (trunc_grpd_carrier Y))
                  (@trunc_grpd_carrier_path
                    n
                    (@Struct_trunc_grpd n A hA)
                    Y
                    (@trunc_grpd_path_decode
                      n
                      (@Struct_trunc_grpd n A hA)
                      Y
                      w))
                  (sigma_Fst w)))
          (λ B : Grpd,
            λ hB : τ (IsTruncGrpd n B),
            λ w : τ (TruncGrpdPathView
                n
                (@Struct_trunc_grpd n A hA)
                (@Struct_trunc_grpd n B hB)),
              @trunc_grpd_path_intro_carrier
                n
                A
                B
                hA
                hB
                (sigma_Fst w)
                (sigma_Snd w)))
    X
    Y
    w;

// Proposition-valued evidence supplies the dependent field path over p.
symbol trunc_grpd_evidence_pathover
  [n : TruncLevel]
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= Grpd_grpd
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y)))
  : τ (@PathOver
      Grpd_grpd
      (λ A : Grpd, IsTruncGrpd n A)
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y)
      p
      (trunc_grpd_evidence X)
      (trunc_grpd_evidence Y))
≔ is_contr_center
    (@is_trunc_grpd_evidence_is_prop
      n
      (trunc_grpd_carrier X)
      (trunc_grpd_evidence X)
      (@ind_eq
        Grpd_grpd
        (trunc_grpd_carrier X)
        (trunc_grpd_carrier Y)
        p
        (λ A : Grpd, IsTruncGrpd n A)
        (trunc_grpd_evidence Y)));

// Reconstruct a package path from only its carrier path.
symbol trunc_grpd_path_from_carrier
  [n : TruncLevel]
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= Grpd_grpd
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y)))
  : τ (@= (TruncGrpdU n) X Y)
≔ @trunc_grpd_path_decode
    n
    X
    Y
    (@Struct_sigma
      (@= Grpd_grpd
        (trunc_grpd_carrier X)
        (trunc_grpd_carrier Y))
      (λ q : τ (@= Grpd_grpd
          (trunc_grpd_carrier X)
          (trunc_grpd_carrier Y)),
        @PathOver
          Grpd_grpd
          (λ A : Grpd, IsTruncGrpd n A)
          (trunc_grpd_carrier X)
          (trunc_grpd_carrier Y)
          q
          (trunc_grpd_evidence X)
          (trunc_grpd_evidence Y))
      p
      (@trunc_grpd_evidence_pathover n X Y p));

// Carrier projection after reconstruction returns the original carrier path.
symbol trunc_grpd_carrier_path_from_carrier
  [n : TruncLevel]
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= Grpd_grpd
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y)))
  : τ (@=
      (@= Grpd_grpd
        (trunc_grpd_carrier X)
        (trunc_grpd_carrier Y))
      (@trunc_grpd_carrier_path
        n X Y (@trunc_grpd_path_from_carrier n X Y p))
      p)
≔ @trunc_grpd_path_decode_carrier
    n
    X
    Y
    (@Struct_sigma
      (@= Grpd_grpd
        (trunc_grpd_carrier X)
        (trunc_grpd_carrier Y))
      (λ q : τ (@= Grpd_grpd
          (trunc_grpd_carrier X)
          (trunc_grpd_carrier Y)),
        @PathOver
          Grpd_grpd
          (λ A : Grpd, IsTruncGrpd n A)
          (trunc_grpd_carrier X)
          (trunc_grpd_carrier Y)
          q
          (trunc_grpd_evidence X)
          (trunc_grpd_evidence Y))
      p
      (@trunc_grpd_evidence_pathover n X Y p));

// Reconstruction at reflexivity is reflexivity for a constructor package.
symbol trunc_grpd_path_from_carrier_refl_struct
  [n : TruncLevel]
  [A : Grpd]
  (h : τ (IsTruncGrpd n A))
  : τ (@=
      (@= (TruncGrpdU n)
        (@Struct_trunc_grpd n A h)
        (@Struct_trunc_grpd n A h))
      (@trunc_grpd_path_from_carrier
        n
        (@Struct_trunc_grpd n A h)
        (@Struct_trunc_grpd n A h)
        (@eq_refl Grpd_grpd A))
      (@eq_refl
        (TruncGrpdU n)
        (@Struct_trunc_grpd n A h)))
≔ @eq_ap
    (@= (IsTruncGrpd n A) h h)
    (@= (TruncGrpdU n)
      (@Struct_trunc_grpd n A h)
      (@Struct_trunc_grpd n A h))
    (λ q : τ (@= (IsTruncGrpd n A) h h),
      @eq_ap
        (IsTruncGrpd n A)
        (TruncGrpdU n)
        (λ k : τ (IsTruncGrpd n A),
          @Struct_trunc_grpd n A k)
        h
        h
        q)
    (is_contr_center
      (@is_trunc_grpd_evidence_is_prop n A h h))
    (@eq_refl (IsTruncGrpd n A) h)
    (is_contr_path
      (@is_trunc_grpd_evidence_is_prop n A h h)
      (@eq_refl (IsTruncGrpd n A) h));

// Reconstruction at reflexivity is reflexivity for every package.
symbol trunc_grpd_path_from_carrier_refl
  [n : TruncLevel]
  (X : τ (TruncGrpdU n))
  : τ (@=
      (@= (TruncGrpdU n) X X)
      (@trunc_grpd_path_from_carrier
        n
        X
        X
        (@eq_refl Grpd_grpd (trunc_grpd_carrier X)))
      (@eq_refl (TruncGrpdU n) X))
≔ @trunc_grpd_ind
    n
    (λ X : τ (TruncGrpdU n),
      @=
        (@= (TruncGrpdU n) X X)
        (@trunc_grpd_path_from_carrier
          n
          X
          X
          (@eq_refl Grpd_grpd (trunc_grpd_carrier X)))
        (@eq_refl (TruncGrpdU n) X))
    (λ A : Grpd,
      λ h : τ (IsTruncGrpd n A),
        @trunc_grpd_path_from_carrier_refl_struct n A h)
    X;

// Reconstruction after carrier projection is propositionally the input path.
symbol trunc_grpd_path_from_carrier_carrier_path
  [n : TruncLevel]
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= (TruncGrpdU n) X Y))
  : τ (@=
      (@= (TruncGrpdU n) X Y)
      (@trunc_grpd_path_from_carrier
        n
        X
        Y
        (@trunc_grpd_carrier_path n X Y p))
      p)
≔ @ind_eqr
    (TruncGrpdU n)
    Y
    (λ X : τ (TruncGrpdU n),
      λ p : τ (@= (TruncGrpdU n) X Y),
        @=
          (@= (TruncGrpdU n) X Y)
          (@trunc_grpd_path_from_carrier
            n
            X
            Y
            (@trunc_grpd_carrier_path n X Y p))
          p)
    (@trunc_grpd_path_from_carrier_refl n Y)
    X
    p;

// Function-valued carrier-path projection.
symbol trunc_grpd_carrier_path_map
  [n : TruncLevel]
  [X Y : τ (TruncGrpdU n)]
  : τ (Function_grpd
      (@= (TruncGrpdU n) X Y)
      (@= Grpd_grpd
        (trunc_grpd_carrier X)
        (trunc_grpd_carrier Y)))
≔ λ p : τ (@= (TruncGrpdU n) X Y),
    @trunc_grpd_carrier_path n X Y p;

// Function-valued reconstruction from a carrier path.
symbol trunc_grpd_path_from_carrier_map
  [n : TruncLevel]
  [X Y : τ (TruncGrpdU n)]
  : τ (Function_grpd
      (@= Grpd_grpd
        (trunc_grpd_carrier X)
        (trunc_grpd_carrier Y))
      (@= (TruncGrpdU n) X Y))
≔ λ p : τ (@= Grpd_grpd
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y)),
    @trunc_grpd_path_from_carrier n X Y p;

// The carrier-path projection and evidence-derived reconstruction are inverse.
symbol trunc_grpd_carrier_path_by_inverse
  [n : TruncLevel]
  [X Y : τ (TruncGrpdU n)]
  : τ (@EquivByInverse
      (@= (TruncGrpdU n) X Y)
      (@= Grpd_grpd
        (trunc_grpd_carrier X)
        (trunc_grpd_carrier Y))
      (@trunc_grpd_carrier_path_map n X Y)
      (@trunc_grpd_path_from_carrier_map n X Y))
≔ @Product_pair_grpd
    (@Pi_grpd
      (@= (TruncGrpdU n) X Y)
      (λ p : τ (@= (TruncGrpdU n) X Y),
        @=
          (@= (TruncGrpdU n) X Y)
          (@trunc_grpd_path_from_carrier
            n X Y (@trunc_grpd_carrier_path n X Y p))
          p))
    (@Pi_grpd
      (@= Grpd_grpd
        (trunc_grpd_carrier X)
        (trunc_grpd_carrier Y))
      (λ p : τ (@= Grpd_grpd
          (trunc_grpd_carrier X)
          (trunc_grpd_carrier Y)),
        @=
          (@= Grpd_grpd
            (trunc_grpd_carrier X)
            (trunc_grpd_carrier Y))
          (@trunc_grpd_carrier_path
            n X Y (@trunc_grpd_path_from_carrier n X Y p))
          p))
    (λ p : τ (@= (TruncGrpdU n) X Y),
      @trunc_grpd_path_from_carrier_carrier_path n X Y p)
    (λ p : τ (@= Grpd_grpd
        (trunc_grpd_carrier X)
        (trunc_grpd_carrier Y)),
      @trunc_grpd_carrier_path_from_carrier n X Y p);

// Contractible-fibre evidence for package-path projection.
symbol trunc_grpd_carrier_path_is_equiv
  [n : TruncLevel]
  [X Y : τ (TruncGrpdU n)]
  : τ (@IsEquivMap
      (@= (TruncGrpdU n) X Y)
      (@= Grpd_grpd
        (trunc_grpd_carrier X)
        (trunc_grpd_carrier Y))
      (@trunc_grpd_carrier_path_map n X Y))
≔ @is_equiv_map_by_inverse
    (@= (TruncGrpdU n) X Y)
    (@= Grpd_grpd
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y))
    (@trunc_grpd_carrier_path_map n X Y)
    (@trunc_grpd_path_from_carrier_map n X Y)
    (@trunc_grpd_carrier_path_by_inverse n X Y);

// Package equality is equivalent to equality of the retained carriers.
symbol trunc_grpd_carrier_path_type_equiv
  [n : TruncLevel]
  [X Y : τ (TruncGrpdU n)]
  : τ (TypeEquiv
      (@= (TruncGrpdU n) X Y)
      (@= Grpd_grpd
        (trunc_grpd_carrier X)
        (trunc_grpd_carrier Y)))
≔ @Struct_sigma
    (Function_grpd
      (@= (TruncGrpdU n) X Y)
      (@= Grpd_grpd
        (trunc_grpd_carrier X)
        (trunc_grpd_carrier Y)))
    (λ f : τ (Function_grpd
        (@= (TruncGrpdU n) X Y)
        (@= Grpd_grpd
          (trunc_grpd_carrier X)
          (trunc_grpd_carrier Y))),
      @IsEquivMap
        (@= (TruncGrpdU n) X Y)
        (@= Grpd_grpd
          (trunc_grpd_carrier X)
          (trunc_grpd_carrier Y))
        f)
    (@trunc_grpd_carrier_path_map n X Y)
    (@trunc_grpd_carrier_path_is_equiv n X Y);

/*
  Restricted univalence for the packaged truncated universes.

  Package equality first projects equivalently to carrier equality; the
  canonical ambient decoder then identifies carrier equality with ordinary
  TypeEquiv data. This composition does not assert direct observational
  universe identity or the (n+1)-truncation theorem for TruncGrpdU(n).
*/
// Package equality is equivalent to ordinary equivalence of its carriers.
symbol trunc_grpd_univalence_type_equiv
  [n : TruncLevel]
  [X Y : τ (TruncGrpdU n)]
  : τ (TypeEquiv
      (@= (TruncGrpdU n) X Y)
      (TypeEquiv
        (trunc_grpd_carrier X)
        (trunc_grpd_carrier Y)))
≔ @type_equiv_comp
    (@= (TruncGrpdU n) X Y)
    (@= Grpd_grpd
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y))
    (TypeEquiv
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y))
    (@grpd_univalence_type_equiv
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y))
    (@trunc_grpd_carrier_path_type_equiv n X Y);

// Encoder from package equality to ordinary carrier equivalence.
symbol trunc_grpd_idtoequiv
  [n : TruncLevel]
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= (TruncGrpdU n) X Y))
  : τ (TypeEquiv
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y))
≔ type_equiv_to (@trunc_grpd_univalence_type_equiv n X Y) p;

// Operational inverse: ambient decoding followed by evidence reconstruction.
symbol trunc_grpd_equiv_path
  [n : TruncLevel]
  [X Y : τ (TruncGrpdU n)]
  (e : τ (TypeEquiv
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y)))
  : τ (@= (TruncGrpdU n) X Y)
≔ type_equiv_from (@trunc_grpd_univalence_type_equiv n X Y) e;

// Decoder after encoder is propositionally the original package path.
symbol trunc_grpd_equiv_path_idtoequiv
  [n : TruncLevel]
  [X Y : τ (TruncGrpdU n)]
  (p : τ (@= (TruncGrpdU n) X Y))
  : τ (@=
      (@= (TruncGrpdU n) X Y)
      (@trunc_grpd_equiv_path
        n X Y (@trunc_grpd_idtoequiv n X Y p))
      p)
≔ type_equiv_left (@trunc_grpd_univalence_type_equiv n X Y) p;

// Encoder after decoder is propositionally the original carrier equivalence.
symbol trunc_grpd_idtoequiv_equiv_path
  [n : TruncLevel]
  [X Y : τ (TruncGrpdU n)]
  (e : τ (TypeEquiv
      (trunc_grpd_carrier X)
      (trunc_grpd_carrier Y)))
  : τ (@=
      (TypeEquiv
        (trunc_grpd_carrier X)
        (trunc_grpd_carrier Y))
      (@trunc_grpd_idtoequiv
        n X Y (@trunc_grpd_equiv_path n X Y e))
      e)
≔ type_equiv_right (@trunc_grpd_univalence_type_equiv n X Y) e;

// Decoding reflexive carrier equivalence is propositionally package reflexivity.
symbol trunc_grpd_equiv_path_refl
  [n : TruncLevel]
  (X : τ (TruncGrpdU n))
  : τ (@=
      (@= (TruncGrpdU n) X X)
      (@trunc_grpd_equiv_path
        n X X (@type_equiv_refl (trunc_grpd_carrier X)))
      (@eq_refl (TruncGrpdU n) X))
≔ @trunc_grpd_path_from_carrier_refl n X;

/*
  Expected truncation level of the packaged truncated universe.

  Restricted package univalence identifies each package path space with the
  TypeEquiv classifier of its n-truncated carriers. Same-level TypeEquiv
  closure therefore makes every package path space n-truncated, hence
  TruncGrpdU(n) is (n+1)-truncated. This is a theorem through the selected
  decoder package, not a same-level claim or direct universe computation.
*/
symbol is_trunc_grpd_universe
  (n : TruncLevel)
  : τ (IsTruncGrpd
      (trunc_succ n)
      (TruncGrpdU n))
≔ λ X : τ (TruncGrpdU n),
   λ Y : τ (TruncGrpdU n),
     @is_trunc_grpd_equiv_from
       n
       (@= (TruncGrpdU n) X Y)
       (TypeEquiv
         (trunc_grpd_carrier X)
         (trunc_grpd_carrier Y))
       (@trunc_grpd_univalence_type_equiv n X Y)
       (@is_trunc_type_equiv
         n
         (trunc_grpd_carrier X)
         (trunc_grpd_carrier Y)
         (trunc_grpd_evidence X)
         (trunc_grpd_evidence Y));

// Category of categories.
constant symbol Cat_cat : Cat;

/*
  Proof-time identity comparison for Cat-valued action from a path category.

  The runtime identity of `Path_cat(A)` exposes `eq_refl(A,x)` before the
  generic functor-identity owner can match. This narrowly typed join restores
  that functorial comparison without selecting a second runtime normal form.
*/
unif_rule
  @fapp1_fapp0 (Path_cat $A) Cat_cat $D $x $x (@eq_refl $A $x)
  ≡ @id Cat_cat (@fapp0 (Path_cat $A) Cat_cat $D $x)
  ↪ [ tt ≡ tt ];

// Object classifier of the category universe.
injective symbol Cat_grpd  : Grpd ≔ Obj Cat_cat;

// Universe-object decoding: `Obj(Cat_cat)` decodes to the meta-type `Cat`.
rule τ (Obj Cat_cat)  ↪ Cat;

// Directed-universe beta: a hom in `Cat_cat` is an ordinary functor category.
rule Hom_cat Cat_cat $X $Y ↪ Functor_cat $X $Y;

/*
  Internal path-category action.

  Path_cat_func[A] = Path_cat(A), and its iterated ordinary functor action
  supplies functions, equalities between functions, and every higher equality
  action without reflecting a directed cell into equality.
*/
injective symbol Path_cat_func
  : τ (Functor Grpd_cat Cat_cat);

// Object projection: Path_cat_func[A] ↪ Path_cat(A).
rule @fapp0 Grpd_cat Cat_cat Path_cat_func $A
  ↪ Path_cat $A;

// Readable first action: a function acts by equality congruence.
symbol path_map_func
  [A B : Grpd]
  (f : τ (@Function_grpd A B))
  : τ (Functor (Path_cat A) (Path_cat B))
≔ @fapp1_fapp0
    Grpd_cat Cat_cat Path_cat_func
    A B f;

// Object action of Path_map(f).
// lhs-audit: keep 1,2 -- the rigid Path_cat endpoints exclude product
// projection overlaps while retaining the intended internal-action owner.
rule @fapp0
      (Path_cat $A) (Path_cat $B)
      (@fapp1_fapp0
        Grpd_cat Cat_cat Path_cat_func
        _ _ $f)
      $x
  ↪ $f $x;

// Full next-hom action of Path_map(f), retaining an iterable path functor.
rule @fapp1_func
      _ _
      (@fapp1_fapp0
        Grpd_cat Cat_cat Path_cat_func
        $A $B $f)
      $x $y
  ↪ @fapp1_fapp0
      Grpd_cat Cat_cat Path_cat_func
      (@= $A $x $y)
      (@= $B ($f $x) ($f $y))
      (λ p : τ (@= $A $x $y),
        @eq_ap $A $B $f $x $y p);

// Capped equality action of Path_map(f).
// lhs-audit: keep 1,2 -- Path_cat guards the generic identity-action overlap.
rule @fapp1_fapp0
      (Path_cat $A) (Path_cat $B)
      (@fapp1_fapp0
        Grpd_cat Cat_cat Path_cat_func
        _ _ $f)
      $x $y $p
  ↪ @eq_ap $A $B $f $x $y $p;

// Canonical off-diagonal equality action for h : f = g.
symbol path_map_transf_cell
  [A B : Grpd]
  [f g : τ (@Function_grpd A B)]
  (h : τ (@= (@Function_grpd A B) f g))
  [x y : τ A]
  (p : τ (@= A x y))
  : τ (@= B (f x) (g y))
≔ @comp_fapp0
    (Path_cat B)
    (f x) (g x) (g y)
    (@eq_ap A B g x y p)
    (@PiHapply A (λ _ : τ A, B) f g h x);

// Object map of a fixed ordinary functor, exposed as a groupoid function.
symbol functor_object_function
  [C D : Cat]
  (F : τ (Functor C D))
  : τ (@Function_grpd (Obj C) (Obj D))
≔ λ x : τ (Obj C), @fapp0 C D F x;

/*
  Universe-category object and hom computations.

  Surface/formula:
    Obj(Grpd_cat) = Grpd
    Obj(Cat_cat)  = Cat
    Hom_Cat(A,B)  = A ⊢ B.
*/

// 3d. Directed-family and displayed-arrow classifiers
//
// Directed Cat-valued families form a stable displayed facade over ordinary
// Cat-valued functors.
//
// Surface/formula:
//   Catd_cat(K) = K ⊢ Cat
//   Catd(K)     = Obj(Catd_cat(K))
//   E[k]        = fapp0 E k, usually via Fibre_cat E k.
injective symbol Catd_cat (K : Cat) : Cat;

// Object/type classifier of directed Cat-valued families over K.
injective symbol Catd (K : Cat) : Grpd
≔ Obj (Catd_cat K);

// Runtime object projection: a directed family is represented by an ordinary
// Cat-valued functor while the `Catd_cat` category head remains visible.
rule Obj (@Catd_cat $K)
  ↪ Obj (Functor_cat $K Cat_cat);

// Proof-time comparison only: the ordinary and displayed category
// presentations recover the same base.
unif_rule Functor_cat $K Cat_cat ≡ @Catd_cat $K'
  ↪ [ $K ≡ $K' ];

// Proof-time inversion for two rigid directed-family category heads.
unif_rule Obj (@Catd_cat $K) ≡ Obj (@Catd_cat $K') ↪ [ $K ≡ $K' ];

// Natural/displayed families of functors between directed Cat-valued families.
//
// Surface/formula:
//   Functord_cat(E,D) = k :^n K ; E[k] ⊢ D[k]
//   Functord(E,D)     = Obj(Functord_cat(E,D)).
injective symbol Functord_cat [K : Cat] (E D : τ (Catd K)) : Cat;

// Object/type classifier of natural/displayed functor families.
injective symbol Functord [K : Cat] (E D : τ (Catd K)) : Grpd
≔ Obj (@Functord_cat K E D);

// Proof-time inversion for two rigid displayed-functor category heads.
unif_rule Obj (@Functord_cat $K $E $D) ≡ Obj (@Functord_cat $K' $E' $D')
  ↪ [ $K ≡ $K'; $E ≡ $E'; $D ≡ $D' ];

// Hom projection in `Catd_cat`: arrows are natural/displayed functor
// families. The ordinary `Transf_cat` presentation is related to this stable
// displayed head at proof time below, rather than by a category rewrite.
rule Hom_cat (@Catd_cat $K) $E $D ↪ @Functord_cat $K $E $D;

// Transparent displayed identity: generic identity at `Catd_cat(K)`.
symbol id_funcd [K : Cat] [E : τ (Catd K)] : τ (Functord E E)
≔ @id (@Catd_cat K) E;

// Displayed-functor composition.
symbol comp_catd_fapp0 [K : Cat] [E D : τ (Catd K)] [C : τ (Catd K)]
  (FF : τ (Functord D C)) (GG : τ (Functord E D)) : τ (Functord E C)
≔ @comp_fapp0 (@Catd_cat K) E D C FF GG;

// Displayed-composition identity units are inherited from generic
// `comp_fapp0` at `Catd_cat K`.

// Canonical Catd specialization of the global strict-functor identity cut.
// This is generic for every functor out of Catd_cat; individual functor
// constructors must not restate the same identity computation.
// lhs-audit: keep 1 -- Catd_cat is the source discriminator for id_funcd.
rule @fapp1_fapp0
      (@Catd_cat $K)
      $B
      $F
      $E $E
      (@id (@Catd_cat $K) $E)
  ↪ @id $B (@fapp0 (@Catd_cat $K) $B $F $E);

// Canonical Catd specialization of the global strict-functor composition
// cut. The three family endpoints are inferred from the two arrow actions;
// keeping them implicit lets this rule survive object-action normalization.
// lhs-audit: keep 1 -- Catd_cat is the source-category discriminator for displayed-functor action.
rule @comp_fapp0
      (@Catd_cat $K)
      _ _ _
      (@fapp1_fapp0
        $A (@Catd_cat $K) $F $Y $Z $g)
      (@fapp1_fapp0
        $A (@Catd_cat $K) $F $X $Y $f)
  ↪ @fapp1_fapp0
      $A
      (@Catd_cat $K)
      $F
      $X
      $Z
      (@comp_fapp0 $A $X $Y $Z $g $f);

// Natural/displayed families of transformations, i.e. modifications between
// directed-family functors.
//
// Surface/formula:
//   Transfd_cat(FF,GG) = k :^n K ; FF[k] => GG[k]
//   Transfd(FF,GG)     = Obj(Transfd_cat(FF,GG)).
injective symbol Transfd_cat [K : Cat] [E D : τ (Catd K)]
  (FF GG : τ (Functord E D)) : Cat;

// Object/type classifier of natural/displayed transformations.
injective symbol Transfd [K : Cat] [E D : τ (Catd K)]
  (FF GG : τ (Functord E D)) : Grpd
≔ Obj (@Transfd_cat K E D FF GG);

// Proof-time inversion for two rigid displayed-transformation category heads.
unif_rule Obj (@Transfd_cat $K $E $D $FF $GG) ≡ Obj (@Transfd_cat $K' $E' $D' $FF' $GG')
  ↪ [ $K ≡ $K'; $E ≡ $E'; $D ≡ $D'; $FF ≡ $FF'; $GG ≡ $GG' ];

// Hom projection in `Functord_cat`: arrows are displayed transformations.
rule Hom_cat (@Functord_cat $K $E $D) $FF $GG
  ↪ @Transfd_cat $K $E $D $FF $GG;

// Transparent displayed identity: generic identity at `Functord_cat(E,D)`.
symbol id_transfd [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  : τ (@Transfd K E D FF FF)
≔ @id (@Functord_cat K E D) FF;

/*
  Directed-family category and displayed-arrow normal forms.

  Surface/formula:
    K ⊢ Cat = Catd_cat(K)
    Hom_Catd(E,D) = k :^n K ; E[k] ⊢ D[k]
    Hom_Functord(FF,GG) = k :^n K ; FF[k] => GG[k].
*/

// 3e. Ordinary identity, composition, opposite, terminal, and constant functors
/*
  Ordinary identity/composition in Cat_cat.

  Surface/formula:
    id_func(A)             = id_A : A ⊢ A
    comp_cat_fapp0(F,G)    = F ∘ G
    (F ∘ G)[x]             = F[G[x]]
    (F ∘ G)[f]             = F[G[f]]
*/
// Stable identity functor head: id_func(A) = id_A : A ⊢ A.
symbol id_func [A: Cat] : τ (Functor A A)
≔ @id Cat_cat A;

// Cat_cat identity and point/arrow actions of the ordinary identity functor.
rule @fapp0 $A $A (@id Cat_cat $A) $xA ↪ $xA;

// Identity functor acts trivially on arrows.
rule @fapp1_fapp0 $A $A (@id Cat_cat $A) $x $y $p ↪ $p;

// Stable composition head: comp_cat_fapp0(F,G) = F ∘ G.
symbol comp_cat_fapp0 [A B : Cat] [C : Cat]
  (F : τ (Functor B C)) (G : τ (Functor A B)) : τ (Functor A C)
≔ @comp_fapp0 Cat_cat A B C F G;

// Cat_cat composition point/arrow actions of composed functors. Identity
// units are inherited from generic `comp_fapp0` at `Cat_cat`.
// Canonical left-associated normal form for iterated functor composition.
rule @comp_fapp0
      Cat_cat
      $A $C $E
      $H
      (@comp_fapp0 Cat_cat $A $B $C $G $F)
  ↪ @comp_fapp0
      Cat_cat
      $A $B $E
      (@comp_fapp0 Cat_cat $B $C $E $H $G)
      $F;

// Object beta for composed functors: `(F o G)[x] = F[G[x]]`.
rule @fapp0 $A $C (@comp_fapp0 Cat_cat $A $B $C $F $G) $x ↪ @fapp0 $B $C $F (@fapp0 $A $B $G $x);

// Arrow beta for composed functors: `(F o G)[f] = F[G[f]]`.
rule @fapp1_fapp0 $A $C (@comp_fapp0 Cat_cat $A $B $C $F $G) $x $y $f
  ↪ @fapp1_fapp0
      $B
      $C
      $F
      (@fapp0 $A $B $G $x)
      (@fapp0 $A $B $G $y)
      (@fapp1_fapp0 $A $B $G $x $y $f);

// Ordinary category identity cuts: g ∘ id ↪ g and id ∘ f ↪ f. The repeated
// middle object is the intentional composition-interface guard; the external
// endpoints remain inferred and may use proof-time-compatible presentations.
// The resulting critical pair is required to join by typed proof-time equality.
rule @comp_fapp0 $A _ $Y _ $g (@id $A $Y) ↪ $g;

// Left identity cut with the shared middle object as the matching guard.
rule @comp_fapp0 $A _ $Y _ (@id $A $Y) $f ↪ $f;

/*
  Path-category unit projection bridges.

  `id(Path_cat(A),x)` projects to `eq_refl(x)`. These two narrow constructor
  rules make both generic category-unit cuts stable when that inner projection
  is selected first; they do not choose a path-specific composition owner.
*/
// lhs-audit: keep 1 -- Path_cat is the semantic discriminator for the projected right-unit bridge.
rule @comp_fapp0
      (Path_cat $A) $x $x _ $p (@eq_refl $A $x)
  ↪ $p;

// lhs-audit: keep 1 -- Path_cat is the semantic discriminator for the projected left-unit bridge.
rule @comp_fapp0
      (Path_cat $A) _ $y $y (@eq_refl $A $y) $p
  ↪ $p;

// PathRecord shaped-reflexivity registrations for both shared category units.
// lhs-audit: keep 1 -- the nested Path_cat/PathRecord heads select this former.
rule @comp_fapp0
      (Path_cat (PathRecord_grpd $A))
      $r $r _ $p (@PathRecordPathRefl $A $r)
  ↪ $p;

// lhs-audit: keep 1 -- the nested Path_cat/PathRecord heads select this former.
rule @comp_fapp0
      (Path_cat (PathRecord_grpd $A))
      _ $r $r (@PathRecordPathRefl $A $r) $p
  ↪ $p;

/*
  Propositional comparison with J-derived path transitivity.

  Runtime retains `comp_fapp0(Path_cat(A),...)`; path induction supplies the
  mathematical agreement with `eq_trans` without installing a reverse fold or
  a proof-time equation specific to paths.
*/
symbol path_comp_eq_trans
  [A : Grpd]
  [x y : τ A]
  (p : τ (x = y))
  [z : τ A]
  (q : τ (y = z))
  : τ (
      @comp_fapp0 (Path_cat A) x y z q p
      = @eq_trans A x y z p q)
≔ @ind_eqr A y
    (λ x : τ A, λ p : τ (x = y),
      @Pi_grpd A
        (λ z : τ A,
          @Pi_grpd (y = z)
            (λ q : τ (y = z),
              @comp_fapp0 (Path_cat A) x y z q p
              = @eq_trans A x y z p q)))
    (λ z : τ A, λ q : τ (y = z), eq_refl q)
    x p z q;

// Reflexive ordinary isomorphism evidence requires the identity-cut rules
// above so that both propositional inverse equations are reflexivity.
injective symbol iso_evidence_refl
  [C : Cat]
  (x : τ (Obj C))
  : τ (IsoEvidence C x x);

// Forward arrow of reflexive isomorphism evidence is identity.
rule sigma_Fst (@iso_evidence_refl $C $x)
  ↪ @id $C $x;

// Inverse arrow of reflexive isomorphism evidence is identity.
rule sigma_Fst (sigma_Snd (@iso_evidence_refl $C $x))
  ↪ @id $C $x;

// Left inverse proof of reflexive evidence is reflexivity.
rule sigma_Fst (sigma_Snd (sigma_Snd (@iso_evidence_refl $C $x)))
  ↪ eq_refl (@id $C $x);

// Right inverse proof of reflexive evidence is reflexivity.
rule sigma_Snd (sigma_Snd (sigma_Snd (@iso_evidence_refl $C $x)))
  ↪ eq_refl (@id $C $x);

/*
  Categorical univalence skeleton.

  The 1-categorical staging layer maps object paths to ordinary isomorphism
  evidence. It is a compatibility approximation for the familiar
  univalent-category slogan "isomorphisms are paths"; it remains separate from
  the recursive omega-categorical equivalence below.
*/

// Convert object equality to ordinary categorical isomorphism evidence.
symbol idtoiso_cat
  [C : Cat]
  [x y : τ (Obj C)]
  (p : τ (x = y))
  : τ (IsoEvidence C x y);

// Reflexive object equality maps to reflexive isomorphism evidence.
rule @idtoiso_cat $C $x $x (eq_refl $x)
  ↪ @iso_evidence_refl $C $x;

// Closed shaped-reflexivity registration for the ordinary iso encoder.
rule @idtoiso_cat $C $r $r (@PathRecordPathRefl _ $r)
  ↪ @iso_evidence_refl $C $r;

// 1-categorical univalence capability for `idtoiso_cat`.
symbol CatIsoUnivalence
  (C : Cat)
  : Grpd
≔ @Pi_grpd (Obj C)
    (λ x : τ (Obj C),
      @Pi_grpd (Obj C)
        (λ y : τ (Obj C),
          @IsEquivMap
            (@= (Obj C) x y)
            (IsoEvidence C x y)
            (λ p : τ (@= (Obj C) x y), @idtoiso_cat C x y p)));

// Decode ordinary isomorphism evidence to object equality using a capability.
symbol isotoid_cat
  [C : Cat]
  (U : τ (CatIsoUnivalence C))
  [x y : τ (Obj C)]
  (i : τ (IsoEvidence C x y))
  : τ (x = y)
≔ @type_equiv_from
    (@= (Obj C) x y)
    (IsoEvidence C x y)
    (@Struct_sigma
      (Function_grpd (@= (Obj C) x y) (IsoEvidence C x y))
      (λ f : τ (Function_grpd (@= (Obj C) x y) (IsoEvidence C x y)),
        @IsEquivMap (@= (Obj C) x y) (IsoEvidence C x y) f)
      (λ p : τ (@= (Obj C) x y), @idtoiso_cat C x y p)
      (U x y))
    i;

/*
  Equality-valued fixed-arrow omega-equivalence staging record.

  For `f : Hom_C(x,y)`, separate left and right inverse arrows carry ordinary
  equality witnesses in the two endomorphism hom-categories. The arrow remains
  an index, so the public eliminator ranges over both `f` and its evidence.
  This native owner has no comparison with the retired legacy representation;
  no public compatibility interface remains.
*/
(C : Cat)
(x y : τ (Obj C))
(f : τ (Hom C x y))
inductive OmegaEquivAlongEqData : TYPE ≔
| Struct_omega_equiv_along_eq
    (left_inv right_inv : τ (Hom C y x))
    (left_law : τ (@=
      (Hom C x x)
      (@comp_fapp0 C x y x left_inv f)
      (@id C x)))
    (right_law : τ (@=
      (Hom C y y)
      (@comp_fapp0 C y x y f right_inv)
      (@id C y)))
    : OmegaEquivAlongEqData C x y f;

// Stable groupoid classifier decoded by the native record above.
constant symbol OmegaEquivAlong
  [C : Cat]
  [x y : τ (Obj C)]
  (f : τ (Hom C x y))
  : Grpd;

rule τ (@OmegaEquivAlong $C $x $y $f)
  ↪ @OmegaEquivAlongEqData $C $x $y $f;

// Readable introduction alias routed through the native constructor.
symbol omega_equiv_along_intro
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (left_inv right_inv : τ (Hom C y x))
  (left_law : τ (@=
    (Hom C x x)
    (@comp_fapp0 C x y x left_inv f)
    (@id C x)))
  (right_law : τ (@=
    (Hom C y y)
    (@comp_fapp0 C y x y f right_inv)
    (@id C y)))
  : τ (@OmegaEquivAlong C x y f)
≔ @Struct_omega_equiv_along_eq
    C x y f left_inv right_inv left_law right_law;

// Selected left-inverse arrow.
symbol omega_equiv_along_left_inv
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f))
  : τ (Hom C y x);

rule @omega_equiv_along_left_inv _ _ _ _
      (@Struct_omega_equiv_along_eq _ _ _ _ $l _ _ _)
  ↪ $l;

// Selected right-inverse arrow.
symbol omega_equiv_along_right_inv
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f))
  : τ (Hom C y x);

rule @omega_equiv_along_right_inv _ _ _ _
      (@Struct_omega_equiv_along_eq _ _ _ _ _ $r _ _)
  ↪ $r;

// Equality-valued left cancellation in `Hom_C(x,x)`.
symbol omega_equiv_along_left_law
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f))
  : τ (@=
      (Hom C x x)
      (@comp_fapp0 C x y x
        (@omega_equiv_along_left_inv C x y f u)
        f)
      (@id C x));

rule @omega_equiv_along_left_law _ _ _ _
      (@Struct_omega_equiv_along_eq _ _ _ _ _ _ $alpha _)
  ↪ $alpha;

// Equality-valued right cancellation in `Hom_C(y,y)`.
symbol omega_equiv_along_right_law
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f))
  : τ (@=
      (Hom C y y)
      (@comp_fapp0 C y x y
        f
        (@omega_equiv_along_right_inv C x y f u))
      (@id C y));

rule @omega_equiv_along_right_law _ _ _ _
      (@Struct_omega_equiv_along_eq _ _ _ _ _ _ _ $beta)
  ↪ $beta;

// Public indexed eliminator: the motive ranges over the arrow index and data.
symbol omega_equiv_along_ind
  [C : Cat]
  [x y : τ (Obj C)]
  (Q : Π f : τ (Hom C x y),
       τ (@OmegaEquivAlong C x y f) → Grpd)
  (c : Π f : τ (Hom C x y),
       Π (l r : τ (Hom C y x)),
       Π alpha : τ (@=
         (Hom C x x)
         (@comp_fapp0 C x y x l f)
         (@id C x)),
       Π beta : τ (@=
         (Hom C y y)
         (@comp_fapp0 C y x y f r)
         (@id C y)),
       τ (Q f (@Struct_omega_equiv_along_eq
         C x y f l r alpha beta)))
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f))
  : τ (Q f u)
≔ @ind_OmegaEquivAlongEqData C x y Q c f u;

// Reflexive evidence for the already-selected identity arrow.
symbol omega_equiv_along_refl
  [C : Cat]
  (x : τ (Obj C))
  : τ (@OmegaEquivAlong C x x (@id C x))
≔ @omega_equiv_along_intro
    C x x (@id C x)
    (@id C x)
    (@id C x)
    (@eq_refl (Hom C x x) (@id C x))
    (@eq_refl (Hom C x x) (@id C x));

/*
  Ordinary functor action preserves equality-valued fixed-arrow equivalence.

  The inverse arrows are the images of the selected inverses. Applying the
  functor action to the two source cancellation laws supplies the target
  laws; the global functoriality owners then compare the mapped composites
  and identities with their canonical target forms.
*/
symbol omega_equiv_along_fapp1_fapp0
  [A B : Cat]
  (F : τ (Functor A B))
  [x y : τ (Obj A)]
  [f : τ (Hom A x y)]
  (u : τ (@OmegaEquivAlong A x y f))
  : τ (@OmegaEquivAlong
      B
      (@fapp0 A B F x)
      (@fapp0 A B F y)
      (@fapp1_fapp0 A B F x y f))
≔ @omega_equiv_along_intro
    B
    (@fapp0 A B F x)
    (@fapp0 A B F y)
    (@fapp1_fapp0 A B F x y f)
    (@fapp1_fapp0 A B F y x
      (@omega_equiv_along_left_inv A x y f u))
    (@fapp1_fapp0 A B F y x
      (@omega_equiv_along_right_inv A x y f u))
    (@eq_ap
      (Hom A x x)
      (Hom B (@fapp0 A B F x) (@fapp0 A B F x))
      (λ h : τ (Hom A x x), @fapp1_fapp0 A B F x x h)
      (@comp_fapp0 A x y x
        (@omega_equiv_along_left_inv A x y f u)
        f)
      (@id A x)
      (@omega_equiv_along_left_law A x y f u))
    (@eq_ap
      (Hom A y y)
      (Hom B (@fapp0 A B F y) (@fapp0 A B F y))
      (λ h : τ (Hom A y y), @fapp1_fapp0 A B F y y h)
      (@comp_fapp0 A y x y
        f
        (@omega_equiv_along_right_inv A x y f u))
      (@id A y)
      (@omega_equiv_along_right_law A x y f u));

/*
  Stable first-class facade for a selected arrow and its equality-valued evidence.

  This is an abstract record-like classifier rather than a transparent Sigma:
  its constructor, observers, and trusted dependent eliminator own the
  computational interface. The later abstract proof-time and rigid-universe
  direct owners below target this stable facade.
*/
constant symbol OmegaEquiv
  (C : Cat)
  (x y : τ (Obj C))
  : Grpd;

/*
  Abstract direct-univalence comparison.

  This proof-time owner applies while the category remains syntactically
  abstract. Constructors whose object equality has already reduced to a
  different classifier may require an explicit adapter or a stable shaped
  join; no literal-identity cast is exported by this slice.
*/
unif_rule
  @OmegaEquiv $C $x $y
  ≡ @= (Obj $C) $x $y
  ↪ [ tt ≡ tt ];

/*
  General stable carrier view for explicit equality/equality-valued casts.

  Equality enters by carrier reduction and equality-valued enters through one direct
  proof-time comparison. The typed-let adapters below therefore never rely on
  transitivity of unification hints, even after category specialization.
*/
injective symbol ObjectPathCastView
  [C : Cat]
  (x y : τ (Obj C))
  : Grpd;

rule τ (@ObjectPathCastView $C $x $y)
  ↪ τ (@= (Obj $C) $x $y);

unif_rule
  @OmegaEquiv $C $x $y
  ≡ @ObjectPathCastView $C $x $y
  ↪ [ tt ≡ tt ];

symbol object_path_cast_to_omega
  [C : Cat]
  [x y : τ (Obj C)]
  (p : τ (@= (Obj C) x y))
  : τ (@OmegaEquiv C x y)
≔ let w : τ (@ObjectPathCastView C x y) ≔ p in w;

symbol omega_cast_to_object_path
  [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (@OmegaEquiv C x y))
  : τ (@= (Obj C) x y)
≔ let w : τ (@ObjectPathCastView C x y) ≔ e in w;

/*
  Opposite compatibility names route through the general stable carrier cast.
  They remain transparent identities and do not reify a package.
*/
symbol op_path_as_omega
  [C : Cat]
  [x y : τ (Obj C)]
  (p : τ (@= (Obj C) x y))
  : τ (@OmegaEquiv (Op_cat C) x y)
≔ @object_path_cast_to_omega (Op_cat C) x y p;

symbol op_omega_as_path
  [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (@OmegaEquiv (Op_cat C) x y))
  : τ (@= (Obj C) x y)
≔ @omega_cast_to_object_path (Op_cat C) x y e;

// The rigid groupoid universe has a finite direct equality-valued runtime normal form.
rule @= (Obj Grpd_cat) $A $B
  ↪ @OmegaEquiv Grpd_cat $A $B;

// Literal path-category equivalence and ambient path equality are the same
// classifier at proof time. This narrow join handles the shaped case after
// Path-category reduction; it is separate from the abstract owner above.
unif_rule
  @OmegaEquiv (Path_cat $A) $x $y
  ≡ @= $A $x $y
  ↪ [ tt ≡ tt ];

// Constructor for the stable dependent-pair facade.
injective symbol omega_equiv_pack
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f))
  : τ (@OmegaEquiv C x y);

// Selected forward arrow.
symbol omega_equiv_to
  [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (@OmegaEquiv C x y))
  : τ (Hom C x y);

rule @omega_equiv_to _ _ _
      (@omega_equiv_pack _ _ _ $f _)
  ↪ $f;

// Fixed-arrow evidence over the selected forward arrow.
symbol omega_equiv_evidence
  [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (@OmegaEquiv C x y))
  : τ (@OmegaEquivAlong C x y
      (@omega_equiv_to C x y e));

rule @omega_equiv_evidence _ _ _
      (@omega_equiv_pack _ _ _ _ $u)
  ↪ $u;

// Trusted record-like dependent eliminator for the stable facade.
symbol omega_equiv_ind
  [C : Cat]
  [x y : τ (Obj C)]
  (Q : τ (@OmegaEquiv C x y) → Grpd)
  (c : Π f : τ (Hom C x y),
       Π u : τ (@OmegaEquivAlong C x y f),
       τ (Q (@omega_equiv_pack C x y f u)))
  (e : τ (@OmegaEquiv C x y))
  : τ (Q e);

rule @omega_equiv_ind _ _ _ _ $c
      (@omega_equiv_pack _ _ _ $f $u)
  ↪ $c $f $u;

// Canonical first-class reflexive package.
symbol omega_equiv_refl
  [C : Cat]
  (x : τ (Obj C))
  : τ (@OmegaEquiv C x x)
≔ @omega_equiv_pack
    C x x (@id C x)
    (@omega_equiv_along_refl C x);

// Propositional facade eta derived through the primitive eliminator.
symbol omega_equiv_eta
  [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (@OmegaEquiv C x y))
  : τ (@=
      (@OmegaEquiv C x y)
      (@omega_equiv_pack
        C x y
        (@omega_equiv_to C x y e)
        (@omega_equiv_evidence C x y e))
      e)
≔ @omega_equiv_ind
    C x y
    (λ e : τ (@OmegaEquiv C x y),
      @=
        (@OmegaEquiv C x y)
        (@omega_equiv_pack
          C x y
          (@omega_equiv_to C x y e)
          (@omega_equiv_evidence C x y e))
        e)
    (λ f : τ (Hom C x y),
      λ u : τ (@OmegaEquivAlong C x y f),
        @eq_refl
          (@OmegaEquiv C x y)
          (@omega_equiv_pack C x y f u))
    e;

// Transparent Sigma presentation retained as a comparison/library view.
symbol OmegaEquivSigma
  (C : Cat)
  (x y : τ (Obj C))
  : Grpd
≔ `Σ_ f : τ (Hom C x y), @OmegaEquivAlong C x y f;

symbol omega_facade_to_sigma
  [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (@OmegaEquiv C x y))
  : τ (@OmegaEquivSigma C x y)
≔ @Struct_sigma
    (Hom C x y)
    (λ f : τ (Hom C x y), @OmegaEquivAlong C x y f)
    (@omega_equiv_to C x y e)
    (@omega_equiv_evidence C x y e);

symbol omega_sigma_to_facade
  [C : Cat]
  [x y : τ (Obj C)]
  (s : τ (@OmegaEquivSigma C x y))
  : τ (@OmegaEquiv C x y)
≔ @omega_equiv_pack
    C x y
    (@sigma_Fst
      (Hom C x y)
      (λ f : τ (Hom C x y), @OmegaEquivAlong C x y f)
      s)
    (@sigma_Snd
      (Hom C x y)
      (λ f : τ (Hom C x y), @OmegaEquivAlong C x y f)
      s);

// Sigma-to-facade-to-Sigma is propositionally the identity.
symbol omega_sigma_roundtrip
  [C : Cat]
  [x y : τ (Obj C)]
  (s : τ (@OmegaEquivSigma C x y))
  : τ (@=
      (@OmegaEquivSigma C x y)
      (@omega_facade_to_sigma C x y
        (@omega_sigma_to_facade C x y s))
      s)
≔ @sigma_ind
    (Hom C x y)
    (λ f : τ (Hom C x y), @OmegaEquivAlong C x y f)
    (λ s : τ (@OmegaEquivSigma C x y),
      @=
        (@OmegaEquivSigma C x y)
        (@omega_facade_to_sigma C x y
          (@omega_sigma_to_facade C x y s))
        s)
    (λ f : τ (Hom C x y),
      λ u : τ (@OmegaEquivAlong C x y f),
        @eq_refl
          (@OmegaEquivSigma C x y)
          (@Struct_sigma
            (Hom C x y)
            (λ g : τ (Hom C x y), @OmegaEquivAlong C x y g)
            f u))
    s;

// Facade-to-Sigma-to-facade is the previously derived facade eta.
symbol omega_facade_roundtrip
  [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (@OmegaEquiv C x y))
  : τ (@=
      (@OmegaEquiv C x y)
      (@omega_sigma_to_facade C x y
        (@omega_facade_to_sigma C x y e))
      e)
≔ @omega_equiv_eta C x y e;

/*
  Explicit general object-path adapter.

  Unlike a literal identity typing view, this constructs a facade package.
  Its arrow is `path_to_hom`; both inverse arrows use the reversed path; the
  cancellation laws are defined by primitive path induction.
*/
symbol object_path_equiv_left_law
  [C : Cat]
  [x y : τ (Obj C)]
  (p : τ (@= (Obj C) x y))
  : τ (@=
      (Hom C x x)
      (@comp_fapp0 C x y x
        (@path_to_hom C y x (@path_sym (Obj C) x y p))
        (@path_to_hom C x y p))
      (@id C x))
≔ @ind_eqr
    (Obj C)
    y
    (λ x : τ (Obj C), λ p : τ (@= (Obj C) x y),
      @=
        (Hom C x x)
        (@comp_fapp0 C x y x
          (@path_to_hom C y x (@path_sym (Obj C) x y p))
          (@path_to_hom C x y p))
        (@id C x))
    (@eq_refl (Hom C y y) (@id C y))
    x
    p;

symbol object_path_equiv_right_law
  [C : Cat]
  [x y : τ (Obj C)]
  (p : τ (@= (Obj C) x y))
  : τ (@=
      (Hom C y y)
      (@comp_fapp0 C y x y
        (@path_to_hom C x y p)
        (@path_to_hom C y x (@path_sym (Obj C) x y p)))
      (@id C y))
≔ @ind_eqr
    (Obj C)
    y
    (λ x : τ (Obj C), λ p : τ (@= (Obj C) x y),
      @=
        (Hom C y y)
        (@comp_fapp0 C y x y
          (@path_to_hom C x y p)
          (@path_to_hom C y x (@path_sym (Obj C) x y p)))
        (@id C y))
    (@eq_refl (Hom C y y) (@id C y))
    x
    p;

symbol object_path_equiv_along
  [C : Cat]
  [x y : τ (Obj C)]
  (p : τ (@= (Obj C) x y))
  : τ (@OmegaEquivAlong C x y (@path_to_hom C x y p))
≔ @omega_equiv_along_intro
    C
    x
    y
    (@path_to_hom C x y p)
    (@path_to_hom C y x (@path_sym (Obj C) x y p))
    (@path_to_hom C y x (@path_sym (Obj C) x y p))
    (@object_path_equiv_left_law C x y p)
    (@object_path_equiv_right_law C x y p);

symbol object_path_equiv
  [C : Cat]
  [x y : τ (Obj C)]
  (p : τ (@= (Obj C) x y))
  : τ (@OmegaEquiv C x y)
≔ @omega_equiv_pack
    C
    x
    y
    (@path_to_hom C x y p)
    (@object_path_equiv_along C x y p);

/*
  Ordinary isomorphism evidence embeds directly in native equality-valued evidence.

  The single selected ordinary inverse supplies both native inverse slots;
  the two ordinary inverse equations already have exactly the required
  equality-valued law types. This is a one-way structural construction, not
  a decoder or a claim that a stable facade cast exposes package observers.
*/
symbol iso_evidence_omega_along
  [C : Cat]
  [x y : τ (Obj C)]
  (i : τ (IsoEvidence C x y))
  : τ (@OmegaEquivAlong C x y (@iso_evidence_to C x y i))
≔ @omega_equiv_along_intro
    C x y
    (@iso_evidence_to C x y i)
    (@iso_evidence_from C x y i)
    (@iso_evidence_from C x y i)
    (@iso_evidence_left C x y i)
    (@iso_evidence_right C x y i);

// First-class native facade carrying the ordinary forward arrow and inverse.
symbol iso_evidence_omega_equiv
  [C : Cat]
  [x y : τ (Obj C)]
  (i : τ (IsoEvidence C x y))
  : τ (@OmegaEquiv C x y)
≔ @omega_equiv_pack
    C x y
    (@iso_evidence_to C x y i)
    (@iso_evidence_omega_along C x y i);

/*
  Literal path-category specialization.

  The general object-path adapter exposes `path_to_hom(p)`. For a literal
  `Path_cat(A)` this stronger package instead retains `p` itself as the
  selected arrow, with `path_sym(p)` as both inverse choices.
*/
symbol path_equiv_left_law
  [A : Grpd]
  [x y : τ A]
  (p : τ (@= A x y))
  : τ (@=
      (Hom (Path_cat A) x x)
      (@comp_fapp0
        (Path_cat A) x y x
        (@path_sym A x y p)
        p)
      (@id (Path_cat A) x))
≔ @ind_eqr
    A
    y
    (λ x : τ A, λ p : τ (@= A x y),
      @=
        (Hom (Path_cat A) x x)
        (@comp_fapp0
          (Path_cat A) x y x
          (@path_sym A x y p)
          p)
        (@id (Path_cat A) x))
    (@eq_refl
      (Hom (Path_cat A) y y)
      (@id (Path_cat A) y))
    x
    p;

symbol path_equiv_right_law
  [A : Grpd]
  [x y : τ A]
  (p : τ (@= A x y))
  : τ (@=
      (Hom (Path_cat A) y y)
      (@comp_fapp0
        (Path_cat A) y x y
        p
        (@path_sym A x y p))
      (@id (Path_cat A) y))
≔ @ind_eqr
    A
    y
    (λ x : τ A, λ p : τ (@= A x y),
      @=
        (Hom (Path_cat A) y y)
        (@comp_fapp0
          (Path_cat A) y x y
          p
          (@path_sym A x y p))
        (@id (Path_cat A) y))
    (@eq_refl
      (Hom (Path_cat A) y y)
      (@id (Path_cat A) y))
    x
    p;

symbol path_equiv_along
  [A : Grpd]
  [x y : τ A]
  (p : τ (@= A x y))
  : τ (@OmegaEquivAlong (Path_cat A) x y p)
≔ @omega_equiv_along_intro
    (Path_cat A)
    x
    y
    p
    (@path_sym A x y p)
    (@path_sym A x y p)
    (@path_equiv_left_law A x y p)
    (@path_equiv_right_law A x y p);

symbol path_equiv
  [A : Grpd]
  [x y : τ A]
  (p : τ (@= A x y))
  : τ (@OmegaEquiv (Path_cat A) x y)
≔ @omega_equiv_pack
    (Path_cat A)
    x
    y
    p
    (@path_equiv_along A x y p);

/*
  Internal groupoidality in the intended univalent-category setting.

  Equivalence of `Core_cat(C) -> C` says that every directed arrow is
  represented by an object path. Without the surrounding univalence intent
  this is stronger than ordinary external groupoidality.
*/
// This comparison cannot live beside `Core_incl_func`, which precedes the
// declaration of `Cat_cat`. The groupoidality owner is the first boundary at
// which both rigid heads exist. Neither side becomes a runtime normal form.
unif_rule
  @Core_incl_func (Path_cat $A)
  ≡ @id Cat_cat (Path_cat $A)
  ↪ [ tt ≡ tt ];

symbol IsGroupoidalCat
  (C : Cat)
  : Grpd
≔ @OmegaEquivAlong
    Cat_cat
    (Core_cat C)
    C
    (Core_incl_func C);

// The literal path category is canonically internally groupoidal.
symbol path_cat_is_groupoidal
  (A : Grpd)
  : τ (@IsGroupoidalCat (Path_cat A))
≔ @omega_equiv_along_refl Cat_cat (Path_cat A);

/*
  Explicit comparison with contractible-fibre equivalence over `Grpd_cat`.

  These are derived adapters, not universe decoders. The forward direction
  uses the selected inverse of `TypeEquiv`; the reverse direction converts
  equality-valued bi-inverse data through the existing
  `is_equiv_map_by_inverse` theorem capability.
*/

// Pointwise TypeEquiv left inverse assembled into a Grpd_cat hom path.
symbol type_equiv_omega_left_law
  [A B : Grpd]
  (e : τ (TypeEquiv A B))
  : τ (@=
      (Hom Grpd_cat A A)
      (@comp_fapp0 Grpd_cat A B A
        (λ b : τ B, @type_equiv_from A B e b)
        (@type_equiv_to A B e))
      (@id Grpd_cat A))
≔ @PiFunext
    A
    (λ _ : τ A, A)
    (@grpd_comp_function A B A
      (λ b : τ B, @type_equiv_from A B e b)
      (@type_equiv_to A B e))
    (@grpd_id_function A)
    (λ a : τ A, @type_equiv_left A B e a);

// Pointwise TypeEquiv right inverse assembled into a Grpd_cat hom path.
symbol type_equiv_omega_right_law
  [A B : Grpd]
  (e : τ (TypeEquiv A B))
  : τ (@=
      (Hom Grpd_cat B B)
      (@comp_fapp0 Grpd_cat B A B
        (@type_equiv_to A B e)
        (λ b : τ B, @type_equiv_from A B e b))
      (@id Grpd_cat B))
≔ @PiFunext
    B
    (λ _ : τ B, B)
    (@grpd_comp_function B A B
      (@type_equiv_to A B e)
      (λ b : τ B, @type_equiv_from A B e b))
    (@grpd_id_function B)
    (λ b : τ B, @type_equiv_right A B e b);

// Contractible-fibre equivalence embeds into equality-valued omega-equivalence.
symbol type_equiv_to_omega
  [A B : Grpd]
  (e : τ (TypeEquiv A B))
  : τ (@OmegaEquiv Grpd_cat A B)
≔ @omega_equiv_pack
    Grpd_cat A B
    (@type_equiv_to A B e)
    (@omega_equiv_along_intro
      Grpd_cat A B
      (@type_equiv_to A B e)
      (λ b : τ B, @type_equiv_from A B e b)
      (λ b : τ B, @type_equiv_from A B e b)
      (@type_equiv_omega_left_law A B e)
      (@type_equiv_omega_right_law A B e));

// Pointwise form of the equality-valued left inverse law in Grpd_cat.
symbol omega_grpd_left_point
  [A B : Grpd]
  [f : τ (@Function_grpd A B)]
  (u : τ (@OmegaEquivAlong Grpd_cat A B f))
  (a : τ A)
  : τ (@= A
      ((@omega_equiv_along_left_inv Grpd_cat A B f u) (f a))
      a)
≔ @PiHapply
    A
    (λ _ : τ A, A)
    (@grpd_comp_function A B A
      (@omega_equiv_along_left_inv Grpd_cat A B f u)
      f)
    (@grpd_id_function A)
    (@omega_equiv_along_left_law Grpd_cat A B f u)
    a;

// Pointwise form of the equality-valued right inverse law in Grpd_cat.
symbol omega_grpd_right_point
  [A B : Grpd]
  [f : τ (@Function_grpd A B)]
  (u : τ (@OmegaEquivAlong Grpd_cat A B f))
  (b : τ B)
  : τ (@= B
      (f ((@omega_equiv_along_right_inv Grpd_cat A B f u) b))
      b)
≔ @PiHapply
    B
    (λ _ : τ B, B)
    (@grpd_comp_function B A B
      f
      (@omega_equiv_along_right_inv Grpd_cat A B f u))
    (@grpd_id_function B)
    (@omega_equiv_along_right_law Grpd_cat A B f u)
    b;

// The separately selected left and right inverses agree pointwise.
symbol omega_grpd_left_to_right_point
  [A B : Grpd]
  [f : τ (@Function_grpd A B)]
  (u : τ (@OmegaEquivAlong Grpd_cat A B f))
  (b : τ B)
  : τ (@= A
      ((@omega_equiv_along_left_inv Grpd_cat A B f u) b)
      ((@omega_equiv_along_right_inv Grpd_cat A B f u) b))
≔ @eq_trans
    A
    ((@omega_equiv_along_left_inv Grpd_cat A B f u) b)
    ((@omega_equiv_along_left_inv Grpd_cat A B f u)
      (f ((@omega_equiv_along_right_inv Grpd_cat A B f u) b)))
    ((@omega_equiv_along_right_inv Grpd_cat A B f u) b)
    (@eq_ap
      B
      A
      (@omega_equiv_along_left_inv Grpd_cat A B f u)
      b
      (f ((@omega_equiv_along_right_inv Grpd_cat A B f u) b))
      (@eq_sym
        B
        (f ((@omega_equiv_along_right_inv Grpd_cat A B f u) b))
        b
        (@omega_grpd_right_point A B f u b)))
    (@omega_grpd_left_point
      A B f u
      ((@omega_equiv_along_right_inv Grpd_cat A B f u) b));

// The selected left inverse therefore also satisfies the right inverse law.
symbol omega_grpd_left_right_point
  [A B : Grpd]
  [f : τ (@Function_grpd A B)]
  (u : τ (@OmegaEquivAlong Grpd_cat A B f))
  (b : τ B)
  : τ (@= B
      (f ((@omega_equiv_along_left_inv Grpd_cat A B f u) b))
      b)
≔ @eq_trans
    B
    (f ((@omega_equiv_along_left_inv Grpd_cat A B f u) b))
    (f ((@omega_equiv_along_right_inv Grpd_cat A B f u) b))
    b
    (@eq_ap
      A
      B
      f
      ((@omega_equiv_along_left_inv Grpd_cat A B f u) b)
      ((@omega_equiv_along_right_inv Grpd_cat A B f u) b)
      (@omega_grpd_left_to_right_point A B f u b))
    (@omega_grpd_right_point A B f u b);

// Equality-valued bi-inverse data supplies one specified quasi-inverse.
symbol omega_grpd_by_inverse
  [A B : Grpd]
  [f : τ (@Function_grpd A B)]
  (u : τ (@OmegaEquivAlong Grpd_cat A B f))
  : τ (@EquivByInverse
      A B f
      (@omega_equiv_along_left_inv Grpd_cat A B f u))
≔ @Product_pair_grpd
    (@Pi_grpd A
      (λ a : τ A,
        @= A
          ((@omega_equiv_along_left_inv Grpd_cat A B f u) (f a))
          a))
    (@Pi_grpd B
      (λ b : τ B,
        @= B
          (f ((@omega_equiv_along_left_inv Grpd_cat A B f u) b))
          b))
    (λ a : τ A, @omega_grpd_left_point A B f u a)
    (λ b : τ B, @omega_grpd_left_right_point A B f u b);

// The forward function has contractible fibres by the existing theorem.
symbol omega_grpd_is_equiv
  [A B : Grpd]
  [f : τ (@Function_grpd A B)]
  (u : τ (@OmegaEquivAlong Grpd_cat A B f))
  : τ (@IsEquivMap A B f)
≔ @is_equiv_map_by_inverse
    A B f
    (@omega_equiv_along_left_inv Grpd_cat A B f u)
    (@omega_grpd_by_inverse A B f u);

// Fixed-arrow omega-equivalence over Grpd_cat yields TypeEquiv.
symbol omega_along_to_type_equiv
  [A B : Grpd]
  [f : τ (@Function_grpd A B)]
  (u : τ (@OmegaEquivAlong Grpd_cat A B f))
  : τ (TypeEquiv A B)
≔ @Struct_sigma
    (@Function_grpd A B)
    (λ g : τ (@Function_grpd A B), @IsEquivMap A B g)
    f
    (@omega_grpd_is_equiv A B f u);

// First-class omega-equivalence over Grpd_cat yields TypeEquiv by observers.
symbol omega_to_type_equiv
  [A B : Grpd]
  (e : τ (@OmegaEquiv Grpd_cat A B))
  : τ (TypeEquiv A B)
≔ @omega_along_to_type_equiv
    A B
    (@omega_equiv_to Grpd_cat A B e)
    (@omega_equiv_evidence Grpd_cat A B e);

// Phase-13 direct owner: category-universe equality exposes omega-equivalence.
rule @= (Obj Cat_cat) $A $B
  ↪ @OmegaEquiv Cat_cat $A $B;

/*
  Composition of ordinary isomorphism evidence.

  The small proof steps keep endpoint inference bounded. The observable
  forward and inverse arrows remain transparent compositions; only their
  propositional inverse witnesses use comp_assoc and equality congruence.
*/
symbol iso_evidence_comp_left_step1
  [C : Cat]
  [x y z : τ (Obj C)]
  (j : τ (IsoEvidence C y z))
  (i : τ (IsoEvidence C x y))
  : τ (
      @comp_fapp0 C x z x
        (@comp_fapp0 C z y x
          (@iso_evidence_from C x y i)
          (@iso_evidence_from C y z j))
        (@comp_fapp0 C x y z
          (@iso_evidence_to C y z j)
          (@iso_evidence_to C x y i))
      =
      @comp_fapp0 C x y x
        (@iso_evidence_from C x y i)
        (@comp_fapp0 C x z y
          (@iso_evidence_from C y z j)
          (@comp_fapp0 C x y z
            (@iso_evidence_to C y z j)
            (@iso_evidence_to C x y i))))
≔ @eq_sym
    (Hom C x x)
    (@comp_fapp0 C x y x
      (@iso_evidence_from C x y i)
      (@comp_fapp0 C x z y
        (@iso_evidence_from C y z j)
        (@comp_fapp0 C x y z
          (@iso_evidence_to C y z j)
          (@iso_evidence_to C x y i))))
    (@comp_fapp0 C x z x
      (@comp_fapp0 C z y x
        (@iso_evidence_from C x y i)
        (@iso_evidence_from C y z j))
      (@comp_fapp0 C x y z
        (@iso_evidence_to C y z j)
        (@iso_evidence_to C x y i)))
    (@comp_assoc C x z y x
      (@iso_evidence_from C x y i)
      (@iso_evidence_from C y z j)
      (@comp_fapp0 C x y z
        (@iso_evidence_to C y z j)
        (@iso_evidence_to C x y i)));

// Left-cancellation proof step 2: reassociate around the j inverse pair.
symbol iso_evidence_comp_left_step2
  [C : Cat]
  [x y z : τ (Obj C)]
  (j : τ (IsoEvidence C y z))
  (i : τ (IsoEvidence C x y))
  : τ (
      @comp_fapp0 C x y x
        (@iso_evidence_from C x y i)
        (@comp_fapp0 C x z y
          (@iso_evidence_from C y z j)
          (@comp_fapp0 C x y z
            (@iso_evidence_to C y z j)
            (@iso_evidence_to C x y i)))
      =
      @comp_fapp0 C x y x
        (@iso_evidence_from C x y i)
        (@comp_fapp0 C x y y
          (@comp_fapp0 C y z y
            (@iso_evidence_from C y z j)
            (@iso_evidence_to C y z j))
          (@iso_evidence_to C x y i)))
≔ @eq_ap
    (Hom C x y)
    (Hom C x x)
    (λ q : τ (Hom C x y),
      @comp_fapp0 C x y x
        (@iso_evidence_from C x y i)
        q)
    (@comp_fapp0 C x z y
      (@iso_evidence_from C y z j)
      (@comp_fapp0 C x y z
        (@iso_evidence_to C y z j)
        (@iso_evidence_to C x y i)))
    (@comp_fapp0 C x y y
      (@comp_fapp0 C y z y
        (@iso_evidence_from C y z j)
        (@iso_evidence_to C y z j))
      (@iso_evidence_to C x y i))
    (@comp_assoc C x y z y
      (@iso_evidence_from C y z j)
      (@iso_evidence_to C y z j)
      (@iso_evidence_to C x y i));

// Left-cancellation proof step 3: replace `from(j) o to(j)` by identity.
symbol iso_evidence_comp_left_step3
  [C : Cat]
  [x y z : τ (Obj C)]
  (j : τ (IsoEvidence C y z))
  (i : τ (IsoEvidence C x y))
  : τ (
      @comp_fapp0 C x y x
        (@iso_evidence_from C x y i)
        (@comp_fapp0 C x y y
          (@comp_fapp0 C y z y
            (@iso_evidence_from C y z j)
            (@iso_evidence_to C y z j))
          (@iso_evidence_to C x y i))
      =
      @comp_fapp0 C x y x
        (@iso_evidence_from C x y i)
        (@iso_evidence_to C x y i))
≔ @eq_ap
    (Hom C y y)
    (Hom C x x)
    (λ m : τ (Hom C y y),
      @comp_fapp0 C x y x
        (@iso_evidence_from C x y i)
        (@comp_fapp0 C x y y
          m
          (@iso_evidence_to C x y i)))
    (@comp_fapp0 C y z y
      (@iso_evidence_from C y z j)
      (@iso_evidence_to C y z j))
    (@id C y)
    (@iso_evidence_left C y z j);

// Left inverse proof for the composite ordinary isomorphism evidence.
symbol iso_evidence_comp_left
  [C : Cat]
  [x y z : τ (Obj C)]
  (j : τ (IsoEvidence C y z))
  (i : τ (IsoEvidence C x y))
  : τ (
      @comp_fapp0 C x z x
        (@comp_fapp0 C z y x
          (@iso_evidence_from C x y i)
          (@iso_evidence_from C y z j))
        (@comp_fapp0 C x y z
          (@iso_evidence_to C y z j)
          (@iso_evidence_to C x y i))
      =
      @id C x)
≔ eq_trans
    (@iso_evidence_comp_left_step1 C x y z j i)
    (eq_trans
      (@iso_evidence_comp_left_step2 C x y z j i)
      (eq_trans
        (@iso_evidence_comp_left_step3 C x y z j i)
        (@iso_evidence_left C x y i)));

// Right-cancellation proof step 1: reassociate the outer composite.
symbol iso_evidence_comp_right_step1
  [C : Cat]
  [x y z : τ (Obj C)]
  (j : τ (IsoEvidence C y z))
  (i : τ (IsoEvidence C x y))
  : τ (
      @comp_fapp0 C z x z
        (@comp_fapp0 C x y z
          (@iso_evidence_to C y z j)
          (@iso_evidence_to C x y i))
        (@comp_fapp0 C z y x
          (@iso_evidence_from C x y i)
          (@iso_evidence_from C y z j))
      =
      @comp_fapp0 C z y z
        (@iso_evidence_to C y z j)
        (@comp_fapp0 C z x y
          (@iso_evidence_to C x y i)
          (@comp_fapp0 C z y x
            (@iso_evidence_from C x y i)
            (@iso_evidence_from C y z j))))
≔ @eq_sym
    (Hom C z z)
    (@comp_fapp0 C z y z
      (@iso_evidence_to C y z j)
      (@comp_fapp0 C z x y
        (@iso_evidence_to C x y i)
        (@comp_fapp0 C z y x
          (@iso_evidence_from C x y i)
          (@iso_evidence_from C y z j))))
    (@comp_fapp0 C z x z
      (@comp_fapp0 C x y z
        (@iso_evidence_to C y z j)
        (@iso_evidence_to C x y i))
      (@comp_fapp0 C z y x
        (@iso_evidence_from C x y i)
        (@iso_evidence_from C y z j)))
    (@comp_assoc C z x y z
      (@iso_evidence_to C y z j)
      (@iso_evidence_to C x y i)
      (@comp_fapp0 C z y x
        (@iso_evidence_from C x y i)
        (@iso_evidence_from C y z j)));

// Right-cancellation proof step 2: reassociate around the i inverse pair.
symbol iso_evidence_comp_right_step2
  [C : Cat]
  [x y z : τ (Obj C)]
  (j : τ (IsoEvidence C y z))
  (i : τ (IsoEvidence C x y))
  : τ (
      @comp_fapp0 C z y z
        (@iso_evidence_to C y z j)
        (@comp_fapp0 C z x y
          (@iso_evidence_to C x y i)
          (@comp_fapp0 C z y x
            (@iso_evidence_from C x y i)
            (@iso_evidence_from C y z j)))
      =
      @comp_fapp0 C z y z
        (@iso_evidence_to C y z j)
        (@comp_fapp0 C z y y
          (@comp_fapp0 C y x y
            (@iso_evidence_to C x y i)
            (@iso_evidence_from C x y i))
          (@iso_evidence_from C y z j)))
≔ @eq_ap
    (Hom C z y)
    (Hom C z z)
    (λ q : τ (Hom C z y),
      @comp_fapp0 C z y z
        (@iso_evidence_to C y z j)
        q)
    (@comp_fapp0 C z x y
      (@iso_evidence_to C x y i)
      (@comp_fapp0 C z y x
        (@iso_evidence_from C x y i)
        (@iso_evidence_from C y z j)))
    (@comp_fapp0 C z y y
      (@comp_fapp0 C y x y
        (@iso_evidence_to C x y i)
        (@iso_evidence_from C x y i))
      (@iso_evidence_from C y z j))
    (@comp_assoc C z y x y
      (@iso_evidence_to C x y i)
      (@iso_evidence_from C x y i)
      (@iso_evidence_from C y z j));

// Right-cancellation proof step 3: replace `to(i) o from(i)` by identity.
symbol iso_evidence_comp_right_step3
  [C : Cat]
  [x y z : τ (Obj C)]
  (j : τ (IsoEvidence C y z))
  (i : τ (IsoEvidence C x y))
  : τ (
      @comp_fapp0 C z y z
        (@iso_evidence_to C y z j)
        (@comp_fapp0 C z y y
          (@comp_fapp0 C y x y
            (@iso_evidence_to C x y i)
            (@iso_evidence_from C x y i))
          (@iso_evidence_from C y z j))
      =
      @comp_fapp0 C z y z
        (@iso_evidence_to C y z j)
        (@iso_evidence_from C y z j))
≔ @eq_ap
    (Hom C y y)
    (Hom C z z)
    (λ m : τ (Hom C y y),
      @comp_fapp0 C z y z
        (@iso_evidence_to C y z j)
        (@comp_fapp0 C z y y
          m
          (@iso_evidence_from C y z j)))
    (@comp_fapp0 C y x y
      (@iso_evidence_to C x y i)
      (@iso_evidence_from C x y i))
    (@id C y)
    (@iso_evidence_right C x y i);

// Right inverse proof for the composite ordinary isomorphism evidence.
symbol iso_evidence_comp_right
  [C : Cat]
  [x y z : τ (Obj C)]
  (j : τ (IsoEvidence C y z))
  (i : τ (IsoEvidence C x y))
  : τ (
      @comp_fapp0 C z x z
        (@comp_fapp0 C x y z
          (@iso_evidence_to C y z j)
          (@iso_evidence_to C x y i))
        (@comp_fapp0 C z y x
          (@iso_evidence_from C x y i)
          (@iso_evidence_from C y z j))
      =
      @id C z)
≔ eq_trans
    (@iso_evidence_comp_right_step1 C x y z j i)
    (eq_trans
      (@iso_evidence_comp_right_step2 C x y z j i)
      (eq_trans
        (@iso_evidence_comp_right_step3 C x y z j i)
        (@iso_evidence_right C y z j)));

// Composition of ordinary isomorphism evidence.
symbol iso_evidence_comp
  [C : Cat]
  [x y z : τ (Obj C)]
  (j : τ (IsoEvidence C y z))
  (i : τ (IsoEvidence C x y))
  : τ (IsoEvidence C x z)
≔ Struct_sigma
    (@comp_fapp0 C x y z
      (@iso_evidence_to C y z j)
      (@iso_evidence_to C x y i))
    (Struct_sigma
      (@comp_fapp0 C z y x
        (@iso_evidence_from C x y i)
        (@iso_evidence_from C y z j))
      (Struct_sigma
        (@iso_evidence_comp_left C x y z j i)
        (@iso_evidence_comp_right C x y z j i)));

// Strict functors preserve ordinary isomorphism evidence.
symbol iso_evidence_fmap
  [C D : Cat]
  (F : τ (Functor C D))
  [x y : τ (Obj C)]
  (i : τ (IsoEvidence C x y))
  : τ (IsoEvidence D (fapp0 F x) (fapp0 F y))
≔ Struct_sigma
    (@fapp1_fapp0 C D F x y
      (@iso_evidence_to C x y i))
    (Struct_sigma
      (@fapp1_fapp0 C D F y x
        (@iso_evidence_from C x y i))
      (Struct_sigma
        (@eq_ap
          (Hom C x x)
          (Hom D (fapp0 F x) (fapp0 F x))
          (λ p : τ (Hom C x x),
            @fapp1_fapp0 C D F x x p)
          (@comp_fapp0 C x y x
            (@iso_evidence_from C x y i)
            (@iso_evidence_to C x y i))
          (@id C x)
          (@iso_evidence_left C x y i))
        (@eq_ap
          (Hom C y y)
          (Hom D (fapp0 F y) (fapp0 F y))
          (λ p : τ (Hom C y y),
            @fapp1_fapp0 C D F y y p)
          (@comp_fapp0 C y x y
            (@iso_evidence_to C x y i)
            (@iso_evidence_from C x y i))
          (@id C y)
          (@iso_evidence_right C x y i))));

// Ordinary opposite functor action.
//
// Surface/formula:
//   Op_func(F) : A^op ⊢ B^op
//   Op_func(F)[x] = F[x]
//   Op_func(F)[f^op] = F[f]^op.
injective symbol Op_func : Π [A B : Cat],
  τ (Functor A B) → τ (Functor (Op_cat A) (Op_cat B));

// Opposite-functor involution and pointwise object/arrow computations.
rule Op_func (@Op_func $A $B $F) ↪ $F;

// Opposite functor has the same object action.
rule @fapp0 _ _ (@Op_func $A $B $F) $xA ↪ @fapp0 $A $B $F $xA;

// Full hom action of opposite reverses the source endpoints.
rule @fapp1_func _ _ (@Op_func $A $B $F) $X $Y ↪ @fapp1_func $A $B $F $Y $X;

// Capped arrow action of opposite reuses the underlying arrow action.
rule @fapp1_fapp0 _ _ (@Op_func $A $B $F) $X $Y $f
  ↪ @fapp1_fapp0 $A $B $F $Y $X $f;

// Opposite preserves identity and ordinary functor composition.
rule @Op_func _ _ (@id Cat_cat $A) ↪ @id Cat_cat (Op_cat $A);

// Projection-order bridge: opposite sends a composite functor to the composite of opposites.
rule @Op_func _ _ (@comp_fapp0 Cat_cat $A $B $C $F $G)
  ↪ comp_cat_fapp0 (Op_func $F) (Op_func $G);

// Terminal category and points-as-functors are needed to derive unary homs from
// binary homs.
//
// Surface/formula:
//   1 = Terminal_cat
//   Terminal_func(A) : A ⊢ 1
//   Obj_func(y) : 1 ⊢ Y picks out y : Obj(Y).
constant symbol Terminal_cat : Cat;

// Terminal normal forms: Obj(1)=Unit, Hom_1(*,*)=1, id/comp are Terminal_obj.
rule Op_cat Terminal_cat ↪ Terminal_cat;

// Object classifier of the terminal category is the unit groupoid.
rule Obj Terminal_cat ↪ Unit_grpd;

// Every terminal hom-category is terminal.
rule Hom_cat Terminal_cat _ _ ↪ Terminal_cat;

// Unique object of the terminal category.
constant symbol Terminal_obj : τ (Obj Terminal_cat);

// Terminal identity is the unique terminal object/arrow.
rule @id Terminal_cat _ ↪ Terminal_obj;

// Terminal composition is the unique terminal object/arrow.
rule @comp_fapp0 Terminal_cat _ _ _ _ _ ↪ Terminal_obj;

// Unique functor into the terminal category.
injective symbol Terminal_func : Π (A : Cat), τ (Functor A Terminal_cat);
// Opposite preserves the unique terminal-valued functor.
rule @Op_func _ _ (@Terminal_func $A) ↪ @Terminal_func (Op_cat $A);

// Evaluation at a fixed object, as a functor out of a functor category.
//
// Surface/formula:
//   fapp0_func(x)[F] = F[x].
symbol fapp0_func : Π [A B : Cat],
  τ (Obj A) → τ (Functor (Functor_cat A B) B);
// Evaluation functor object action: ev_x(F) ↪ F[x].
rule fapp0 (fapp0_func $x) $F ↪ fapp0 $F $x;

// Constant functor, used by constant directed families without capping the
// hom-action too early.
//
// Surface/formula:
//   Const_func(b) : A ⊢ B
//   Const_func(b)[x] = b
//   Const_func(b)[f] = id_b.
injective symbol Const_func [A B : Cat] (b : τ (Obj B)) : τ (Functor A B);
// Constant-functor object/arrow actions and functorial compatibility.
rule @fapp0 $A $B (@Const_func $A $B $b) $_ ↪ $b;

// Full hom action of a constant functor is constant at `id_b`.
rule @fapp1_func $A $B (@Const_func $A $B $b) $x $y
  ↪ @Const_func
      (Hom_cat $A $x $y)
      (Hom_cat $B $b $b)
      (@id $B $b);
// Capped arrow action of a constant functor is `id_b`.
rule @fapp1_fapp0 $A $B (@Const_func $A $B $b) $x $y $_ ↪ @id $B $b;

// Opposite preserves constant functors pointwise.
rule @Op_func $A $B (@Const_func $A $B $b)
  ↪ @Const_func (Op_cat $A) (Op_cat $B) $b;
// Postcomposing a constant functor evaluates the outer functor at its value.
rule @comp_fapp0 Cat_cat $A $B $C $F (@Const_func $A $B $b)
  ↪ @Const_func $A $C (@fapp0 $B $C $F $b);
// Precomposing a constant functor leaves it constant.
rule @comp_fapp0 Cat_cat $A $B $C (@Const_func $B $C $c) $G
  ↪ @Const_func $A $C $c;

// Point object as a functor from the terminal category.
//
// Surface/formula:
//   Obj_func(y) = const_1(y) : 1 ⊢ Y.
injective symbol Obj_func [Y : Cat] (y : τ (Obj Y)) : τ (Functor Terminal_cat Y)
≔ @Const_func Terminal_cat Y y;

// Internalized opposite as a functor in Cat.
//
// Surface/formula:
//   op : Cat ⊢ Cat
//   op[A] = A^op
//   op[F] = F^op.
constant symbol op : τ (Functor Cat_cat Cat_cat);
// Internal opposite action on categories and functors.
rule @fapp0 Cat_cat Cat_cat op $A ↪ Op_cat $A;
// Arrow action of the internal opposite functor is `Op_func`.
rule @fapp1_fapp0 Cat_cat Cat_cat op $A $B $F ↪ @Op_func $A $B $F;

// 3f. Internalized universe-level constructor packages
//
// Internalized ordinary functor-category formation. The total package has no
// recoverable parameters; the partial stage is injective so equality of
// packages can recover the fixed source category.
//
// Surface/formula:
//   Functor_cat_func[A][B] = A ⊢ B.
constant symbol Functor_cat_func : τ (Functor (Op_cat Cat_cat) (Functor_cat Cat_cat Cat_cat));

// Partial internalized functor-category constructor at fixed source A.
injective symbol Functor_cat_fapp0_func (A : Cat) : τ (Functor Cat_cat Cat_cat);

// First application of the binary constructor fixes the source category.
rule @fapp0 _ _ Functor_cat_func $A
  ↪ Functor_cat_fapp0_func $A;
// Second application yields the ordinary functor category `A ⊢ B`.
rule @fapp0 Cat_cat Cat_cat (Functor_cat_fapp0_func $A) $B
  ↪ Functor_cat $A $B;

// Internalized-x prerequisite: directed-family category formation as a
// universe-level functor.
//
// Surface/formula:
//   Catd_cat_func : Cat^op ⊢ Cat
//   Catd_cat_func[K] = Catd(K) = (K ⊢ Cat)
//   Catd_cat_func[F : A ⊢ B] = F^* : Catd(B) ⊢ Catd(A)
//
// This is the internal package that lets later constructions vary the base
// category. It is obtained by evaluating the internalized ordinary
// functor-category constructor at Cat_cat.
symbol Catd_cat_func : τ (Functor (Op_cat Cat_cat) Cat_cat)
≔ @comp_cat_fapp0
     (Op_cat Cat_cat)
     (Functor_cat Cat_cat Cat_cat)
     Cat_cat
     (@fapp0_func Cat_cat Cat_cat Cat_cat)
     Functor_cat_func;

// Derived classifier of displayed categories over the fibres of a displayed
// category. This is intentionally a semantic alias, not a new primitive:
//
//   Catd_catd_con(K) : Catd(Op_cat L)
//   Catd_catd_con(K)[l] = Catd_cat(K[l])
//   Catd_catd_con(K)[p^op] = Pullback_catd_func(K[p])
//
// The definition routes through the already-internalized constructor
// `Catd_cat_func : Cat^op ⊢ Cat` and the opposite of K.
symbol Catd_catd_con [L : Cat] (K : τ (Catd L)) : τ (Catd (Op_cat L))
≔ @comp_cat_fapp0
     (Op_cat L)
     (Op_cat Cat_cat)
     Cat_cat
     Catd_cat_func
     (@Op_func L Cat_cat K);

// Internalized pointwise opposite on directed families. This is the packaged
// functorial version of `Op_catd`; the object-level result remains the
// canonical normal form.
//
// Surface/formula:
//   Op_catd_func(Z)[E] = E^op.
injective symbol Op_catd_func (Z : Cat) : τ (Functor (Catd_cat Z) (Catd_cat Z));

// -------------------------------------------------------------------------------------------------
// 4. Ordinary internal hom and hom actions
// -------------------------------------------------------------------------------------------------

// 4a. Covariant represented hom families and postcomposition action

/*
  Ordinary internal hom classifiers.

  Surface/formula:
    hom_(F,W)[y]          = Hom_A(W,F[y])
    hom_postcomp_func(f)(g)= F[f] ∘ g
    hom_con(W,F)[y]       = Hom_A(F[y],W)
    hom_int(F)[W][y]      = Hom_A(W,F[y])
    hom_precomp_along_func(id_A,Z,f)(g)= g ∘ f

  `hom_int(F)` is the internalized functorial package
  A^op ⊢ (B ⊢ Cat). Its surface reading is:

    W :^n A^op ; 1[W] ⊢ (y :^n B ; 1[y] ⊢ Hom_A(W,F[y]))

  Design/SOP note:
    Use `hom_int(F)` when the varying endpoint is already functor-shaped.
    For example, for f : A ⊢ B, the outgoing comma family is naturally

      b ↦ Σ (a :^n A), Hom_B(b,f[a])

    and its hom-family part is `hom_int(f)[b]`. This avoids spelling the same
    idea as a raw post/precomposition pipeline first, where later rules would
    have to cut through `comp_cat_fapp0` before finding the hom-action owner.

  Simplicial reading:
    Fixing W and taking the Sigma total of hom_(F,W) gives the
    Grothendieck/coslice presentation: an object is an edge W ->^A F[y], and a
    total arrow is a base edge together with a comparison triangle/surface over
    it. This is the first simplicial presentation used by the later dependent
    hom iteration; it is a reading of existing hom/Sigma structure, not a
    separate kernel primitive.
*/
// Represented hom family with fixed source W: hom_(F,W)[y] = Hom_A(W,F[y]).
injective symbol hom_ [A B : Cat] (F : τ (Functor B A)) (W : τ (Obj A))
  : τ (Functor B Cat_cat);
// Object projection of the represented hom family.
rule @fapp0 $B Cat_cat (@hom_ $A $B $F $W) $y
  ↪ Hom_cat $A $W (@fapp0 $B $A $F $y);

// Ordinary hom-action computes by postcomposition:
// ((Hom_A(W,F-))_1 f)_0 g ↪ (F f) ∘ g.
rule fapp0 (@fapp1_fapp0 $B Cat_cat (@hom_ $A $B $F $W) $X $Y $f) $g
  ↪ comp_fapp0 (fapp1_fapp0 $F $f) $g;

/*
  Stable covariant hom-action projections.

  Mathematical notation:
    hom_postcomp_tele_func(F,W,X,Y)
      : Hom_B(X,Y) ⊢ (Hom_A(W,F[X]) ⊢ Hom_A(W,F[Y]))

    hom_postcomp_func(F,W,X,Y,f)[g] = F[f] ∘ g

    hom_postcomp_fapp1_func(F,W,X,Y,f,g,h)
      : Hom(g,h) ⊢ Hom(F[f] ∘ g, F[f] ∘ h)

    hom_postcomp_tele_fapp1_func(F,W,X,Y,f,g)
      : Hom(f,g) ⊢ Hom(hom_postcomp_func(f), hom_postcomp_func(g))

  Canonical comment syntax:
    Hom_A(W,F[-])[f](g)

  This is the functorial-in-f head for postcomposition. It keeps the arrow
  f : X ->^B Y visible long enough to expose the whole functor
  Hom_A(W,F[X]) ⊢ Hom_A(W,F[Y]), rather than capping immediately at a
  single g.
*/
// Telescope-level postcomposition: f ↦ (g ↦ F[f] ∘ g).
symbol hom_postcomp_tele_func [A B : Cat]
  (F : τ (Functor B A)) (W : τ (Obj A))
  [X Y : τ (Obj B)]
  : τ (Functor
      (Hom_cat B X Y)
      (Functor_cat
        (Hom_cat A W (@fapp0 B A F X))
        (Hom_cat A W (@fapp0 B A F Y))));

// Arrow action of hom_(F,W) exposes the postcomposition telescope.
rule @fapp1_func $B Cat_cat (@hom_ $A $B $F $W) $X $Y
  ↪ @hom_postcomp_tele_func $A $B $F $W $X $Y;

// Capped postcomposition functor: hom_postcomp_func(f)[g] = F[f] ∘ g.
symbol hom_postcomp_func [A B : Cat]
  (F : τ (Functor B A)) (W : τ (Obj A))
  [X Y : τ (Obj B)]
  (f : τ (Hom B X Y))
  : τ (Functor
      (Hom_cat A W (@fapp0 B A F X))
      (Hom_cat A W (@fapp0 B A F Y)));

// Stable object action of postcomposition: hom_postcomp_func(f)[g] = F[f] ∘ g.
//
// This head keeps the postcomposition cut visible for DefIso-style
// cancellation. Ordinary composition is the semantic reading, but the runtime
// normal form now records the hom-action owner instead of immediately erasing
// to the shared `comp_fapp0` head.
symbol hom_postcomp_fapp0 [A B : Cat]
  (F : τ (Functor B A)) (W : τ (Obj A))
  [X Y : τ (Obj B)]
  (f : τ (Hom B X Y))
  (g : τ (Hom A W (@fapp0 B A F X)))
  : τ (Hom A W (@fapp0 B A F Y));

// Applying the telescope to f yields the capped postcomposition functor.
rule fapp0 (@hom_postcomp_tele_func $A $B $F $W $X $Y) $f
  ↪ @hom_postcomp_func $A $B $F $W $X $Y $f;

// Direct capped arrow action of hom_(F,W) joins the telescope projection.
rule @fapp1_fapp0 $B Cat_cat (@hom_ $A $B $F $W) $X $Y $f
  ↪ @hom_postcomp_func $A $B $F $W $X $Y $f;

// Object action of postcomposition: keep the stable postcomposition head.
rule fapp0 (@hom_postcomp_func $A $B $F $W $X $Y $f) $g
  ↪ @hom_postcomp_fapp0 $A $B $F $W $X $Y $f $g;

// Generic object projection for Cat-valued postcomposition:
// hom_postcomp_E(p,G)[w] ↪ E[p](G[w]).
rule @fapp0
      _ _
      (@hom_postcomp_fapp0
        Cat_cat $B $E $W $X $Y $p $G)
      $w
  ↪ @fapp0
      (@fapp0 $B Cat_cat $E $X)
      (@fapp0 $B Cat_cat $E $Y)
      (@fapp1_fapp0 $B Cat_cat $E $X $Y $p)
      (@fapp0 $W (@fapp0 $B Cat_cat $E $X) $G $w);

// Capped arrow action of Cat-valued postcomposition:
//   (E[p] o G)[q] = E[p][G[q]].
//
// This is the arrow projection following the object projection above. It
// preserves the existing family and postcomposition owners rather than
// introducing a displayed-product constructor.
rule @fapp1_fapp0
      _ _
      (@hom_postcomp_fapp0
        Cat_cat $B $E $W $X $Y $p $G)
      $w
      $w'
      $q
  ↪ @fapp1_fapp0
      (@fapp0 $B Cat_cat $E $X)
      (@fapp0 $B Cat_cat $E $Y)
      (@fapp1_fapp0 $B Cat_cat $E $X $Y $p)
      (@fapp0 $W (@fapp0 $B Cat_cat $E $X) $G $w)
      (@fapp0 $W (@fapp0 $B Cat_cat $E $X) $G $w')
      (@fapp1_fapp0
        $W
        (@fapp0 $B Cat_cat $E $X)
        $G
        $w
        $w'
        $q);

// Hom-action functoriality for postcomposition. These joins prevent the
// stable postcomposition owner from hiding the functoriality already present
// in `hom_(F,W)`.
rule @hom_postcomp_func $A $B $F $W $X $X (@id $B $X)
  ↪ @id_func (Hom_cat $A $W (@fapp0 $B $A $F $X));

// Identity base arrow acts trivially at the stable postcomposition point head.
rule @hom_postcomp_fapp0 $A $B $F $W $X $X (@id $B $X) $g
  ↪ $g;

// Functor-level accumulation: consecutive postcomposition actions combine.
rule @comp_fapp0
      Cat_cat
      _ _ _
      (@hom_postcomp_func $A $B $F $W $Y $Z $q)
      (@hom_postcomp_func $A $B $F $W $X $Y $p)
  ↪ @hom_postcomp_func
      $A $B $F $W $X $Z
      (@comp_fapp0 $B $X $Y $Z $q $p);

// Point-level accumulation of consecutive postcomposition actions.
rule @hom_postcomp_fapp0
      $A $B $F $W $Y $Z $q
      (@hom_postcomp_fapp0 $A $B $F $W $X $Y $p $g)
  ↪ @hom_postcomp_fapp0
      $A $B $F $W $X $Z
      (@comp_fapp0 $B $X $Y $Z $q $p)
      $g;

// Raw adjacent-codomain postcomposition fold:
// F[q] o ((F[p])_*(g)) -> (F[q o p])_*(g).
rule @comp_fapp0
      $A
      _
      _
      _
      (@fapp1_fapp0 $B $A $F $Y $Z $q)
      (@hom_postcomp_fapp0 $A $B $F $W $X $Y $p $g)
  ↪ @hom_postcomp_fapp0
      $A
      $B
      $F
      $W
      $X
      $Z
      (@comp_fapp0 $B $X $Y $Z $q $p)
      $g;

// Identity-family nested postcomposition reassociates under the stable owner.
rule @hom_postcomp_fapp0
      $A $A (@id Cat_cat $A) $W $X $Z
      (@hom_postcomp_fapp0 $A $A (@id Cat_cat $A) $X $Y $Z $q $p)
      $g
  ↪ @hom_postcomp_fapp0
      $A $A (@id Cat_cat $A) $W $Y $Z $q
      (@hom_postcomp_fapp0 $A $A (@id Cat_cat $A) $W $X $Y $p $g);

// Postcomposition commutes with precomposition in the represented source
// object. This generic join is the hom-action replacement for profunctor-
// specific incoming-map naturality rules.
rule @comp_fapp0
      $A
      $V
      $W
      _
      (@hom_postcomp_fapp0 $A $B $F $W $X $Y $f $g)
      $h
  ↪ @hom_postcomp_fapp0
      $A $B $F $V $X $Y $f
      (@comp_fapp0
        $A
        $V
        $W
        (@fapp0 $B $A $F $X)
        $g
        $h);

// Identity cuts for the identity-functor postcomposition owner. These keep
// composition normalization at the stable postcomposition head instead of
// erasing to the shared `comp_fapp0` head.
rule @hom_postcomp_fapp0 $A $A (@id Cat_cat $A) $W $X $X (@id $A $X) $f ↪ $f
with @hom_postcomp_fapp0 $A $A (@id Cat_cat $A) $X $X $Y $f (@id $A $X) ↪ $f;

// Hom-action of the telescope as f varies: alpha : f ->^(Hom_B(X,Y)) g.
symbol hom_postcomp_tele_fapp1_func [A B : Cat]
  (F : τ (Functor B A)) (W : τ (Obj A))
  [X Y : τ (Obj B)]
  [f g : τ (Hom B X Y)]
  : τ (Functor
      (Hom_cat (Hom_cat B X Y) f g)
      (Hom_cat
        (Functor_cat
          (Hom_cat A W (@fapp0 B A F X))
          (Hom_cat A W (@fapp0 B A F Y)))
        (@hom_postcomp_func A B F W X Y f)
        (@hom_postcomp_func A B F W X Y g)));

// Capped hom-action of the postcomposition telescope.
symbol hom_postcomp_tele_fapp1_fapp0 [A B : Cat]
  (F : τ (Functor B A)) (W : τ (Obj A))
  [X Y : τ (Obj B)]
  [f g : τ (Hom B X Y)]
  (alpha : τ (Hom (Hom_cat B X Y) f g))
  : τ (Hom
      (Functor_cat
        (Hom_cat A W (@fapp0 B A F X))
        (Hom_cat A W (@fapp0 B A F Y)))
      (@hom_postcomp_func A B F W X Y f)
      (@hom_postcomp_func A B F W X Y g));

// Unspecialized transfor owner for the postcomposition telescope. Cat-valued
// instances expose ordinary transfor projections, but the owner itself is not
// Cat-specific.
symbol hom_postcomp_tele_transf [A B : Cat]
  (F : τ (Functor B A)) (W : τ (Obj A))
  [X Y : τ (Obj B)]
  [f g : τ (Hom B X Y)]
  (alpha : τ (Hom (Hom_cat B X Y) f g))
  : τ (Hom
      (Functor_cat
        (Hom_cat A W (@fapp0 B A F X))
        (Hom_cat A W (@fapp0 B A F Y)))
      (@hom_postcomp_func A B F W X Y f)
      (@hom_postcomp_func A B F W X Y g));

// Projection rules for the telescope hom-action.
rule @fapp1_func _ _ (@hom_postcomp_tele_func $A $B $F $W $X $Y) $f $g
  ↪ @hom_postcomp_tele_fapp1_func $A $B $F $W $X $Y $f $g;

// Applying the full telescope hom action yields its transfor component.
rule fapp0 (@hom_postcomp_tele_fapp1_func $A $B $F $W $X $Y $f $g) $alpha
  ↪ @hom_postcomp_tele_transf $A $B $F $W $X $Y $f $g $alpha;

// Direct capped telescope action joins the full-action projection.
rule @fapp1_fapp0 _ _ (@hom_postcomp_tele_func $A $B $F $W $X $Y) $f $g $alpha
  ↪ @hom_postcomp_tele_transf $A $B $F $W $X $Y $f $g $alpha;

// Runtime functoriality of the tele-level postcomposition stable head.
rule @hom_postcomp_tele_fapp1_fapp0
      $A $B $F $W $X $Y
      $f $f
      (@id _ $f)
  ↪ @id
      (Functor_cat
        (Hom_cat $A $W (@fapp0 $B $A $F $X))
        (Hom_cat $A $W (@fapp0 $B $A $F $Y)))
      (@hom_postcomp_func $A $B $F $W $X $Y $f);

// Telescope 2-cell composition accumulates inside the stable action head.
rule @comp_fapp0
      _
      _
      _
      _
      (@hom_postcomp_tele_fapp1_fapp0 $A $B $F $W $X $Y $g $h $e_gh)
      (@hom_postcomp_tele_fapp1_fapp0 $A $B $F $W $X $Y $f $g $e_fg)
  ↪ @hom_postcomp_tele_fapp1_fapp0
      $A
      $B
      $F
      $W
      $X
      $Y
      $f
      $h
      (@comp_fapp0 (Hom_cat $B $X $Y) $f $g $h $e_gh $e_fg);

// Hom-action of capped postcomposition on alpha : g ->^(Hom_A(W,F[X])) h.
symbol hom_postcomp_fapp1_func [A B : Cat]
  (F : τ (Functor B A)) (W : τ (Obj A))
  [X Y : τ (Obj B)]
  (f : τ (Hom B X Y))
  [g h : τ (Hom A W (@fapp0 B A F X))]
  : τ (Functor
      (Hom_cat (Hom_cat A W (@fapp0 B A F X)) g h)
      (Hom_cat
        (Hom_cat A W (@fapp0 B A F Y))
        (@hom_postcomp_fapp0 A B F W X Y f g)
        (@hom_postcomp_fapp0 A B F W X Y f h)));

// Capped hom-action of capped postcomposition.
symbol hom_postcomp_fapp1_fapp0 [A B : Cat]
  (F : τ (Functor B A)) (W : τ (Obj A))
  [X Y : τ (Obj B)]
  (f : τ (Hom B X Y))
  [g h : τ (Hom A W (@fapp0 B A F X))]
  (alpha : τ (Hom (Hom_cat A W (@fapp0 B A F X)) g h))
  : τ (Hom
      (Hom_cat A W (@fapp0 B A F Y))
      (@hom_postcomp_fapp0 A B F W X Y f g)
      (@hom_postcomp_fapp0 A B F W X Y f h));

// Projection rules for the capped postcomposition hom-action.
rule @fapp1_func _ _ (@hom_postcomp_func $A $B $F $W $X $Y $f) $g $h
  ↪ @hom_postcomp_fapp1_func $A $B $F $W $X $Y $f $g $h;

// Applying the full capped-action hom functor yields its point action.
rule fapp0 (@hom_postcomp_fapp1_func $A $B $F $W $X $Y $f $g $h) $alpha
  ↪ @hom_postcomp_fapp1_fapp0 $A $B $F $W $X $Y $f $g $h $alpha;

// Direct capped 2-cell action joins the full-action projection.
rule @fapp1_fapp0 _ _ (@hom_postcomp_func $A $B $F $W $X $Y $f) $g $h $alpha
  ↪ @hom_postcomp_fapp1_fapp0 $A $B $F $W $X $Y $f $g $h $alpha;

// Identity 2-cell under postcomposition maps to the identity at the stable
// postcomposition object action.
rule @hom_postcomp_fapp1_fapp0
      $A
      $B
      $F
      $W
      $X
      $Y
      $f
      $g
      $g
      (@id _ $g)
  ↪ @id
      (Hom_cat $A $W (@fapp0 $B $A $F $Y))
      (@hom_postcomp_fapp0 $A $B $F $W $X $Y $f $g);

// Proof-time raw-composition reading of the stable postcomposition point head.
unif_rule @hom_postcomp_fapp0 $A $B $F $W $X $Y $h $g
  ≡ @comp_fapp0
      $A
      $W
      _
      _
      (@fapp1_fapp0 $B $A $F $X $Y $h)
      $g
  ↪ [ tt ≡ tt ];

// Proof-time identity-family comparison with ordinary raw composition.
unif_rule @hom_postcomp_fapp0 $A $A (@id Cat_cat $A) $W $X $Y $h $g
  ≡ @comp_fapp0 $A $W $X $Y $h $g
  ↪ [ tt ≡ tt ];

// Proof-time bridge between a general postcomposition endpoint and its
// identity-functor presentation. Both sides already identify with the same
// raw composition; this direct bridge avoids relying on transitive unification
// search when higher component rules need matching endpoints.
unif_rule @hom_postcomp_fapp0 $A $B $F $W $X $Y $h $g
  ≡ @hom_postcomp_fapp0
      $A
      $A
      (@id Cat_cat $A)
      $W
      _
      _
      (@fapp1_fapp0 $B $A $F $X $Y $h)
      $g
  ↪ [ tt ≡ tt ];

// 4b. Computational isomorphisms under the represented hom-action owner

/*
  Definitional/computational isomorphisms.

  `IsoEvidence(C,x,y)` is ordinary propositional inverse data. `DefIso`
  records the stricter Lambdapi-specific situation where inverse cancellation
  is judgmental under the stable postcomposition owner. This is the
  postcomposition/consequent variant; a dual precomposition/antecedent variant
  can be added later if consumed.
*/
injective symbol DefIso
  [C : Cat]
  (x y : τ (Obj C))
  : Grpd;

// Selected forward arrow of a computational isomorphism.
symbol defiso_to
  [C : Cat]
  [x y : τ (Obj C)]
  (i : τ (@DefIso C x y))
  : τ (Hom C x y);

// Selected inverse arrow of a computational isomorphism.
symbol defiso_from
  [C : Cat]
  [x y : τ (Obj C)]
  (i : τ (@DefIso C x y))
  : τ (Hom C y x);

// Reflexive computational isomorphism.
injective symbol defiso_refl
  [C : Cat]
  (x : τ (Obj C))
  : τ (@DefIso C x x);

// Forward/inverse projections of reflexivity are identity arrows.
rule @defiso_to $C $x $x (@defiso_refl $C $x)
  ↪ @id $C $x
with @defiso_from $C $x $x (@defiso_refl $C $x)
  ↪ @id $C $x;

// Symmetry of computational isomorphism.
injective symbol defiso_sym
  [C : Cat]
  [x y : τ (Obj C)]
  (i : τ (@DefIso C x y))
  : τ (@DefIso C y x);

// Symmetry swaps the forward and inverse projections.
rule @defiso_to $C $y $x (@defiso_sym $C $x $y $i)
  ↪ @defiso_from $C $x $y $i
with @defiso_from $C $y $x (@defiso_sym $C $x $y $i)
  ↪ @defiso_to $C $x $y $i;

// DefIso beta: postcomposing by `to` after `from` cancels.
rule @hom_postcomp_fapp0
      $A $C $F $W $y $x
      (@defiso_from $C $x $y $i)
      (@hom_postcomp_fapp0
        $A $C $F $W $x $y
        (@defiso_to $C $x $y $i)
        $f)
  ↪ $f
with @hom_postcomp_fapp0
      $A $C $F $W $x $y
      (@defiso_to $C $x $y $i)
      (@hom_postcomp_fapp0
        $A $C $F $W $y $x
        (@defiso_from $C $x $y $i)
        $g)
  ↪ $g;

// DefIso eta: postcomposing by `from` after `to` cancels.
rule @hom_postcomp_fapp0
      $C $C (@id Cat_cat $C) $x $y $x
      (@defiso_from $C $x $y $i)
      (@defiso_to $C $x $y $i)
  ↪ @id $C $x
with @hom_postcomp_fapp0
      $C $C (@id Cat_cat $C) $y $x $y
      (@defiso_to $C $x $y $i)
      (@defiso_from $C $x $y $i)
  ↪ @id $C $y;

// Raw right-inverse cut joins the same computational cancellation.
rule @comp_fapp0
      $C $x $y $x
      (@defiso_from $C $x $y $i)
      (@defiso_to $C $x $y $i)
  ↪  @id $C $x;

// Raw left-inverse cut joins the same computational cancellation.
rule @comp_fapp0
      $C $y $x $y
      (@defiso_to $C $x $y $i)
      (@defiso_from $C $x $y $i)
  ↪  @id $C $y;

// Forget a computational isomorphism to ordinary propositional evidence.
symbol defiso_iso_evidence
  [C : Cat]
  [x y : τ (Obj C)]
  (i : τ (@DefIso C x y))
  : τ (@IsoEvidence C x y);

// Forward-arrow projection of the ordinary evidence view.
rule sigma_Fst (@defiso_iso_evidence $C $x $y $i)
  ↪ @defiso_to $C $x $y $i;

// Inverse-arrow projection of the ordinary evidence view.
rule sigma_Fst (sigma_Snd (@defiso_iso_evidence $C $x $y $i))
  ↪ @defiso_from $C $x $y $i;

// Left inverse evidence is reflexivity after computational cancellation.
rule sigma_Fst (sigma_Snd (sigma_Snd (@defiso_iso_evidence $C $x $y $i)))
  ↪ eq_refl
      (@comp_fapp0 $C $x $y $x
        (@defiso_from $C $x $y $i)
        (@defiso_to $C $x $y $i));

// Right inverse evidence is reflexivity after computational cancellation.
rule sigma_Snd (sigma_Snd (sigma_Snd (@defiso_iso_evidence $C $x $y $i)))
  ↪ eq_refl
      (@comp_fapp0 $C $y $x $y
        (@defiso_to $C $x $y $i)
        (@defiso_from $C $x $y $i));

// Composition of computational isomorphisms.
injective symbol defiso_comp
  [C : Cat]
  [x y z : τ (Obj C)]
  (j : τ (@DefIso C y z))
  (i : τ (@DefIso C x y))
  : τ (@DefIso C x z);

// Composite forward/inverse projections compose in opposite orders.
rule @defiso_to $C $x $z (@defiso_comp $C $x $y $z $j $i)
  ↪ @hom_postcomp_fapp0
      $C $C (@id_func $C) $x $y $z
      (@defiso_to $C $y $z $j)
      (@defiso_to $C $x $y $i)
with @defiso_from $C $x $z (@defiso_comp $C $x $y $z $j $i)
  ↪ @hom_postcomp_fapp0
      $C $C (@id_func $C) $z $y $x
      (@defiso_from $C $x $y $i)
      (@defiso_from $C $y $z $j);

// Composite DefIso cancellation accumulates nested stable postcomposition cuts.
rule @hom_postcomp_fapp0
      $C $C (@id Cat_cat $C) $x $z $x
      (@hom_postcomp_fapp0
        $C $C (@id Cat_cat $C) $z $y $x
        (@defiso_from $C $x $y $i)
        (@defiso_from $C $y $z $j))
      (@hom_postcomp_fapp0
        $C $C (@id Cat_cat $C) $x $y $z
        (@defiso_to $C $y $z $j)
        (@defiso_to $C $x $y $i))
  ↪ @id $C $x
with @hom_postcomp_fapp0
      $C $C (@id Cat_cat $C) $z $x $z
      (@hom_postcomp_fapp0
        $C $C (@id Cat_cat $C) $x $y $z
        (@defiso_to $C $y $z $j)
        (@defiso_to $C $x $y $i))
      (@hom_postcomp_fapp0
        $C $C (@id Cat_cat $C) $z $y $x
        (@defiso_from $C $x $y $i)
        (@defiso_from $C $y $z $j))
  ↪ @id $C $z;

// Functorial image of a computational isomorphism.
injective symbol defiso_fmap
  [C D : Cat]
  (F : τ (Functor C D))
  [x y : τ (Obj C)]
  (i : τ (@DefIso C x y))
  : τ (@DefIso D (@fapp0 C D F x) (@fapp0 C D F y));

// Functorial image projects by applying the functor to both selected arrows.
rule @defiso_to
      $D
      _ _
      (@defiso_fmap $C $D $F $x $y $i)
  ↪ @fapp1_fapp0 $C $D $F $x $y (@defiso_to $C $x $y $i)
with @defiso_from
      $D
      _ _
      (@defiso_fmap $C $D $F $x $y $i)
  ↪ @fapp1_fapp0 $C $D $F $y $x (@defiso_from $C $x $y $i);

// Left cancellation of a mapped DefIso under the target hom-action owner.
// The three hom endpoints are inferred from the mapped arrows. Keeping their
// explicit fapp0 projections would make object beta erase the owner pattern.
rule @hom_postcomp_fapp0
      $D $D (@id Cat_cat $D)
      _ _ _
      (@fapp1_fapp0 $C $D $F $y $x (@defiso_from $C $x $y $i))
      (@fapp1_fapp0 $C $D $F $x $y (@defiso_to $C $x $y $i))
  ↪ @id $D (@fapp0 $C $D $F $x)
with @hom_postcomp_fapp0
      $D $D (@id Cat_cat $D)
      _ _ _
      (@fapp1_fapp0 $C $D $F $x $y (@defiso_to $C $x $y $i))
      (@fapp1_fapp0 $C $D $F $y $x (@defiso_from $C $x $y $i))
  ↪ @id $D (@fapp0 $C $D $F $y);

// Right cancellation of a mapped DefIso under the target hom-action owner.
rule @hom_postcomp_fapp0
      $D $D (@id Cat_cat $D)
      $W _ _
      (@fapp1_fapp0 $C $D $F $y $x (@defiso_from $C $x $y $i))
      (@hom_postcomp_fapp0
        $D $D (@id Cat_cat $D)
        $W _ _
        (@fapp1_fapp0 $C $D $F $x $y (@defiso_to $C $x $y $i))
        $f)
  ↪ $f
with @hom_postcomp_fapp0
      $D $D (@id Cat_cat $D)
      $W _ _
      (@fapp1_fapp0 $C $D $F $x $y (@defiso_to $C $x $y $i))
      (@hom_postcomp_fapp0
        $D $D (@id Cat_cat $D)
        $W _ _
        (@fapp1_fapp0 $C $D $F $y $x (@defiso_from $C $x $y $i))
        $g)
  ↪ $g;

// Forgetful view preserves reflexivity.
rule @defiso_iso_evidence $C $x $x (@defiso_refl $C $x)
  ↪ @iso_evidence_refl $C $x;

// Forgetful view preserves symmetry.
rule @defiso_iso_evidence $C $y $x (@defiso_sym $C $x $y $i)
  ↪ @iso_evidence_sym
      $C $x $y
      (@defiso_iso_evidence $C $x $y $i);

// Forgetful view preserves composition.
rule @defiso_iso_evidence $C $x $z (@defiso_comp $C $x $y $z $j $i)
  ↪ @iso_evidence_comp
      $C $x $y $z
      (@defiso_iso_evidence $C $y $z $j)
      (@defiso_iso_evidence $C $x $y $i);

// Forgetful view preserves functorial image.
rule @defiso_iso_evidence
      $D
      _ _
      (@defiso_fmap $C $D $F $x $y $i)
  ↪ @iso_evidence_fmap
      $C $D $F $x $y
      (@defiso_iso_evidence $C $x $y $i);

// 4c. Contravariant represented hom families and precomposition action

// Contravariant represented-object classifier.
//
// Surface/formula:
//   hom_con(W,F)[y] = Hom_A(F[y],W).
injective symbol hom_con [A : Cat] (W : τ (Obj A)) [B : Cat] (F : τ (Functor B A))
  : τ (Functor (Op_cat B) Cat_cat);

// Direct object projection preserves contravariant runtime ownership without
// discriminating on an opposite-functor presentation.
rule @fapp0 _ Cat_cat (@hom_con $A $W $B $F) $x
  ↪ Hom_cat $A (@fapp0 $B $A $F $x) $W;

/*
  Generalized precomposition along a functor, routed through the semantic
  contravariant representable.

  Mathematical notation:
    hom_precomp_along_tele_func(F,Z,W,X)
      : Hom_A(W,X) ⊢ (Hom_B(F[X],Z) ⊢ Hom_B(F[W],Z))

    hom_precomp_along_func(F,Z,h)[g] = g ∘ F[h]

    hom_precomp_along_fapp1_func(F,Z,h,g,k)
      : Hom(g,k) ⊢ Hom(g ∘ F[h], k ∘ F[h])

    hom_precomp_along_tele_fapp1_func(F,Z,W,X,h,k)
      : Hom(h,k) ⊢ Hom(hom_precomp_along_func(h), hom_precomp_along_func(k))

  When F is the identity functor, this is ordinary represented-object
  precomposition: g maps to g ∘ h.
*/
// Telescope-level precomposition: h ↦ (g ↦ g ∘ F[h]).
symbol hom_precomp_along_tele_func [A B : Cat]
  (F : τ (Functor A B)) (Z : τ (Obj B))
  [W X : τ (Obj A)]
  : τ (Functor
      (Hom_cat A W X)
      (Functor_cat
        (Hom_cat B (@fapp0 A B F X) Z)
        (Hom_cat B (@fapp0 A B F W) Z)));

// Cat-valued precomposition remains owned by the generic hom-action heads.
// The Cat helper names are now transparent aliases for the identity-family
// case, so reverse folds from `hom_precomp_along_*` to `comp_cat_*` are omitted.

// Capped precomposition functor: hom_precomp_along_func(h)[g] = g ∘ F[h].
symbol hom_precomp_along_func [A B : Cat]
  (F : τ (Functor A B)) (Z : τ (Obj B))
  [W X : τ (Obj A)]
  (h : τ (Hom A W X))
  : τ (Functor
      (Hom_cat B (@fapp0 A B F X) Z)
      (Hom_cat B (@fapp0 A B F W) Z));

// Stable object action of precomposition: hom_precomp_along_func(h)[g] = g ∘ F[h].
//
// This is the antecedent/precomposition counterpart to `hom_postcomp_fapp0`.
// It keeps the cut owner visible while proof-time unification records the
// ordinary composition reading.
symbol hom_precomp_along_fapp0 [A B : Cat]
  (F : τ (Functor A B)) (Z : τ (Obj B))
  [W X : τ (Obj A)]
  (h : τ (Hom A W X))
  (g : τ (Hom B (@fapp0 A B F X) Z))
  : τ (Hom B (@fapp0 A B F W) Z);

// Full contravariant action with the source category retained in its literal
// opposite presentation. Its object projection returns the existing
// precomposition owner.
symbol hom_con_precomp_tele_func [A B : Cat]
  (F : τ (Functor B A)) (W : τ (Obj A))
  [X Y : τ (Obj B)]
  : τ (Functor
      (Hom_cat (Op_cat B) X Y)
      (Functor_cat
        (Hom_cat A (@fapp0 B A F X) W)
        (Hom_cat A (@fapp0 B A F Y) W)));

// Arrow projections of hom_con route to the literal-opposite full owner and
// the existing capped precomposition owner.
rule @fapp1_func
      _ Cat_cat
      (@hom_con $A $W $B $F)
      $X $Y
  ↪ @hom_con_precomp_tele_func $A $B $F $W $X $Y;

// Applying the contravariant telescope at p yields the capped precomposition functor.
rule fapp0 (@hom_con_precomp_tele_func $A $B $F $W $X $Y) $p
  ↪ @hom_precomp_along_func $B $A $F $W $Y $X $p;

// Direct contravariant capped action joins the telescope projection.
rule @fapp1_fapp0
      _ Cat_cat
      (@hom_con $A $W $B $F)
      $X $Y $p
  ↪ @hom_precomp_along_func $B $A $F $W $Y $X $p;

// Applying the telescope to h yields the capped precomposition functor.
rule fapp0 (@hom_precomp_along_tele_func $A $B $F $Z $W $X) $h
  ↪ @hom_precomp_along_func $A $B $F $Z $W $X $h;

// Object action of precomposition: keep the stable precomposition head.
rule fapp0 (@hom_precomp_along_func $A $B $F $Z $W $X $h) $g
  ↪ @hom_precomp_along_fapp0 $A $B $F $Z $W $X $h $g;

// Hom-action functoriality for precomposition. The composition orientation is
// contravariant in the acted-on base arrow: first precompose by q, then by p.
rule @hom_precomp_along_func $A $B $F $Z $X $X (@id $A $X)
  ↪ @id_func (Hom_cat $B (@fapp0 $A $B $F $X) $Z);

// Identity base arrow acts trivially at the stable precomposition point head.
rule @hom_precomp_along_fapp0 $A $B $F $Z $X $X (@id $A $X) $g
  ↪ $g;

// Functor-level contravariant accumulation of consecutive precomposition actions.
rule @comp_fapp0
      Cat_cat
      _ _ _
      (@hom_precomp_along_func $A $B $F $Z $W $X $p)
      (@hom_precomp_along_func $A $B $F $Z $X $Y $q)
  ↪ @hom_precomp_along_func
      $A $B $F $Z $W $Y
      (@comp_fapp0 $A $W $X $Y $q $p);

// Point-level contravariant accumulation of consecutive precomposition actions.
rule @hom_precomp_along_fapp0
      $A $B $F $Z $W $X $p
      (@hom_precomp_along_fapp0 $A $B $F $Z $X $Y $q $g)
  ↪ @hom_precomp_along_fapp0
      $A $B $F $Z $W $Y
      (@comp_fapp0 $A $W $X $Y $q $p)
      $g;

// Raw adjacent-source precomposition fold:
// ((F[p])^*(g)) o F[q] -> (F[p o q])^*(g).
rule @comp_fapp0
      $B
      _
      _
      _
      (@hom_precomp_along_fapp0 $A $B $F $Z $W $X $p $g)
      (@fapp1_fapp0 $A $B $F $V $W $q)
  ↪ @hom_precomp_along_fapp0
      $A
      $B
      $F
      $Z
      $V
      $X
      (@comp_fapp0 $A $V $W $X $p $q)
      $g;

// Precomposing the identity at F[X] by h returns the functorial action F[h].
// The first rule covers unreduced generic identities; the `Cat_cat` and
// `Catd_cat` rules cover the normal forms of category and displayed-category
// identities.
// Identity-family codomain accumulation remains under the precomposition owner.
rule @hom_precomp_along_fapp0
      $A
      $B
      $F
      _
      $W
      $X
      $h
      (@id $B _)
  ↪ @fapp1_fapp0 $A $B $F $W $X $h;

// Identity-family left identity cut for stable precomposition.
rule @hom_precomp_along_fapp0
      $A
      Cat_cat
      $F
      _
      $W
      $X
      $h
      (@id Cat_cat _)
  ↪ @fapp1_fapp0 $A Cat_cat $F $W $X $h;

// Catd-valued left identity cut for stable precomposition.
rule @hom_precomp_along_fapp0
      $A
      (@Catd_cat $K)
      $F
      _
      $W
      $X
      $h
      (@id (@Catd_cat $K) _)
  ↪ @fapp1_fapp0 $A (@Catd_cat $K) $F $W $X $h;

// Proof-time raw-composition reading of the stable precomposition point head.
unif_rule @hom_precomp_along_fapp0 $A $B $F $Z $W $X $h $g
  ≡ @comp_fapp0
      $B
      _
      _
      $Z
      $g
      (@fapp1_fapp0 $A $B $F $W $X $h)
  ↪ [ tt ≡ tt ];

// Proof-time identity-family comparison with ordinary raw composition.
unif_rule @hom_precomp_along_fapp0 $A $A (@id Cat_cat $A) $Z $W $X $h $g
  ≡ @comp_fapp0
      $A
      _
      _
      $Z
      $g
      $h
  ↪ [ tt ≡ tt ];

/*
  Propositional join for postcomposition outside stable precomposition:

    k o (g o F[h]) = (k o g) o F[h].

  Runtime keeps the stable precomposition and raw-composition owners distinct.
  This theorem stages their proof-time comparison explicitly around the
  ordinary associator instead of relying on transitivity of `unif_rule`.
*/
symbol hom_precomp_along_postcomp_assoc
  [A B : Cat]
  (F : τ (Functor A B))
  [W X : τ (Obj A)]
  (h : τ (Hom A W X))
  [Z U : τ (Obj B)]
  (k : τ (Hom B Z U))
  (g : τ (Hom B (@fapp0 A B F X) Z))
  : τ (@=
      (Hom B (@fapp0 A B F W) U)
      (@comp_fapp0
        B (@fapp0 A B F W) Z U
        k
        (@hom_precomp_along_fapp0 A B F Z W X h g))
      (@hom_precomp_along_fapp0
        A B F U W X h
        (@comp_fapp0 B (@fapp0 A B F X) Z U k g)))
≔ @eq_trans
    (Hom B (@fapp0 A B F W) U)
    (@comp_fapp0
      B (@fapp0 A B F W) Z U
      k
      (@hom_precomp_along_fapp0 A B F Z W X h g))
    (@comp_fapp0
      B (@fapp0 A B F W) Z U
      k
      (@comp_fapp0
        B (@fapp0 A B F W) (@fapp0 A B F X) Z
        g
        (@fapp1_fapp0 A B F W X h)))
    (@hom_precomp_along_fapp0
      A B F U W X h
      (@comp_fapp0 B (@fapp0 A B F X) Z U k g))
    (@eq_ap
      (Hom B (@fapp0 A B F W) Z)
      (Hom B (@fapp0 A B F W) U)
      (λ q : τ (Hom B (@fapp0 A B F W) Z),
        @comp_fapp0 B (@fapp0 A B F W) Z U k q)
      (@hom_precomp_along_fapp0 A B F Z W X h g)
      (@comp_fapp0
        B (@fapp0 A B F W) (@fapp0 A B F X) Z
        g
        (@fapp1_fapp0 A B F W X h))
      (@eq_refl
        (Hom B (@fapp0 A B F W) Z)
        (@hom_precomp_along_fapp0 A B F Z W X h g)))
    (@eq_trans
      (Hom B (@fapp0 A B F W) U)
      (@comp_fapp0
        B (@fapp0 A B F W) Z U
        k
        (@comp_fapp0
          B (@fapp0 A B F W) (@fapp0 A B F X) Z
          g
          (@fapp1_fapp0 A B F W X h)))
      (@comp_fapp0
        B (@fapp0 A B F W) (@fapp0 A B F X) U
        (@comp_fapp0 B (@fapp0 A B F X) Z U k g)
        (@fapp1_fapp0 A B F W X h))
      (@hom_precomp_along_fapp0
        A B F U W X h
        (@comp_fapp0 B (@fapp0 A B F X) Z U k g))
      (@comp_assoc
        B
        (@fapp0 A B F W)
        (@fapp0 A B F X)
        Z U
        k g
        (@fapp1_fapp0 A B F W X h))
      (@eq_refl
        (Hom B (@fapp0 A B F W) U)
        (@comp_fapp0
          B (@fapp0 A B F W) (@fapp0 A B F X) U
          (@comp_fapp0 B (@fapp0 A B F X) Z U k g)
          (@fapp1_fapp0 A B F W X h))));

// Proof-time endpoint bridge for the component of a general postcomposition
// action. Runtime keeps the precomposition and postcomposition owners
// distinct; this direct comparison avoids relying on transitive unification
// through their separate identity-postcomposition and raw-composition views.
unif_rule @hom_postcomp_fapp0
      $A $B $F $W $X $Y $h $g
  ≡ @hom_precomp_along_fapp0
      $A $A (@id Cat_cat $A)
      (@fapp0 $B $A $F $Y)
      $W
      (@fapp0 $B $A $F $X)
      $g
      (@fapp1_fapp0 $B $A $F $X $Y $h)
  ↪ [ tt ≡ tt ];

// The already-normalized identity-family presentation needs its own direct
// rigid-head bridge because unification does not reliably reduce the generic
// functor-action arguments while selecting the rule above.
unif_rule @hom_precomp_along_fapp0
      $A $A (@id Cat_cat $A) $Z $W $X $h $g
  ≡ @hom_postcomp_fapp0
      $A $A (@id Cat_cat $A) $W $X $Z $g $h
  ↪ [ tt ≡ tt ];

// Fold-direction codomain accumulation for precomposition.
rule @comp_fapp0
      $B
      _
      $Z
      $U
      $k
      (@hom_precomp_along_fapp0 $A $B $F $Z $W $X $p $g)
  ↪ @hom_precomp_along_fapp0
      $A
      $B
      $F
      $U
      $W
      $X
      $p
      (@comp_fapp0 $B (@fapp0 $A $B $F $X) $Z $U $k $g);

// Hom-action of the telescope as h varies: alpha : h ->^(Hom_A(W,X)) k.
symbol hom_precomp_along_tele_fapp1_func [A B : Cat]
  (F : τ (Functor A B)) (Z : τ (Obj B))
  [W X : τ (Obj A)]
  [h k : τ (Hom A W X)]
  : τ (Functor
      (Hom_cat (Hom_cat A W X) h k)
      (Hom_cat
        (Functor_cat
          (Hom_cat B (@fapp0 A B F X) Z)
          (Hom_cat B (@fapp0 A B F W) Z))
        (@hom_precomp_along_func A B F Z W X h)
        (@hom_precomp_along_func A B F Z W X k)));

// Capped hom-action of the precomposition telescope.
symbol hom_precomp_along_tele_fapp1_fapp0 [A B : Cat]
  (F : τ (Functor A B)) (Z : τ (Obj B))
  [W X : τ (Obj A)]
  [h k : τ (Hom A W X)]
  (alpha : τ (Hom (Hom_cat A W X) h k))
  : τ (Hom
      (Functor_cat
        (Hom_cat B (@fapp0 A B F X) Z)
        (Hom_cat B (@fapp0 A B F W) Z))
      (@hom_precomp_along_func A B F Z W X h)
      (@hom_precomp_along_func A B F Z W X k));

// Unspecialized transfor owner for the precomposition telescope.
symbol hom_precomp_along_tele_transf [A B : Cat]
  (F : τ (Functor A B)) (Z : τ (Obj B))
  [W X : τ (Obj A)]
  [h k : τ (Hom A W X)]
  (alpha : τ (Hom (Hom_cat A W X) h k))
  : τ (Hom
      (Functor_cat
        (Hom_cat B (@fapp0 A B F X) Z)
        (Hom_cat B (@fapp0 A B F W) Z))
      (@hom_precomp_along_func A B F Z W X h)
      (@hom_precomp_along_func A B F Z W X k));

// Projection rules for the precomposition telescope hom-action.
rule @fapp1_func _ _ (@hom_precomp_along_tele_func $A $B $F $Z $W $X) $h $k
  ↪ @hom_precomp_along_tele_fapp1_func $A $B $F $Z $W $X $h $k;

// Applying the full precomposition telescope hom action yields its transfor.
rule fapp0 (@hom_precomp_along_tele_fapp1_func $A $B $F $Z $W $X $h $k) $alpha
  ↪ @hom_precomp_along_tele_transf $A $B $F $Z $W $X $h $k $alpha;

// Direct capped telescope action joins the full-action projection.
rule @fapp1_fapp0 _ _ (@hom_precomp_along_tele_func $A $B $F $Z $W $X) $h $k $alpha
  ↪ @hom_precomp_along_tele_transf $A $B $F $Z $W $X $h $k $alpha;

// Runtime functoriality of the tele-level precomposition stable head.
rule @hom_precomp_along_tele_fapp1_fapp0
      $A $B $F $Z $W $X
      $h $h
      (@id _ $h)
  ↪ @id
      (Functor_cat
        (Hom_cat $B (@fapp0 $A $B $F $X) $Z)
        (Hom_cat $B (@fapp0 $A $B $F $W) $Z))
      (@hom_precomp_along_func $A $B $F $Z $W $X $h);

// Precomposition-telescope 2-cell composition accumulates inside the stable head.
rule @comp_fapp0
      _
      _
      _
      _
      (@hom_precomp_along_tele_fapp1_fapp0 $A $B $F $Z $W $X $g $h $e_gh)
      (@hom_precomp_along_tele_fapp1_fapp0 $A $B $F $Z $W $X $f $g $e_fg)
  ↪ @hom_precomp_along_tele_fapp1_fapp0
      $A
      $B
      $F
      $Z
      $W
      $X
      $f
      $h
      (@comp_fapp0 (Hom_cat $A $W $X) $f $g $h $e_gh $e_fg);

// Hom-action of capped precomposition on alpha : g ->^(Hom_B(F[X],Z)) k.
symbol hom_precomp_along_fapp1_func [A B : Cat]
  (F : τ (Functor A B)) (Z : τ (Obj B))
  [W X : τ (Obj A)]
  (h : τ (Hom A W X))
  [g k : τ (Hom B (@fapp0 A B F X) Z)]
  : τ (Functor
      (Hom_cat (Hom_cat B (@fapp0 A B F X) Z) g k)
        (Hom_cat
          (Hom_cat B (@fapp0 A B F W) Z)
        (@hom_precomp_along_fapp0 A B F Z W X h g)
        (@hom_precomp_along_fapp0 A B F Z W X h k)));

// Capped hom-action of capped precomposition.
symbol hom_precomp_along_fapp1_fapp0 [A B : Cat]
  (F : τ (Functor A B)) (Z : τ (Obj B))
  [W X : τ (Obj A)]
  (h : τ (Hom A W X))
  [g k : τ (Hom B (@fapp0 A B F X) Z)]
  (alpha : τ (Hom (Hom_cat B (@fapp0 A B F X) Z) g k))
      : τ (Hom
      (Hom_cat B (@fapp0 A B F W) Z)
      (@hom_precomp_along_fapp0 A B F Z W X h g)
      (@hom_precomp_along_fapp0 A B F Z W X h k));

// Projection rules for the capped precomposition hom-action.
rule @fapp1_func _ _ (@hom_precomp_along_func $A $B $F $Z $W $X $h) $g $k
  ↪ @hom_precomp_along_fapp1_func $A $B $F $Z $W $X $h $g $k;

// Applying the full capped precomposition action yields its point action.
rule fapp0 (@hom_precomp_along_fapp1_func $A $B $F $Z $W $X $h $g $k) $alpha
  ↪ @hom_precomp_along_fapp1_fapp0 $A $B $F $Z $W $X $h $g $k $alpha;

// Direct capped 2-cell action joins the full-action projection.
rule @fapp1_fapp0 _ _ (@hom_precomp_along_func $A $B $F $Z $W $X $h) $g $k $alpha
  ↪ @hom_precomp_along_fapp1_fapp0 $A $B $F $Z $W $X $h $g $k $alpha;

// Precomposition along an identity base arrow acts as the identity on 2-cells.
rule @hom_precomp_along_fapp1_fapp0
      $A
      $B
      $F
      $Z
      $X
      $X
      (@id $A $X)
      $g
      $k
      $alpha
  ↪ $alpha;

// Identity 2-cell under precomposition maps to the identity at the stable
// precomposition object action.
rule @hom_precomp_along_fapp1_fapp0
      $A
      $B
      $F
      $Z
      $W
      $X
      $h
      $g
      $g
      (@id _ $g)
  ↪ @id
      (Hom_cat $B (@fapp0 $A $B $F $W) $Z)
      (@hom_precomp_along_fapp0 $A $B $F $Z $W $X $h $g);

// Proof-time duality between covariant postcomposition and contravariant
// precomposition. Runtime preserves the two variance owners. Only the three
// currently consumed projection rungs are bridged; unification is not assumed
// to propagate transitively to the higher-cell ladders.
unif_rule @hom_postcomp_tele_func
      $B $A $F
      $Z $X $W
  ≡ @hom_precomp_along_tele_func
      $A0 $B0 $F0
      $Z $W $X
  ↪ [
      (Op_cat $B) ≡ $B0;
      (Op_cat $A) ≡ $A0;
      $F ≡ (@Op_func $A0 $B0 $F0)
    ];

// Proof-time opposite comparison of the capped post/precomposition functors.
unif_rule @hom_postcomp_func
      $B $A $F
      $Z $X $W $h
  ≡ @hom_precomp_along_func
      $A0 $B0 $F0
      $Z $W $X $h
  ↪ [
      (Op_cat $B) ≡ $B0;
      (Op_cat $A) ≡ $A0;
      $F ≡ (@Op_func $A0 $B0 $F0)
    ];

// Proof-time opposite comparison of the post/precomposition point actions.
unif_rule @hom_postcomp_fapp0
      $B $A $F
      $Z $X $W $h $g
  ≡ @hom_precomp_along_fapp0
      $A0 $B0 $F0
      $Z $W $X $h $g
  ↪ [
      (Op_cat $B) ≡ $B0;
      (Op_cat $A) ≡ $A0;
      $F ≡ (@Op_func $A0 $B0 $F0)
    ];

// 4d. Internalized source/target endpoints and variance comparison

// Internalized hom classifier.
//
// Surface/formula:
//   hom_int(F) : A^op ⊢ (B ⊢ Cat)
//   hom_int(F)[W][y] = Hom_A(W,F[y]).
injective symbol hom_int [A B : Cat] (F : τ (Functor B A))
  : τ (Functor (Op_cat A) (Catd_cat B));

// Object projection: `hom_int(F)[W] = hom_(F,W)`.
rule @fapp0 _ _ (@hom_int $A $B $F) $W
  ↪ @hom_ $A $B $F $W;

// Generic stable owner for the represented-object action of `hom_int`.
//
// Surface/formula:
//   hom_int_precomp(F,p) : hom_int(F)[Y] ⊢ hom_int(F)[X]
//   hom_int_precomp(F,p)[b] = precompose by p in A.
symbol hom_int_precomp_tele_func [A B : Cat]
  (F : τ (Functor B A))
  [Y X : τ (Obj A)]
  : τ (Functor
      (Hom_cat (Op_cat A) Y X)
      (Hom_cat
        (@Catd_cat B)
        (@hom_ A B F Y)
        (@hom_ A B F X)));

// Capped represented-object action of `hom_int` at p.
symbol hom_int_precomp_func [A B : Cat]
  (F : τ (Functor B A))
  [Y X : τ (Obj A)]
  (p : τ (Hom (Op_cat A) Y X))
  : τ (Hom (@Catd_cat B) (@hom_ A B F Y) (@hom_ A B F X));

// Full represented-object hom action of `hom_int`.
rule @fapp1_func _ _ (@hom_int $A $B $F) $Y $X
  ↪ @hom_int_precomp_tele_func $A $B $F $Y $X;

// Direct capped represented-object action of `hom_int`.
rule @fapp1_fapp0 _ _ (@hom_int $A $B $F) $Y $X $p
  ↪ @hom_int_precomp_func $A $B $F $Y $X $p;

// Applying the telescope at p yields the capped represented-object action.
rule @fapp0 _ _ (@hom_int_precomp_tele_func $A $B $F $Y $X) $p
  ↪ @hom_int_precomp_func $A $B $F $Y $X $p;

// Target-internalized mirror of hom_int.
//
// Surface/formula:
//   hom_con_int(F)[W][b] = Hom_A(F[b],W).
injective symbol hom_con_int [A B : Cat] (F : τ (Functor B A))
  : τ (Functor A (Catd_cat (Op_cat B)));

// Object projection: `hom_con_int(F)[W] = hom_con(W,F)`.
rule @fapp0 _ _ (@hom_con_int $A $B $F) $W
  ↪ @hom_con $A $W $B $F;

// Full represented-target action of `hom_con_int`.
symbol hom_con_int_postcomp_tele_func [A B : Cat]
  (F : τ (Functor B A))
  [W X : τ (Obj A)]
  : τ (Functor
      (Hom_cat A W X)
      (Hom_cat
        (@Catd_cat (Op_cat B))
        (@hom_con A W B F)
        (@hom_con A X B F)));

// Capped represented-target action of `hom_con_int` at f.
symbol hom_con_int_postcomp_func [A B : Cat]
  (F : τ (Functor B A))
  [W X : τ (Obj A)]
  (f : τ (Hom A W X))
  : τ (Hom
      (@Catd_cat (Op_cat B))
      (@hom_con A W B F)
      (@hom_con A X B F));

// Full hom action of `hom_con_int` in its represented target.
rule @fapp1_func _ _ (@hom_con_int $A $B $F) $W $X
  ↪ @hom_con_int_postcomp_tele_func $A $B $F $W $X;

// Direct capped represented-target action of `hom_con_int`.
rule @fapp1_fapp0 _ _ (@hom_con_int $A $B $F) $W $X $f
  ↪ @hom_con_int_postcomp_func $A $B $F $W $X $f;

// Applying the target-action telescope at f yields the capped action.
rule fapp0 (@hom_con_int_postcomp_tele_func $A $B $F $W $X) $f
  ↪ @hom_con_int_postcomp_func $A $B $F $W $X $f;

/*
  Ordinary internal-hom computations.

  Surface/formula:
    hom_(F,W)[y] = Hom_A(W,F[y])
    hom_con(W,F)[y] = Hom_A(F[y],W)
    hom_int(F)[W][y] = Hom_A(W,F[y])
    hom_precomp_along_func(id_A,Z,p)[q] = q ∘ p.
*/

// -------------------------------------------------------------------------------------------------
// 5. Ordinary binary products of categories
// -------------------------------------------------------------------------------------------------

// 5a. Product categories, projections, and paired functors
/*
  Minimal ordinary product package.

  Surface/formula:
    Product_cat(A,B)              = A × B
    Obj(A × B)                    = Σ x : Obj(A), Obj(B)
    Hom_{A × B}((x,u),(y,v))      = Hom_A(x,y) × Hom_B(u,v)
    id_{(x,u)}                    = (id_x,id_u)
    (g1,g2) ∘ (f1,f2)             = (g1 ∘ f1, g2 ∘ f2)
    X ⊢ (A × B)                  = (X ⊢ A) × (X ⊢ B)

  Product-valued functors are represented by the product normal form above.
  Projection computation is attached to stable projection functor heads and to
  `sigma_Fst`/`sigma_Snd` consumer rules. Avoid a broad eta rule expanding
  arbitrary `fapp0 H i`; use the narrower paired-head rules below.
*/
// Binary product category: Product_cat(A,B) = A × B.
injective symbol Product_cat : Π (A B : Cat), Cat;

// Product-valued functors normalize componentwise: X ⊢ A × B = (X ⊢ A) × (X ⊢ B).
rule Functor_cat $X (Product_cat $A $B)
  ↪ Product_cat (Functor_cat $X $A) (Functor_cat $X $B);

// Product objects use the stable groupoid-level Product classifier.
rule Obj (Product_cat $A $B)
  ↪ Product_grpd (Obj $A) (Obj $B);

// Direct-univalence join for the stable Product-path normal form.
unif_rule
  @OmegaEquiv (Product_cat $A $B) $x $y
  ≡ @ProductPathView (Obj $A) (Obj $B) $x $y
  ↪ [ tt ≡ tt ];

// Product compatibility names route through the general stable carrier cast.
symbol product_path_as_omega
  [A B : Cat]
  [x y : τ (Obj (Product_cat A B))]
  (p : τ (@= (Obj (Product_cat A B)) x y))
  : τ (@OmegaEquiv (Product_cat A B) x y)
≔ @object_path_cast_to_omega (Product_cat A B) x y p;

symbol product_omega_as_path
  [A B : Cat]
  [x y : τ (Obj (Product_cat A B))]
  (e : τ (@OmegaEquiv (Product_cat A B) x y))
  : τ (@= (Obj (Product_cat A B)) x y)
≔ @omega_cast_to_object_path (Product_cat A B) x y e;

// Opposite distributes over binary products: (A × B)^op = A^op × B^op.
rule Op_cat (Product_cat $A $B)
  ↪ Product_cat (Op_cat $A) (Op_cat $B);

// First object projection: Product_projL(x,u) = x.
symbol Product_projL [A B : Cat] (xy : τ (Obj (Product_cat A B)))
  : τ (Obj A)
≔ sigma_Fst xy;

// Second object projection: Product_projR(x,u) = u.
symbol Product_projR [A B : Cat] (xy : τ (Obj (Product_cat A B)))
  : τ (Obj B)
≔ sigma_Snd xy;

// Object pairing: Product_pair(x,u) = (x,u) : Obj(A × B).
injective symbol Product_pair [A B : Cat]
  (x : τ (Obj A)) (y : τ (Obj B))
  : τ (Obj (Product_cat A B))
≔ @Struct_sigma (Obj A) (λ _ : τ (Obj A), Obj B) x y;

// First projection functor: π₁ : A × B ⊢ A.
injective symbol Product_projL_func [A B : Cat]
  : τ (Functor (Product_cat A B) A);

// Second projection functor: π₂ : A × B ⊢ B.
injective symbol Product_projR_func [A B : Cat]
  : τ (Functor (Product_cat A B) B);

// The identity functor of a product is the paired projection functor.
rule sigma_Fst (@id Cat_cat (Product_cat $A $B)) ↪ @Product_projL_func $A $B;

// Second component of the product identity functor is the right projection.
rule sigma_Snd (@id Cat_cat (Product_cat $A $B)) ↪ @Product_projR_func $A $B;

// Projection functors act by object projections.
rule @fapp0 _ _ (@Product_projL_func $A $B) $p
  ↪ sigma_Fst $p;

// Right product projection acts on objects by `sigma_Snd`.
rule @fapp0 _ _ (@Product_projR_func $A $B) $p
  ↪ sigma_Snd $p;

// Projection of a paired functor application.
rule sigma_Fst (@fapp0 $X (Product_cat $A $B) $H $i)
  ↪ @fapp0 $X $A (sigma_Fst $H) $i;

// Right projection of a product-valued functor application is pointwise.
rule sigma_Snd (@fapp0 $X (Product_cat $A $B) $H $i)
  ↪ @fapp0 $X $B (sigma_Snd $H) $i;

// Application and hom-action for an explicitly paired functor.
// Explicit pair application: (F,G)[i] = (F[i],G[i]).
rule @fapp0 $X (Product_cat $A $B) (Struct_sigma $F $G) $i
  ↪ Struct_sigma
      (@fapp0 $X $A $F $i)
      (@fapp0 $X $B $G $i);

// Product homs compute componentwise.
rule Hom_cat (Product_cat $A $B) $p $q
  ↪ Product_cat
      (Hom_cat $A (sigma_Fst $p) (sigma_Fst $q))
      (Hom_cat $B (sigma_Snd $p) (sigma_Snd $q));

// Hom-action of a paired functor is the pair of hom-actions.
rule @fapp1_func $X (Product_cat $A $B) (Struct_sigma $F $G) $i $j
  ↪ Struct_sigma
      (@fapp1_func $X $A $F $i $j)
      (@fapp1_func $X $B $G $i $j);

// Capped hom-action of a paired functor is componentwise.
rule @fapp1_fapp0 $X (Product_cat $A $B) (Struct_sigma $F $G) $i $j $p
  ↪ Struct_sigma
      (@fapp1_fapp0 $X $A $F $i $j $p)
      (@fapp1_fapp0 $X $B $G $i $j $p);

// Hom-action of product projections is projection on product homs.
rule @fapp1_func _ _ (@Product_projL_func $A $B) $p $q
  ↪ @Product_projL_func
      (Hom_cat $A (sigma_Fst $p) (sigma_Fst $q))
      (Hom_cat $B (sigma_Snd $p) (sigma_Snd $q));

// Full hom action of the right projection is the right hom projection.
rule @fapp1_func _ _ (@Product_projR_func $A $B) $p $q
  ↪ @Product_projR_func
      (Hom_cat $A (sigma_Fst $p) (sigma_Fst $q))
      (Hom_cat $B (sigma_Snd $p) (sigma_Snd $q));

// Capped projection hom-actions select the corresponding component arrow.
rule @fapp1_fapp0 _ _ (@Product_projL_func $A $B) $p $q $h
  ↪ sigma_Fst $h;

// Capped hom action of the right projection selects the right component.
rule @fapp1_fapp0 _ _ (@Product_projR_func $A $B) $p $q $h
  ↪ sigma_Snd $h;

// 5b. Product symmetry, identities, and composition
/*
  Product symmetry.

  Product-valued functors are encoded by their two projection components, so
  the stable swap head exposes that projection ladder as well as direct object
  and arrow computations.
*/
injective symbol Product_swap_func [A B : Cat]
  : τ (Functor (Product_cat A B) (Product_cat B A));

// Left projection of product swap is the original right projection.
rule sigma_Fst (@Product_swap_func $A $B)
  ↪ @Product_projR_func $A $B;

// Right projection of product swap is the original left projection.
rule sigma_Snd (@Product_swap_func $A $B)
  ↪ @Product_projL_func $A $B;

// Product swap exchanges object components.
rule @fapp0
      _
      _
      (@Product_swap_func $A $B)
      (Struct_sigma $x $y)
  ↪ @Struct_sigma
      (Obj $B)
      (λ _ : τ (Obj $B), Obj $A)
      $y $x;

// Full hom action of product swap exchanges hom components.
rule @fapp1_func
      _
      _
      (@Product_swap_func $A $B)
      $p $q
  ↪ @Product_swap_func
      (Hom_cat $A (sigma_Fst $p) (sigma_Fst $q))
      (Hom_cat $B (sigma_Snd $p) (sigma_Snd $q));

// Capped hom action of product swap exchanges arrow components.
rule @fapp1_fapp0
      _
      _
      (@Product_swap_func $A $B)
      $p $q
      $h
  ↪ @Struct_sigma
      (Obj (Hom_cat $B (sigma_Snd $p) (sigma_Snd $q)))
      (λ _ : τ (Obj (Hom_cat $B (sigma_Snd $p) (sigma_Snd $q))),
        Obj (Hom_cat $A (sigma_Fst $p) (sigma_Fst $q)))
      (sigma_Snd $h)
      (sigma_Fst $h);

// lhs-audit: keep 2,3,4 -- product source/middle/target categories guard the symmetry involution rule.
rule @comp_fapp0
      Cat_cat
      (Product_cat $A $B)
      (Product_cat $B $A)
      (Product_cat $A $B)
      (@Product_swap_func $B $A)
      (@Product_swap_func $A $B)
  ↪ @id_func (Product_cat $A $B);

// Pulling an arbitrary functor back along product symmetry twice is neutral
// in the canonical left-associated composition normal form.
// lhs-audit: keep 2,3 -- product source/middle categories guard the symmetry-involution pullback rule.
rule @comp_fapp0
      Cat_cat
      (Product_cat $A $B)
      (Product_cat $B $A)
      $C
      (@comp_fapp0
        Cat_cat
        (Product_cat $B $A)
        (Product_cat $A $B)
        $C
        $H
        (@Product_swap_func $B $A))
      (@Product_swap_func $A $B)
  ↪ $H;

// Opposite of product swap is swap between the opposite factors.
rule @Op_func
      (Product_cat $A $B)
      (Product_cat $B $A)
      (@Product_swap_func $A $B)
  ↪ @Product_swap_func (Op_cat $A) (Op_cat $B);

// Product identities are pairs when the product object is explicit.
rule @id (Product_cat $A $B) (Struct_sigma $x $u)
  ↪ Struct_sigma (@id $A $x) (@id $B $u);

// For an opaque product object, expose identity componentwise through
// projections without expanding the whole arrow. This lets component
// consumers compute while preserving the generic identity normal form.
rule sigma_Fst (@id (Product_cat $A _) $xu)
  ↪ @id $A (sigma_Fst $xu);

// Right component of an opaque product identity is the corresponding identity.
rule sigma_Snd (@id (Product_cat _ $B) $xu)
  ↪ @id $B (sigma_Snd $xu);

// Proof-time eta for an opaque product identity. Keep the runtime identity
// head so the global functor-identity rule remains the computational owner.
unif_rule
  @id (Product_cat $A $B) $xy
  ≡ @Struct_sigma
      (Obj (Hom_cat $A (sigma_Fst $xy) (sigma_Fst $xy)))
      (λ _ : τ (Obj (Hom_cat $A (sigma_Fst $xy) (sigma_Fst $xy))),
        Obj (Hom_cat $B (sigma_Snd $xy) (sigma_Snd $xy)))
      (@id $A (sigma_Fst $xy))
      (@id $B (sigma_Snd $xy))
  ↪ [ tt ≡ tt ];

// Product composition is componentwise: (g1,g2) ∘ (f1,f2).
rule @comp_fapp0
      (Product_cat $A $B)
      (Struct_sigma $x $u)
      (Struct_sigma $y $v)
      (Struct_sigma $z $w)
      (Struct_sigma $g1 $g2)
      (Struct_sigma $f1 $f2)
  ↪ Struct_sigma
      (@comp_fapp0 $A $x $y $z $g1 $f1)
      (@comp_fapp0 $B $u $v $w $g2 $f2);

// 5c. Product and uncurried composition action
/*
  Product/uncurried composition as a functor.

  Surface/formula:
    comp_prod_func[W,X,Z] : Hom(W,X) × Hom(X,Z) ⊢ Hom(W,Z)
    comp_prod_func[(f,g)] = g ∘ f.

  This is the product-form counterpart of the object-level `comp_fapp0`.
  It supplies a neutral capped arrow-action owner for higher cells in the two
  input hom-categories; Cat-specialized horizontal-action structure is a later
  projection-ladder migration.
*/
symbol comp_prod_func [A : Cat]
  [W X Z : τ (Obj A)]
  : τ (Functor
      (Product_cat (Hom_cat A W X) (Hom_cat A X Z))
      (Hom_cat A W Z));

// Object beta: composing a pair `(g,f)` yields `f o g`.
rule fapp0 (@comp_prod_func $A $W $X $Z) $pg
  ↪ @comp_fapp0 $A $W $X $Z (sigma_Snd $pg) (sigma_Fst $pg);

// Full hom action of the product/uncurried composition functor.
symbol comp_prod_fapp1_func [A : Cat]
  [W X Z : τ (Obj A)]
  [pg pg' : τ (Obj
    (Product_cat (Hom_cat A W X) (Hom_cat A X Z)))]
  : τ (Functor
      (Hom_cat
        (Product_cat (Hom_cat A W X) (Hom_cat A X Z))
        pg
        pg')
      (Hom_cat
        (Hom_cat A W Z)
        (@comp_fapp0 A W X Z (sigma_Snd pg) (sigma_Fst pg))
        (@comp_fapp0 A W X Z (sigma_Snd pg') (sigma_Fst pg'))));

// Capped hom action of product/uncurried composition.
symbol comp_prod_fapp1_fapp0 [A : Cat]
  [W X Z : τ (Obj A)]
  [pg pg' : τ (Obj
    (Product_cat (Hom_cat A W X) (Hom_cat A X Z)))]
  (alpha : τ (Hom
    (Product_cat (Hom_cat A W X) (Hom_cat A X Z))
    pg
    pg'))
  : τ (Hom
      (Hom_cat A W Z)
      (@comp_fapp0 A W X Z (sigma_Snd pg) (sigma_Fst pg))
      (@comp_fapp0 A W X Z (sigma_Snd pg') (sigma_Fst pg')));

// Projection from generic full action to the stable composition-action head.
rule @fapp1_func _ _ (@comp_prod_func $A $W $X $Z) $pg $pg'
  ↪ @comp_prod_fapp1_func $A $W $X $Z $pg $pg';

// Applying the full action yields the capped componentwise composition action.
rule fapp0 (@comp_prod_fapp1_func $A $W $X $Z $pg $pg') $alpha
  ↪ @comp_prod_fapp1_fapp0 $A $W $X $Z $pg $pg' $alpha;

// Direct capped action joins the full-action projection.
rule @fapp1_fapp0 _ _ (@comp_prod_func $A $W $X $Z) $pg $pg' $alpha
  ↪ @comp_prod_fapp1_fapp0 $A $W $X $Z $pg $pg' $alpha;

// Transparent Cat specialization: compose a pair of ordinary functors.
symbol Functor_comp_pair_func [A B C : Cat]
  : τ (Functor
      (Product_cat (Functor_cat A B) (Functor_cat B C))
      (Functor_cat A C))
≔ @comp_prod_func Cat_cat A B C;

// 5d. Rigid two-endpoint Hom action
/*
  General two-endpoint action of the ordinary hom-category.

  Surface/formula:
    Hom_tele_func[x,x',y,y'][(g,f)] = Hom_func(g,f)
    Hom_func(g,f)[h] = f o h o g

  This is the ambient-category owner formerly hidden in the
  profunctor-specific `Unit_prof_fapp1_func`: it packages the action of
  Hom_A(-,-) on both endpoints without mentioning profunctors.
*/
symbol Hom_tele_func [A : Cat]
  [x x' y y' : τ (Obj A)]
  : τ (Functor
      (Product_cat (Hom_cat A x' x) (Hom_cat A y y'))
      (Functor_cat (Hom_cat A x y) (Hom_cat A x' y')));

// Capped two-endpoint hom action at the pair `(g,f)`.
symbol Hom_func [A : Cat]
  [x x' y y' : τ (Obj A)]
  (g : τ (Hom A x' x))
  (f : τ (Hom A y y'))
  : τ (Functor
      (Hom_cat A x y)
      (Hom_cat A x' y'));

// Point action `Hom_A(g,f)[h] = f o h o g`.
symbol Hom_fapp0 [A : Cat]
  [x x' y y' : τ (Obj A)]
  (g : τ (Hom A x' x))
  (f : τ (Hom A y y'))
  (h : τ (Hom A x y))
  : τ (Hom A x' y');

// Applying the two-endpoint telescope to `(g,f)` yields `Hom_func(g,f)`.
rule fapp0 (@Hom_tele_func $A $x $x' $y $y') (Struct_sigma $g $f)
  ↪ @Hom_func $A $x $x' $y $y' $g $f;

// Applying `Hom_func(g,f)` to h yields the rigid point head.
rule fapp0 (@Hom_func $A $x $x' $y $y' $g $f) $h
  ↪ @Hom_fapp0 $A $x $x' $y $y' $g $f $h;

// Cat-specialized consumed-point projection of the rigid two-endpoint Hom
// action. The standalone Hom_fapp0 head remains Unit_prof's point normal form.
rule @fapp0 _ _
      (@Hom_fapp0 Cat_cat $X $X' $Y $Y' $g $f $h) $x'
  ↪ @fapp0
      $Y $Y' $f
      (@fapp0
        $X $Y $h
        (@fapp0 $X' $X $g $x'));

// The primitive Unit_prof projection keeps the Hom action rigid at runtime.
// Its two factorizations through one-slot pre/postcomposition remain available
// during typed elaboration without choosing either factorization as the
// computational normal form.
// Proof-time comparison with the pre-then-post factorization.
unif_rule @Hom_fapp0 $A $x $x' $y $y' $g $f $h
  ≡ @hom_postcomp_fapp0
      $A $A (@id Cat_cat $A)
      $x' $y $y' $f
      (@hom_precomp_along_fapp0
        $A $A (@id Cat_cat $A)
        $y $x' $x $g $h)
  ↪ [ tt ≡ tt ];

// Proof-time comparison with the post-then-pre factorization.
unif_rule @Hom_fapp0 $A $x $x' $y $y' $g $f $h
  ≡ @hom_precomp_along_fapp0
      $A $A (@id Cat_cat $A)
      $y' $x' $x $g
      (@hom_postcomp_fapp0
        $A $A (@id Cat_cat $A)
        $x $y $y' $f $h)
  ↪ [ tt ≡ tt ];

// One active endpoint and an identity middle arrow are proof-time
// degenerations of the rigid Hom owner, not runtime unfoldings of it.
unif_rule @Hom_func $A $x $x $y $y' (@id $A $x) $f
  ≡ @hom_postcomp_func $A $A (@id Cat_cat $A) $x $y $y' $f
  ↪ [ tt ≡ tt ];

// Proof-time target-identity degeneration to the precomposition functor.
unif_rule @Hom_func $A $x $x' $y $y $g (@id $A $y)
  ≡ @hom_precomp_along_func $A $A (@id Cat_cat $A) $y $x' $x $g
  ↪ [ tt ≡ tt ];

// Proof-time source-identity point degeneration to postcomposition.
unif_rule @Hom_fapp0 $A $x $x $y $y' (@id $A $x) $f $h
  ≡ @hom_postcomp_fapp0 $A $A (@id Cat_cat $A) $x $y $y' $f $h
  ↪ [ tt ≡ tt ];

// Proof-time target-identity point degeneration to precomposition.
unif_rule @Hom_fapp0 $A $x $x' $y $y $g (@id $A $y) $h
  ≡ @hom_precomp_along_fapp0 $A $A (@id Cat_cat $A) $y $x' $x $g $h
  ↪ [ tt ≡ tt ];

// Proof-time middle-identity degeneration to the corresponding postcomposition cut.
unif_rule @Hom_fapp0 $A $x $x' $x $y' $g $f (@id $A $x)
  ≡ @hom_postcomp_fapp0 $A $A (@id Cat_cat $A) $x' $x $y' $f $g
  ↪ [ tt ≡ tt ];

// Narrow proof-time raw-composition readings for identity endpoint actions.
// Runtime preserves the rigid Hom head for a single inactive endpoint; these
// comparisons remain useful when elaboration expects `comp_fapp0`.
unif_rule @Hom_fapp0 $A $x $x $y $y' (@id $A $x) $f $h
  ≡ @comp_fapp0 $A $x $y $y' $f $h
  ↪ [ tt ≡ tt ];

// Proof-time raw-composition reading for an inactive target endpoint.
unif_rule @Hom_fapp0 $A $x $x' $y $y $g (@id $A $y) $h
  ≡ @comp_fapp0 $A $x' $x $y $h $g
  ↪ [ tt ≡ tt ];

// Functoriality after projection to rigid Hom heads. The generic action is
// owned by Hom_tele_func, but its literal fapp1 pattern is no longer visible
// after capping to Hom_func/Hom_fapp0, so these are projection-order joins.
rule @Hom_func $A $x $x $y $y (@id $A $x) (@id $A $y)
  ↪ @id_func (Hom_cat $A $x $y);

// Point action with both identity endpoints returns h.
rule @Hom_fapp0 $A $x $x $y $y (@id $A $x) (@id $A $y) $h
  ↪ $h;


// Projection-order join: composition of two `Hom_func` values accumulates endpoints.
rule @comp_fapp0
      Cat_cat
      _ _ _
      (@Hom_func $A $x1 $x2 $y1 $y2 $g12 $f12)
      (@Hom_func $A $x0 $x1 $y0 $y1 $g01 $f01)
  ↪ @Hom_func
      $A $x0 $x2 $y0 $y2
      (@comp_fapp0 $A $x2 $x1 $x0 $g01 $g12)
      (@comp_fapp0 $A $y0 $y1 $y2 $f12 $f01);

// Point-level accumulation of nested rigid two-endpoint actions.
rule @Hom_fapp0
      $A $x1 $x2 $y1 $y2 $g12 $f12
      (@Hom_fapp0 $A $x0 $x1 $y0 $y1 $g01 $f01 $h)
  ↪ @Hom_fapp0
      $A $x0 $x2 $y0 $y2
      (@comp_fapp0 $A $x2 $x1 $x0 $g01 $g12)
      (@comp_fapp0 $A $y0 $y1 $y2 $f12 $f01)
      $h;

// 5e. Product closure for ordinary isomorphism evidence
/*
  Ordinary isomorphism evidence is closed under explicit product-category
  pairs. This is the 1-categorical staging analogue of `omega_equiv_product`.
  The inverse-proof projections are intentionally left opaque until a
  consumer needs them; the first staging slice exposes the forward/inverse
  arrows and the path decoder. Product evidence retains its componentwise
  constructor even when both components are reflexive; it does not collapse
  to the unrelated generic reflexive evidence head.
*/
injective symbol iso_evidence_product
  [A B : Cat]
  [x0 x1 : τ (Obj A)]
  [y0 y1 : τ (Obj B)]
  (iA : τ (IsoEvidence A x0 x1))
  (iB : τ (IsoEvidence B y0 y1))
  : τ (IsoEvidence
      (Product_cat A B)
      (Struct_sigma x0 y0)
      (Struct_sigma x1 y1));

// Forward arrow of product isomorphism evidence is componentwise.
rule sigma_Fst
      (@iso_evidence_product $A $B $x0 $x1 $y0 $y1 $iA $iB)
  ↪ Struct_sigma
      (@iso_evidence_to $A $x0 $x1 $iA)
      (@iso_evidence_to $B $y0 $y1 $iB);

// Inverse arrow of product isomorphism evidence is componentwise.
rule sigma_Fst
      (sigma_Snd
        (@iso_evidence_product $A $B $x0 $x1 $y0 $y1 $iA $iB))
  ↪ Struct_sigma
      (@iso_evidence_from $A $x0 $x1 $iA)
      (@iso_evidence_from $B $y0 $y1 $iB);

// Encoding a product object path yields componentwise isomorphism evidence.
rule @idtoiso_cat
      (Product_cat $A $B)
      (Struct_sigma $x0 $y0)
      (Struct_sigma $x1 $y1)
      (Struct_sigma $pA $pB)
  ↪ @iso_evidence_product
      $A
      $B
      $x0
      $x1
      $y0
      $y1
      (@idtoiso_cat $A $x0 $x1 $pA)
      (@idtoiso_cat
        $B
        $y0
        $y1
        (@const_pathover_path
          (Obj $A)
          (Obj $B)
          $x0
          $x1
          $y0
          $y1
          $pA
          $pB));

// 5f. Product-pair telescope declaration

// Pairing telescope for products. Its computation rules are installed later,
// after the constant-section machinery they project to is available.
//
// Surface/formula:
//   Product_pair_tele_func(A,B)[x][y] = (x,y).
symbol Product_pair_tele_func [A B : Cat]
  : τ (Functor A (Functor_cat B (Product_cat A B)));

// -------------------------------------------------------------------------------------------------
// 6. Ordinary transformations and functor composition actions
// -------------------------------------------------------------------------------------------------

// 6a. Transformation classifier, components, and generic projection calculus

/*
  Ordinary transfor/natural-transformation category.

  Surface/formula:
    Transf_cat(F,G) = F => G
    Transf(F,G)     = Obj(F => G)

  For Cat-valued functors this is proof-time-comparable with the stable
  displayed-family category:
    Transf_cat(K,Cat,E,D) = Functord_cat(E,D).
*/
injective symbol Transf_cat : Π [A B : Cat], Π (F G : τ (Functor A B)), Cat;

// Object/type classifier of the ordinary transformation category.
injective symbol Transf [A B : Cat] (F G : τ (Functor A B)) : Grpd
≔ Obj (@Transf_cat A B F G);

// Controlled Obj-inversion for transformation categories. This inherited
// helper lets projection rules keep source/target functors
// implicit, e.g. `@tapp0_fapp0 ... _ _ ...`, without forcing reducible
// compound family expressions into rewrite-rule LHSs.
unif_rule Obj (@Transf_cat $A $B $F $G) ≡ Obj (@Transf_cat $A' $B' $F' $G')
  ↪ [ $A ≡ $A'; $B ≡ $B'; $F ≡ $F'; $G ≡ $G' ];

// Hom in an ordinary functor category is the transfor category.
//
// Surface/formula:
//   Hom_{A ⊢ B}(F,G) = F => G.
rule Hom_cat (Functor_cat _ _) $F $G ↪ Transf_cat $F $G;

// Proof-time comparison only: ordinary Cat-valued transfors and displayed
// functor families are two stable presentations of the same first hom.
//
// Surface/formula:
//   E => D over K = k :^n K ; E[k] ⊢ D[k].
unif_rule
  @Transf_cat $K Cat_cat $E $D
  ≡ @Functord_cat $K' $E' $D'
  ↪ [ $K ≡ $K'; $E ≡ $E'; $D ≡ $D' ];

// Runtime object projection from the displayed first-hom facade.
rule Obj (@Functord_cat $K $E $D)
  ↪ Obj (@Transf_cat $K Cat_cat $E $D);

// Runtime object projection from the displayed second-hom facade to the
// corresponding ordinary iterated hom category.
rule Obj (@Transfd_cat $K $E $D $FF $GG)
  ↪ Obj
      (Hom_cat
        (@Transf_cat $K Cat_cat $E $D)
        $FF
        $GG);

// Direct proof-time second-hom comparison. Do not rely on transitivity of the
// lower Functor/Catd and Transf/Functord comparisons.
unif_rule
  Hom_cat (@Transf_cat $K Cat_cat $E $D) $FF $GG
  ≡ @Transfd_cat $K' $E' $D' $FF' $GG'
  ↪ [
      $K ≡ $K';
      $E ≡ $E';
      $D ≡ $D';
      $FF ≡ $FF';
      $GG ≡ $GG'
    ];

// Product-valued transfors project componentwise.
//
// Surface/formula:
//   Transf(F,G) in A × B = Transf(F_1,G_1) × Transf(F_2,G_2).
rule @Transf_cat $X (Product_cat $A $B) $F $G
  ↪ Product_cat
      (@Transf_cat $X $A (sigma_Fst $F) (sigma_Fst $G))
      (@Transf_cat $X $B (sigma_Snd $F) (sigma_Snd $G));

// Readable second Path action: a function equality induces a path-valued
// transfor through the next ordinary action of Path_cat_func.
symbol path_map_transf
  [A B : Grpd]
  [f g : τ (@Function_grpd A B)]
  (h : τ (@= (@Function_grpd A B) f g))
  : τ (Transf
      (@path_map_func A B f)
      (@path_map_func A B g))
≔ @fapp1_fapp0
    (Path_cat (@Function_grpd A B))
    (Functor_cat (Path_cat A) (Path_cat B))
    (@fapp1_func
      Grpd_cat Cat_cat Path_cat_func A B)
    f g h;

/*
  Cat-valued transfors and displayed functors are proof-time-comparable
  stable presentations.

  Surface/formula:
    Transf(K,Cat,E,D) = Functord(E,D).
*/

/*
  Mathematical notation:
    ϵ : F => G
    tapp0_func(F,G,Y)         : Transf(F,G) ⊢ Hom_B(F[Y],G[Y])
    ϵ[Y]                      = tapp0_fapp0 Y ϵ
    (η ∘ ϵ)[Y]                = η[Y] ∘ ϵ[Y]
*/
symbol tapp0_func : Π [A B : Cat], Π [F G : τ (Functor A B)],
  Π (Y : τ (Obj A)),
  τ (Functor (Transf_cat F G) (Hom_cat B (fapp0 F Y) (fapp0 G Y)));

// Point component `epsilon[Y] : F[Y] -> G[Y]`.
symbol tapp0_fapp0 : Π [A B : Cat], Π [F G : τ (Functor A B)],
  Π (Y : τ (Obj A)),
  Π (ϵ : τ (Obj (Transf_cat F G))),
  τ (Hom B (fapp0 F Y) (fapp0 G Y));

/*
  Design note: `tapp0_fapp0` is a primitive projection head, not a
  definitional abbreviation. The head must remain
  visible so later rules can attach component computations directly to it.
*/
// Evaluation of the component projection functor.
//
// Surface/formula:
//   tapp0_func(Y)[epsilon] = epsilon[Y].
rule fapp0 (@tapp0_func $A $B $F $G $Y) $ϵ
  ↪ @tapp0_fapp0 $A $B $F $G $Y $ϵ;

// Component of a postcomposition-telescope action. Mathematically,
//   ((hom_A(W,F[-]))[alpha])[u] = u^*(F[alpha]).
// This deliberately computes the component through the stable precomposition
// action. The choice is backtrackable if a later consumer needs this as a
// proof-time bridge or a more direct component owner instead.
rule @tapp0_fapp0
      _ _
      _ _
      $u
      (@hom_postcomp_tele_fapp1_fapp0 $A $B $F $W $X $Y $f $g $alpha)
  ↪ @hom_precomp_along_fapp1_fapp0
      $A
      $A
      (@id Cat_cat $A)
      (@fapp0 $B $A $F $Y)
      $W
      (@fapp0 $B $A $F $X)
      $u
      (@fapp1_fapp0 $B $A $F $X $Y $f)
      (@fapp1_fapp0 $B $A $F $X $Y $g)
      (@fapp1_fapp0
        (Hom_cat $B $X $Y)
        (Hom_cat $A (@fapp0 $B $A $F $X) (@fapp0 $B $A $F $Y))
        (@fapp1_func $B $A $F $X $Y)
        $f
        $g
        $alpha);

// Reflexive theorem exposing the selected component formula for the telescope action.
symbol hom_postcomp_tele_tapp0_component_eq
  [A B : Cat]
  (F : τ (Functor B A))
  (W : τ (Obj A))
  [X Y : τ (Obj B)]
  [f g : τ (Hom B X Y)]
  (alpha : τ (Hom (Hom_cat B X Y) f g))
  (u : τ (Hom A W (@fapp0 B A F X)))
  : τ (
      @tapp0_fapp0
        (Hom_cat A W (@fapp0 B A F X))
        (Hom_cat A W (@fapp0 B A F Y))
        (@hom_postcomp_func A B F W X Y f)
        (@hom_postcomp_func A B F W X Y g)
        u
        (@hom_postcomp_tele_fapp1_fapp0 A B F W X Y f g alpha)
      =
      @hom_precomp_along_fapp1_fapp0
        A
        A
        (@id_func A)
        (@fapp0 B A F Y)
        W
        (@fapp0 B A F X)
        u
        (@fapp1_fapp0 B A F X Y f)
        (@fapp1_fapp0 B A F X Y g)
        (@fapp1_fapp0
          (Hom_cat B X Y)
          (Hom_cat A (@fapp0 B A F X) (@fapp0 B A F Y))
          (@fapp1_func B A F X Y)
          f
          g
          alpha))
≔ eq_refl
    (@hom_precomp_along_fapp1_fapp0
      A
      A
      (@id_func A)
      (@fapp0 B A F Y)
      W
      (@fapp0 B A F X)
      u
      (@fapp1_fapp0 B A F X Y f)
      (@fapp1_fapp0 B A F X Y g)
      (@fapp1_fapp0
        (Hom_cat B X Y)
        (Hom_cat A (@fapp0 B A F X) (@fapp0 B A F Y))
        (@fapp1_func B A F X Y)
        f
        g
        alpha));

// Product-valued transfor components project componentwise.
rule sigma_Fst (@tapp0_fapp0 $X (Product_cat $A $B) $F $G $i $eta)
  ↪ @tapp0_fapp0 $X $A (sigma_Fst $F) (sigma_Fst $G) $i (sigma_Fst $eta);

// Right component of a product-valued transfor component is pointwise.
rule sigma_Snd (@tapp0_fapp0 $X (Product_cat $A $B) $F $G $i $eta)
  ↪ @tapp0_fapp0 $X $B (sigma_Snd $F) (sigma_Snd $G) $i (sigma_Snd $eta);

// Hom-action of evaluation-at-an-object is component projection.
rule @fapp1_func _ $B (@fapp0_func $A $B $x) $F $G
  ↪ @tapp0_func $A $B $F $G $x;

// Capped hom action of evaluation is the selected transfor component.
rule @fapp1_fapp0 _ $B (@fapp0_func $A $B $x) $F $G $η
  ↪ @tapp0_fapp0 $A $B $F $G $x $η;

// Identity transfor components are identity arrows.
rule @tapp0_fapp0 $A $B $F $F $Y (@id (Functor_cat $A $B) $F)
  ↪ @id $B (@fapp0 $A $B $F $Y);

// Displayed identity components are identity functors on fibres.
rule @tapp0_fapp0 $K Cat_cat $E $E $Y (@id (@Catd_cat $K) $E)
  ↪ @id Cat_cat (@fapp0 $K Cat_cat $E $Y);

// Vertical composite components compose pointwise.
//
// Surface/formula:
//   (eta ∘ epsilon)[Y] = eta[Y] ∘ epsilon[Y].
rule @tapp0_fapp0 $A $B $F $H $Y (@comp_fapp0 (Functor_cat $A $B) $F $G $H $η $ϵ)
  ↪ comp_fapp0
      (@tapp0_fapp0 $A $B $G $H $Y $η)
      (@tapp0_fapp0 $A $B $F $G $Y $ϵ);

/*
  Phase 9 discrete-category core and homwise adequacy.

  `IsDiscreteCat(C)` stores exactly set-truncated objects and native
  equality-valued groupoidality evidence for `Core_incl_func(C)`. Homwise
  path selection is derived in the one-way native hom-action extension; the
  retired compatibility layer is not part of the discrete-category contract.
*/
// Exact zero-dimensional category contract.
symbol IsDiscreteCat
  (C : Cat)
  : Grpd
≔ @Product_grpd
    (IsSetGrpd (Obj C))
    (@IsGroupoidalCat C);

// Constructor for the selected two-field contract.
symbol discrete_cat_intro
  [C : Cat]
  (obj_set : τ (IsSetGrpd (Obj C)))
  (core_equiv : τ (@IsGroupoidalCat C))
  : τ (IsDiscreteCat C)
≔ @Product_pair_grpd
    (IsSetGrpd (Obj C))
    (@IsGroupoidalCat C)
    obj_set
    core_equiv;

// Set-truncation projection.
symbol is_discrete_cat_obj_set
  [C : Cat]
  (d : τ (IsDiscreteCat C))
  : τ (IsSetGrpd (Obj C))
≔ sigma_Fst d;

// Object paths in a discrete category are proposition-valued.
symbol discrete_cat_path_proof
  [C : Cat]
  (d : τ (IsDiscreteCat C))
  [x y : τ (Obj C)]
  (p q : τ (@= (Obj C) x y))
  : τ (@= (@= (Obj C) x y) p q)
≔ @is_contr_center
    (@= (@= (Obj C) x y) p q)
    ((@is_discrete_cat_obj_set C d) x y p q);

// Native equality-valued core-inclusion evidence projection.
symbol is_discrete_cat_core_equiv
  [C : Cat]
  (d : τ (IsDiscreteCat C))
  : τ (@IsGroupoidalCat C)
≔ sigma_Snd d;

// Hom action of the identity-on-objects core inclusion.
symbol core_incl_hom_func
  [C : Cat]
  [x y : τ (Obj C)]
  : τ (Functor
      (Path_cat (@= (Obj C) x y))
      (Hom_cat C x y))
≔ @fapp1_func
    (Core_cat C)
    C
    (Core_incl_func C)
    x y;


// Readable alias for the native groupoidality projection.
symbol discrete_cat_is_groupoidal
  [C : Cat]
  (d : τ (IsDiscreteCat C))
  : τ (@IsGroupoidalCat C)
≔ @is_discrete_cat_core_equiv C d;

/*
  Phase 9 object truncation and recursive directed dimension.

  `IsObjTruncCat(n,C)` constrains only `Obj(C)`. Directed dimension is a
  separate nonnegative recursion: dimension zero is the exact discrete-
  category contract, and each successor asks every hom-category to have the
  preceding dimension. `NCat(n)` retains that evidence in a named package.
*/
// Independent object-truncation property; this is not directed dimension.
symbol IsObjTruncCat
  (n : TruncLevel)
  (C : Cat)
  : Grpd
≔ IsTruncGrpd n (Obj C);

/*
  Native fixed-map categorical equivalence preserves object truncation.

  Package the selected functor and its equality-valued evidence, use the
  stable facade cast to obtain the category path, and map `Obj` over it. This
  is theorem-level transport; the stable cast deliberately supplies no
  package-to-raw-path reflexive computation.
*/
symbol omega_equiv_along_obj_path
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  : τ (@= Grpd_grpd (Obj A) (Obj B))
≔ @eq_ap
    (Obj Cat_cat)
    Grpd_grpd
    (λ C : τ (Obj Cat_cat), Obj C)
    A
    B
    (@omega_cast_to_object_path
      Cat_cat A B
      (@omega_equiv_pack Cat_cat A B F u));

symbol omega_equiv_along_obj_type_equiv
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  : τ (TypeEquiv (Obj A) (Obj B))
≔ @idtoequiv_grpd
    (Obj A)
    (Obj B)
    (@omega_equiv_along_obj_path A B F u);

symbol is_obj_trunc_cat_equiv_type_equiv
  [n : TruncLevel]
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  : τ (TypeEquiv (IsObjTruncCat n A) (IsObjTruncCat n B))
≔ @is_trunc_grpd_type_equiv
    n
    (Obj A)
    (Obj B)
    (@omega_equiv_along_obj_type_equiv A B F u);

symbol is_obj_trunc_cat_equiv_to
  [n : TruncLevel]
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (h : τ (IsObjTruncCat n A))
  : τ (IsObjTruncCat n B)
≔ type_equiv_to
    (@is_obj_trunc_cat_equiv_type_equiv n A B F u) h;

symbol is_obj_trunc_cat_equiv_from
  [n : TruncLevel]
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (h : τ (IsObjTruncCat n B))
  : τ (IsObjTruncCat n A)
≔ type_equiv_from
    (@is_obj_trunc_cat_equiv_type_equiv n A B F u) h;

// Native nonnegative directed-dimension codes.
inductive CatDim : TYPE ≔
| cat_zero : CatDim
| cat_succ : CatDim → CatDim;

// Groupoidal truncation level predicted for objects of an n-category.
symbol cat_dim_trunc_level
  (n : CatDim)
  : TruncLevel;

// Dimension zero has set-valued objects; successor raises truncation once.
rule cat_dim_trunc_level cat_zero
  ↪ trunc_zero
with cat_dim_trunc_level (cat_succ $n)
  ↪ trunc_succ (cat_dim_trunc_level $n);

// Recursive finite directed dimension in the iterated-hom architecture.
symbol IsNCat
  (n : CatDim)
  (C : Cat)
  : Grpd;

// Zero-dimensional categories are discrete; successor dimension recurses on
// every hom-category.
rule IsNCat cat_zero $C
  ↪ IsDiscreteCat $C
with IsNCat (cat_succ $n) $C
  ↪ @Pi_grpd (Obj $C)
      (λ x : τ (Obj $C),
        @Pi_grpd (Obj $C)
          (λ y : τ (Obj $C),
            IsNCat $n (Hom_cat $C x y)));

/*
  Representation-independent truncation raising used by the native finite-dimension theorem.
*/
// Proposition-valued classifiers are truncated at every native CatDim level.
injective symbol prop_is_trunc_cat_dim
  (n : CatDim)
  [A : Grpd]
  (h : τ (IsPropGrpd A))
  : τ (IsTruncGrpd (cat_dim_trunc_level n) A);

// The zero target is set truncation; each successor follows the native index.
rule @prop_is_trunc_cat_dim cat_zero $A $h
  ↪ @prop_is_trunc_succ trunc_minus_one $A $h
with @prop_is_trunc_cat_dim (cat_succ $n) $A $h
  ↪ @prop_is_trunc_succ (cat_dim_trunc_level $n) $A $h;

// Evidence-retaining package of categories of directed dimension n.
(n : CatDim) inductive NCatData : TYPE ≔
| Struct_ncat
    (carrier : Cat)
    (evidence : τ (IsNCat n carrier))
    : NCatData n;

// Decoded classifier of finite-dimensional category packages.
constant symbol NCat
  (n : CatDim)
  : Grpd;

// Package decoding beta.
rule τ (NCat $n)
  ↪ NCatData $n;

// Carrier projection from a finite-dimensional category package.
symbol ncat_carrier
  [n : CatDim]
  (X : τ (NCat n))
  : Cat;

// Carrier-projection constructor beta.
rule ncat_carrier
  (@Struct_ncat _ $carrier _)
  ↪ $carrier;

// Directed-dimension evidence projection for the selected carrier.
symbol ncat_evidence
  [n : CatDim]
  (X : τ (NCat n))
  : τ (IsNCat n (ncat_carrier X));

// Evidence-projection constructor beta; evidence remains explicit data.
rule ncat_evidence
  (@Struct_ncat _ _ $evidence)
  ↪ $evidence;

// Zero- and one-dimensional package aliases.
symbol ZeroCat : Grpd
≔ NCat cat_zero;

symbol OneCat : Grpd
≔ NCat (cat_succ cat_zero);

// A packaged zero-category is a concrete nonliteral groupoidal category.
symbol zero_cat_is_groupoidal
  (X : τ ZeroCat)
  : τ (@IsGroupoidalCat (@ncat_carrier cat_zero X))
≔ @discrete_cat_is_groupoidal
    (@ncat_carrier cat_zero X)
    (@ncat_evidence cat_zero X);

// Every hom-category of a packaged one-category is discrete.
symbol one_cat_hom_discrete
  (X : τ OneCat)
  (x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X)))
  : τ (IsDiscreteCat
      (Hom_cat (@ncat_carrier (cat_succ cat_zero) X) x y))
≔ @ncat_evidence (cat_succ cat_zero) X x y;

/*
  Opposite of an ordinary transfor.

  A component F[x] -> G[x] in B becomes G[x] -> F[x] in B^op. Vertical
  composition order reverses, while the off-diagonal action swaps its base
  endpoints.
*/
injective symbol Op_transf
  [A B : Cat]
  [F G : τ (Functor A B)]
  (eta : τ (Transf F G))
  : τ (Transf
      (@Op_func A B G)
      (@Op_func A B F));

// Opposite-transfor involution.
rule @Op_transf
      (Op_cat $A) (Op_cat $B)
      (@Op_func $A $B $G)
      (@Op_func $A $B $F)
      (@Op_transf $A $B $F $G $eta)
  ↪ $eta;

// Opposite sends identity to identity on the opposite functor.
rule @Op_transf
      $A $B
      $F $F
      (@id (Functor_cat $A $B) $F)
  ↪ @id
      (Functor_cat (Op_cat $A) (Op_cat $B))
      (@Op_func $A $B $F);

// Opposite reverses the order of vertical transfor composition.
rule @Op_transf
      $A $B
      $F $H
      (@comp_fapp0
        (Functor_cat $A $B)
        $F $G $H
        $eta $epsilon)
  ↪ @comp_fapp0
      (Functor_cat (Op_cat $A) (Op_cat $B))
      (@Op_func $A $B $H)
      (@Op_func $A $B $G)
      (@Op_func $A $B $F)
      (@Op_transf $A $B $F $G $epsilon)
      (@Op_transf $A $B $G $H $eta);

// Components of the opposite transfor reuse the underlying component arrow.
rule @tapp0_fapp0
      _ _
      _ _
      $x
      (@Op_transf $A $B $F $G $eta)
  ↪ @tapp0_fapp0 $A $B $F $G $x $eta;

// 6b. Internalized hom endpoint actions and rigid two-sided projections

// Component of `hom_int` along its contravariant represented-object argument.
// For f : X ->^A Y, the displayed functor Hom(Y,F-) ⊢ Hom(X,F-) is
// precomposition by f.
rule @tapp0_fapp0
      $B
      Cat_cat
      _
      _
      $b
      (@hom_int_precomp_func $A $B $F $Y $X $f)
  ↪ @hom_precomp_along_func
      $A
      $A
      (@id_func $A)
      (@fapp0 $B $A $F $b)
      $X
      $Y
      $f;

// Direct generic `fapp1_fapp0(hom_int)` component joins the named projection.
rule @tapp0_fapp0
      $B
      Cat_cat
      _
      _
      $b
      (@fapp1_fapp0 (Op_cat $A) (@Catd_cat $B)
        (@hom_int $A $B $F) $Y $X $f)
  ↪ @hom_precomp_along_func
      $A
      $A
      (@id_func $A)
      (@fapp0 $B $A $F $b)
      $X
      $Y
      $f;

// Component of `hom_int` in the represented object is precomposition.

// Component of the target-internalized mirror is postcomposition by f.
rule @tapp0_fapp0
      _ Cat_cat
      _ _
      $b
      (@hom_con_int_postcomp_func $A $B $F $W $X $f)
  ↪ @hom_postcomp_func
      $A $A (@id_func $A)
      (@fapp0 $B $A $F $b)
      $W $X $f;

// Reserved capped ordinary hom-action surface. It is not used by v3.2 rules
// yet.
//
// Surface/formula:
//   tapp1_fapp0(ϵ,f) : F[X] ->^B G[Y]
//
// The intended computation is the projected endpoint of
// `tapp1_int_func_transf`: evaluate the internal action at ϵ, project the
// resulting transfor at X and then Y, and finally apply the resulting hom
// functor to f. Keep it abstract until the external ordinary naturality API is
// promoted.
symbol tapp1_fapp0 : Π [A B : Cat], Π [F G : τ (Functor A B)],
  Π [X Y : τ (Obj A)],
  Π (ϵ : τ (Obj (Transf_cat F G))),
  Π (f : τ (Hom A X Y)),
  τ (Hom B (fapp0 F X) (fapp0 G Y));

// Functor-level off-diagonal ordinary transfor component.
//
// Surface/formula:
//   tapp1_func(ϵ,X,Y) : Hom_A(X,Y) ⊢ Hom_B(F[X],G[Y])
//   tapp1_func(ϵ,X,Y)[f] = tapp1_fapp0(ϵ,f).
symbol tapp1_func : Π [A B : Cat], Π [F G : τ (Functor A B)],
  Π [X Y : τ (Obj A)],
  Π (ϵ : τ (Obj (Transf_cat F G))),
  τ (Functor
      (Hom_cat A X Y)
      (Hom_cat B (fapp0 F X) (fapp0 G Y)));

// Evaluation of the off-diagonal transfor component functor.
//
// Surface/formula:
//   tapp1_func(epsilon,X,Y)[f] = tapp1_fapp0(epsilon,f).
rule fapp0 (@tapp1_func $A $B $F $G $X $Y $ϵ) $f
  ↪ @tapp1_fapp0 $A $B $F $G $X $Y $ϵ $f;

// Point component of Path_cat_func's second action.
rule @tapp0_fapp0
      _ _ _ _
      $x
      (@fapp1_fapp0
        _ (Functor_cat (Path_cat $A) (Path_cat $B))
        (@fapp1_func
          Grpd_cat Cat_cat Path_cat_func $A $B)
        $f $g $h)
  ↪ @PiHapply
      $A (λ _ : τ $A, $B) $f $g $h $x;

// Full off-diagonal action of the induced Path transfor remains iterable.
rule @tapp1_func
      _ _ _ _
      $x $y
      (@fapp1_fapp0
        (Path_cat (@Pi_grpd $A (λ _ : τ $A, $B)))
        (Functor_cat (Path_cat $A) (Path_cat $B))
        (@fapp1_func
          Grpd_cat Cat_cat Path_cat_func $A $B)
        $f $g $h)
  ↪ @fapp1_fapp0
      Grpd_cat Cat_cat Path_cat_func
      (@= $A $x $y)
      (@= $B ($f $x) ($g $y))
      (λ p : τ (@= $A $x $y),
        @path_map_transf_cell
          $A $B $f $g $h $x $y p);

// Capped off-diagonal action of the induced Path transfor.
rule @tapp1_fapp0
      _ _ _ _
      $x $y
      (@fapp1_fapp0
        (Path_cat (@Pi_grpd $A (λ _ : τ $A, $B)))
        (Functor_cat (Path_cat $A) (Path_cat $B))
        (@fapp1_func
          Grpd_cat Cat_cat Path_cat_func $A $B)
        $f $g $h)
      $p
  ↪ @path_map_transf_cell
      $A $B $f $g $h $x $y $p;

// The higher action of internalized precomposition is the two-endpoint Hom
// action on the fixed represented arrow and the varying arrow of F.
// lhs-audit: keep 3,4 -- required subject-reduction endpoints of the Catd-valued hom component.
rule @tapp1_func
      $B Cat_cat
      (@hom_ $A $B $F $Y)
      (@hom_ $A $B $F $X)
      $b $c
      (@hom_int_precomp_func $A $B $F $Y $X $p)
  ↪ @comp_fapp0
      Cat_cat
      (Hom_cat $B $b $c)
      (Product_cat
        (Hom_cat $A $X $Y)
        (Hom_cat
          $A
          (@fapp0 $B $A $F $b)
          (@fapp0 $B $A $F $c)))
      (Functor_cat
        (Hom_cat $A $Y (@fapp0 $B $A $F $b))
        (Hom_cat $A $X (@fapp0 $B $A $F $c)))
      (@Hom_tele_func
        $A
        $Y
        $X
        (@fapp0 $B $A $F $b)
        (@fapp0 $B $A $F $c))
      (Struct_sigma
        (@Const_func
          (Hom_cat $B $b $c)
          (Hom_cat $A $X $Y)
          $p)
        (@fapp1_func $B $A $F $b $c));

// Projection-order join for the capped off-diagonal component.
// lhs-audit: keep 3,4 -- required subject-reduction endpoints of the Catd-valued hom component.
rule @tapp1_fapp0
      $B Cat_cat
      (@hom_ $A $B $F $Y)
      (@hom_ $A $B $F $X)
      $b $c
      (@hom_int_precomp_func $A $B $F $Y $X $p)
      $q
  ↪ @Hom_func
      $A
      $Y
      $X
      (@fapp0 $B $A $F $b)
      (@fapp0 $B $A $F $c)
      $p
      (@fapp1_fapp0 $B $A $F $b $c $q);

// Higher action of target-internalized postcomposition:
// q |-> Hom_func(F[q],f).
rule @tapp1_func
      _ Cat_cat
      _ _
      $b $c
      (@hom_con_int_postcomp_func $A $B $F $W $X $f)
  ↪ @comp_fapp0
      Cat_cat
      (Hom_cat (Op_cat $B) $b $c)
      (Product_cat
        (Hom_cat
          $A
          (@fapp0 $B $A $F $c)
          (@fapp0 $B $A $F $b))
        (Hom_cat $A $W $X))
      (Functor_cat
        (Hom_cat $A (@fapp0 $B $A $F $b) $W)
        (Hom_cat $A (@fapp0 $B $A $F $c) $X))
      (@Hom_tele_func
        $A
        (@fapp0 $B $A $F $b)
        (@fapp0 $B $A $F $c)
        $W
        $X)
      (Struct_sigma
        (@fapp1_func $B $A $F $c $b)
        (@Const_func
          (Hom_cat (Op_cat $B) $b $c)
          (Hom_cat $A $W $X)
          $f));

// Capped higher action of target-internalized postcomposition is rigid `Hom_func`.
rule @tapp1_fapp0
      _ Cat_cat
      _ _
      $b $c
      (@hom_con_int_postcomp_func $A $B $F $W $X $f)
      $q
  ↪ @Hom_func
      $A
      (@fapp0 $B $A $F $b)
      (@fapp0 $B $A $F $c)
      $W
      $X
      (@fapp1_fapp0 $B $A $F $c $b $q)
      $f;

// Product-valued off-diagonal components project componentwise.
rule sigma_Fst (@tapp1_func $X (Product_cat $A $B) $F $G $i $j $eta)
  ↪ @tapp1_func $X $A (sigma_Fst $F) (sigma_Fst $G) $i $j (sigma_Fst $eta);

// Right projection of product-valued full off-diagonal action is pointwise.
rule sigma_Snd (@tapp1_func $X (Product_cat $A $B) $F $G $i $j $eta)
  ↪ @tapp1_func $X $B (sigma_Snd $F) (sigma_Snd $G) $i $j (sigma_Snd $eta);

// Identity transfor off-diagonal action is ordinary functor hom-action.
rule @tapp1_func $A $B $F $F $X $Y (@id (Functor_cat $A $B) $F)
  ↪ @fapp1_func $A $B $F $X $Y;

// Opposite transfor off-diagonal action swaps the base endpoints.
rule @tapp1_func
      _ _
      _ _
      $x $y
      (@Op_transf $A $B $F $G $eta)
  ↪ @tapp1_func $A $B $F $G $y $x $eta;

// Cat instance of product-composition arrow action. This is the generic
// horizontal action owner for ordinary transfors; the older covariant and
// contravariant Cat heads are compatibility surfaces for one-slot views.
rule @tapp0_fapp0
      _ _
      _ _
      $i
      (@comp_prod_fapp1_fapp0 Cat_cat $X $Y $Z $FG $FG' $theta)
  ↪ @tapp1_fapp0
      $Y
      $Z
      (sigma_Snd $FG)
      (sigma_Snd $FG')
      (@fapp0 $X $Y (sigma_Fst $FG) $i)
      (@fapp0 $X $Y (sigma_Fst $FG') $i)
      (sigma_Snd $theta)
      (@tapp0_fapp0
        $X
        $Y
        (sigma_Fst $FG)
        (sigma_Fst $FG')
        $i
        (sigma_Fst $theta));

// Full off-diagonal action of generic Cat product-composition action.
rule @tapp1_func
      _ _
      _ _
      $i
      $j
      (@comp_prod_fapp1_fapp0 Cat_cat $X $Y $Z $FG $FG' $theta)
  ↪ @comp_cat_fapp0
      (Hom_cat $X $i $j)
      (Hom_cat
        $Y
        (@fapp0 $X $Y (sigma_Fst $FG) $i)
        (@fapp0 $X $Y (sigma_Fst $FG') $j))
      (Hom_cat
        $Z
        (@fapp0 $Y $Z (sigma_Snd $FG) (@fapp0 $X $Y (sigma_Fst $FG) $i))
        (@fapp0 $Y $Z (sigma_Snd $FG') (@fapp0 $X $Y (sigma_Fst $FG') $j)))
      (@tapp1_func
        $Y
        $Z
        (sigma_Snd $FG)
        (sigma_Snd $FG')
        (@fapp0 $X $Y (sigma_Fst $FG) $i)
        (@fapp0 $X $Y (sigma_Fst $FG') $j)
        (sigma_Snd $theta))
      (@tapp1_func
        $X
        $Y
        (sigma_Fst $FG)
        (sigma_Fst $FG')
        $i
        $j
        (sigma_Fst $theta));

// Capped off-diagonal action of generic Cat product-composition action.
rule @tapp1_fapp0
      _ _
      _ _
      $i
      $j
      (@comp_prod_fapp1_fapp0 Cat_cat $X $Y $Z $FG $FG' $theta)
      $p
  ↪ @tapp1_fapp0
      $Y
      $Z
      (sigma_Snd $FG)
      (sigma_Snd $FG')
      (@fapp0 $X $Y (sigma_Fst $FG) $i)
      (@fapp0 $X $Y (sigma_Fst $FG') $j)
      (sigma_Snd $theta)
      (@tapp1_fapp0
        $X
        $Y
        (sigma_Fst $FG)
        (sigma_Fst $FG')
        $i
        $j
        (sigma_Fst $theta)
        $p);

// Identity pair of transfors collapses to the identity on the composite functor.
rule @comp_prod_fapp1_fapp0
      Cat_cat
      $X
      $Y
      $Z
      (Struct_sigma $F $G)
      (Struct_sigma $F $G)
      (Struct_sigma
        (@id (Functor_cat $X $Y) $F)
        (@id (Functor_cat $Y $Z) $G))
  ↪ @id
      (Functor_cat $X $Z)
      (@comp_cat_fapp0 $X $Y $Z $G $F);

// 6c. Constant/opposite transfors and Cat-valued composition projections

/*
  Constant transfor induced by an arrow in the codomain.

  Mathematical notation:
    Const_transf_func(K,A,x,y)
      : Hom_A(x,y) ⊢ Transf(const x,const y)

    Const_transf(p)[k] = p
    Const_transf(p)[q] = p

  Canonical comment syntax:
    k :^n K ; 1[k] ⊢ (p : x ->^A y)

  The component and off-diagonal action are constant in the K-variable. This
  is the transfor-level counterpart of Const_func.
*/
symbol Const_transf_func [K A : Cat] [x y : τ (Obj A)]
  : τ (Functor
      (Hom_cat A x y)
      (@Transf_cat K A (@Const_func K A x) (@Const_func K A y)));

// Constant transfor selected by the codomain arrow p.
symbol Const_transf [K A : Cat] [x y : τ (Obj A)]
  (p : τ (Hom A x y))
  : τ (Transf (@Const_func K A x) (@Const_func K A y));

// Applying the constructor functor selects `Const_transf(p)`.
rule fapp0 (@Const_transf_func $K $A $x $y) $p
  ↪ @Const_transf $K $A $x $y $p;

// Constant transfor components are the same codomain arrow at every object.
rule @tapp0_fapp0 $K $A _ _ $k (@Const_transf $K $A $x $y $p)
  ↪ $p;

// Constant transfor off-diagonal action is constant on the base arrow.
rule @tapp1_func $K $A _ _ $k $k' (@Const_transf $K $A $x $y $p)
  ↪ @Const_func (Hom_cat $K $k $k') (Hom_cat $A $x $y) $p;

// Capped off-diagonal action of a constant transfor returns p.
rule @tapp1_fapp0 $K $A _ _ $k $k' (@Const_transf $K $A $x $y $p) $_
  ↪ $p;

/*
  Pure Cat/Catd convenience helpers.

  These names are transparent presentations of the generic hom-action
  architecture specialized to the identity family on `Cat_cat`. They remain
  useful in readable semantic bodies, but rewrite rules should key on the
  corresponding generic `hom_*` owner unless a later Cat-only transfor
  projection is the actual extra structure.
*/

// Curried postcomposition in Cat, used to build constructor pipelines.
//
// Surface/formula:
//   comp_cat_cov_func(G) : (X ⊢ Y) ⊢ (X ⊢ Z)
//   comp_cat_cov_func(G)[F] = G ∘ F.
symbol comp_cat_cov_func [X Y Z : Cat]
  (G : τ (Functor Y Z))
  : τ (Functor (Functor_cat X Y) (Functor_cat X Z))
≔ @hom_postcomp_func
    Cat_cat
    Cat_cat
    (@id Cat_cat Cat_cat)
    X
    Y
    Z
    G;

/*
  Internal lift of an object function A -> Obj(C) to a functor
  Path_cat(A) -> C. This is semantic postcomposition of Path_cat_func's first
  action by Core_incl_func(C); no primitive PathLift head is introduced.
*/
symbol path_lift_func
  [A : Grpd]
  [C : Cat]
  : τ (Functor
      (Path_cat (@Function_grpd A (Obj C)))
      (Functor_cat (Path_cat A) C))
≔ @comp_cat_fapp0
    (Path_cat (@Function_grpd A (Obj C)))
    (Functor_cat (Path_cat A) (Core_cat C))
    (Functor_cat (Path_cat A) C)
    (@comp_cat_cov_func
      (Path_cat A) (Core_cat C) C
      (Core_incl_func C))
    (@fapp1_func
      Grpd_cat Cat_cat Path_cat_func
      A (Obj C));

// Postcomposition packaged as a functor in the postcomposing functor.
//
// Surface/formula:
//   comp_cat_cov_func_func[X,Y,Z][G] = comp_cat_cov_func(G)
//   : (Y ⊢ Z) ⊢ ((X ⊢ Y) ⊢ (X ⊢ Z)).
symbol comp_cat_cov_func_func [X Y Z : Cat]
  : τ (Functor
      (Functor_cat Y Z)
      (Functor_cat (Functor_cat X Y) (Functor_cat X Z)))
≔ @hom_postcomp_tele_func
    Cat_cat
    Cat_cat
    (@id Cat_cat Cat_cat)
    X
    Y
    Z;

// Precomposition by a fixed functor.
//
// Surface/formula:
//   comp_cat_con_func(F)[G] = G ∘ F
//   : (Y ⊢ Z) ⊢ (X ⊢ Z).
symbol comp_cat_con_func [X Y Z : Cat]
  (F : τ (Functor X Y))
  : τ (Functor (Functor_cat Y Z) (Functor_cat X Z))
≔ @hom_precomp_along_func
    Cat_cat
    Cat_cat
    (@id Cat_cat Cat_cat)
    Z
    X
    Y
    F;

// Precomposition packaged as a functor in the precomposing functor.
//
// Surface/formula:
//   comp_cat_con_func_func[X,Y,Z][F] = comp_cat_con_func(F)
//   : (X ⊢ Y) ⊢ ((Y ⊢ Z) ⊢ (X ⊢ Z)).
symbol comp_cat_con_func_func [X Y Z : Cat]
  : τ (Functor
      (Functor_cat X Y)
      (Functor_cat (Functor_cat Y Z) (Functor_cat X Z)))
≔ @hom_precomp_along_tele_func
    Cat_cat
    Cat_cat
    (@id Cat_cat Cat_cat)
    Z
    X
    Y;

// Postcomposition by internal opposite is the pointwise opposite-family functor.
rule @hom_postcomp_func Cat_cat Cat_cat (@id Cat_cat Cat_cat) $Z Cat_cat Cat_cat op
  ↪ @Op_catd_func $Z;

/*
  Cat-specialized semantic heads package extra structure exposed only when the
  ambient category is `Cat_cat`. The generic `hom_postcomp_*` and
  `hom_precomp_along_*` owners still describe the hom-action, but after
  specializing to `Cat_cat` the result is a transfor and can expose
  `tapp0_fapp0`, `tapp1_func`, and `tapp1_fapp0` projections without long
  Cat-specialized hom-action patterns.
*/

/*
  Postcomposition of transfors by a fixed functor.

  Mathematical notation:
    comp_cat_cov_fapp1_func(G)
      : Transf(F,H) ⊢ Transf(G ∘ F, G ∘ H)

    hom_postcomp_fapp1_fapp0(G,eta)
      = comp_prod_fapp1_fapp0 Cat_cat (eta,id_G)
    hom_postcomp_fapp1_fapp0(G,eta)[i] = G[eta[i]]

  Canonical comment syntax:
    eta : F => H
    G eta : G ∘ F => G ∘ H

  The name follows the ordinary `comp_cat_cov_func(G)` object action: the
  functor argument varies covariantly in the slot being postcomposed by G.
*/
symbol comp_cat_cov_fapp1_func [X Y Z : Cat]
  (G : τ (Functor Y Z))
  [F H : τ (Functor X Y)]
  : τ (Functor
      (@Transf_cat X Y F H)
      (@Transf_cat
        X Z
        (@comp_cat_fapp0 X Y Z G F)
        (@comp_cat_fapp0 X Y Z G H)))
≔ @hom_postcomp_fapp1_func
    Cat_cat
    Cat_cat
    (@id Cat_cat Cat_cat)
    X
    Y
    Z
    G
    F
    H;

// Cat-valued capped postcomposition exposes ordinary transfor projections.
rule @hom_postcomp_fapp1_fapp0 Cat_cat $K $E $W $X $Y $f $G $H $eta
  ↪ @comp_prod_fapp1_fapp0
      Cat_cat
      $W
      (@fapp0 $K Cat_cat $E $X)
      (@fapp0 $K Cat_cat $E $Y)
      (@Product_pair
        (Functor_cat $W (@fapp0 $K Cat_cat $E $X))
        (Functor_cat (@fapp0 $K Cat_cat $E $X) (@fapp0 $K Cat_cat $E $Y))
        $G
        (@fapp1_fapp0 $K Cat_cat $E $X $Y $f))
      (@Product_pair
        (Functor_cat $W (@fapp0 $K Cat_cat $E $X))
        (Functor_cat (@fapp0 $K Cat_cat $E $X) (@fapp0 $K Cat_cat $E $Y))
        $H
        (@fapp1_fapp0 $K Cat_cat $E $X $Y $f))
      (@Product_pair
        (Hom_cat (Functor_cat $W (@fapp0 $K Cat_cat $E $X)) $G $H)
        (Hom_cat
          (Functor_cat (@fapp0 $K Cat_cat $E $X) (@fapp0 $K Cat_cat $E $Y))
          (@fapp1_fapp0 $K Cat_cat $E $X $Y $f)
          (@fapp1_fapp0 $K Cat_cat $E $X $Y $f))
        $eta
        (@id
          (Functor_cat (@fapp0 $K Cat_cat $E $X) (@fapp0 $K Cat_cat $E $Y))
          (@fapp1_fapp0 $K Cat_cat $E $X $Y $f)));

// The old `comp_cat_cov_transf` compatibility name has been removed; the Cat
// product-composition owner exposes its projections and identity collapse.

/*
  Hom-action of postcomposition as a functor in the postcomposing functor.

  Mathematical notation:
    comp_cat_cov_func_func[X,Y,Z]
      : (Y ⊢ Z) ⊢ ((X ⊢ Y) ⊢ (X ⊢ Z))

    comp_cat_cov_func_func_transf(eta)
      : (G ∘ -) => (H ∘ -)

    comp_cat_cov_func_func_transf(eta)[F]
      = eta ∘ F : G ∘ F => H ∘ F.

  Canonical comment syntax:
    eta : G => H
    eta ∘ F : G ∘ F => H ∘ F

  Its object component at F is precomposition of eta by F, implemented by the
  identity-first Cat instance of `comp_prod_fapp1_fapp0`.
*/
symbol comp_cat_cov_func_func_fapp1_func [X Y Z : Cat]
  [G H : τ (Functor Y Z)]
  : τ (Functor
      (@Transf_cat Y Z G H)
      (@Transf_cat
        (Functor_cat X Y)
        (Functor_cat X Z)
        (@comp_cat_cov_func X Y Z G)
        (@comp_cat_cov_func X Y Z H)))
≔ @hom_postcomp_tele_fapp1_func
    Cat_cat
    Cat_cat
    (@id Cat_cat Cat_cat)
    X
    Y
    Z
    G
    H;

// Cat-valued tele-postcomposition exposes ordinary transfor projections
// through the unspecialized telescope-transfor owner.
rule @hom_postcomp_tele_fapp1_fapp0
      Cat_cat
      $K
      $E
      $W
      $X
      $Y
      $G
      $H
      $eta
  ↪ @hom_postcomp_tele_transf Cat_cat $K $E $W $X $Y $G $H $eta;

// Transparent identity-family name for tele-postcomposition of a transfor.
symbol comp_cat_cov_func_func_transf [X Y Z : Cat]
  [G H : τ (Functor Y Z)]
  (eta : τ (Transf G H))
  : τ (Transf
      (@comp_cat_cov_func X Y Z G)
      (@comp_cat_cov_func X Y Z H))
≔ @hom_postcomp_tele_transf
    Cat_cat
    Cat_cat
    (@id Cat_cat Cat_cat)
    X
    Y
    Z
    G
    H
    eta;

/*
  Precomposition of transfors by a fixed functor.

  Mathematical notation:
    comp_cat_con_fapp1_func(F)
      : Transf(G,H) ⊢ Transf(G ∘ F,H ∘ F)

    hom_precomp_along_fapp1_fapp0(F,eta)
      = comp_prod_fapp1_fapp0 Cat_cat (id_F,eta)
    hom_precomp_along_fapp1_fapp0(F,eta)[i] = eta[F[i]]

  Canonical comment syntax:
    eta : G => H
    eta ∘ F : G ∘ F => H ∘ F
*/
symbol comp_cat_con_fapp1_func [X Y Z : Cat]
  (F : τ (Functor X Y))
  [G H : τ (Functor Y Z)]
  : τ (Functor
      (@Transf_cat Y Z G H)
      (@Transf_cat
        X Z
        (@comp_cat_fapp0 X Y Z G F)
        (@comp_cat_fapp0 X Y Z H F)))
≔ @hom_precomp_along_fapp1_func
    Cat_cat
    Cat_cat
    (@id Cat_cat Cat_cat)
    Z
    X
    Y
    F
    G
    H;

// Component of tele-postcomposition in an arbitrary ambient category.
rule @tapp0_fapp0
      _
      _
      _
      _
      $u
      (@hom_postcomp_tele_transf $A $B $F $W $X $Y $f $g $alpha)
  ↪ @comp_prod_fapp1_fapp0
      $A
      $W
      (@fapp0 $B $A $F $X)
      (@fapp0 $B $A $F $Y)
      (@Product_pair
        (Hom_cat $A $W (@fapp0 $B $A $F $X))
        (Hom_cat $A (@fapp0 $B $A $F $X) (@fapp0 $B $A $F $Y))
        $u
        (@fapp1_fapp0 $B $A $F $X $Y $f))
      (@Product_pair
        (Hom_cat $A $W (@fapp0 $B $A $F $X))
        (Hom_cat $A (@fapp0 $B $A $F $X) (@fapp0 $B $A $F $Y))
        $u
        (@fapp1_fapp0 $B $A $F $X $Y $g))
      (@Product_pair
        (Hom_cat (Hom_cat $A $W (@fapp0 $B $A $F $X)) $u $u)
        (Hom_cat
          (Hom_cat $A (@fapp0 $B $A $F $X) (@fapp0 $B $A $F $Y))
          (@fapp1_fapp0 $B $A $F $X $Y $f)
          (@fapp1_fapp0 $B $A $F $X $Y $g))
        (@id (Hom_cat $A $W (@fapp0 $B $A $F $X)) $u)
        (@fapp1_fapp0
          (Hom_cat $B $X $Y)
          (Hom_cat $A (@fapp0 $B $A $F $X) (@fapp0 $B $A $F $Y))
          (@fapp1_func $B $A $F $X $Y)
          $f
          $g
          $alpha));

// Full hom action of precomposition as the precomposing functor varies.
symbol comp_cat_con_func_func_fapp1_func [X Y Z : Cat]
  [F K : τ (Functor X Y)]
  : τ (Functor
      (@Transf_cat X Y F K)
      (@Transf_cat
        (Functor_cat Y Z)
        (Functor_cat X Z)
        (@comp_cat_con_func X Y Z F)
        (@comp_cat_con_func X Y Z K)))
≔ @hom_precomp_along_tele_fapp1_func
    Cat_cat
    Cat_cat
    (@id Cat_cat Cat_cat)
    Z
    X
    Y
    F
    K;

// Hom-action of precomposition as a functor in the precomposing functor.
//
// Surface/formula:
//   alpha : F => K
//   comp_cat_con_func_func_transf(alpha)[G] = G alpha.
// Cat-valued tele-precomposition exposes ordinary transfor projections through
// the unspecialized telescope-transfor owner.
rule @hom_precomp_along_tele_fapp1_fapp0
      $K
      Cat_cat
      $E
      $Z
      $X
      $Y
      $F
      $H
      $alpha
  ↪ @hom_precomp_along_tele_transf $K Cat_cat $E $Z $X $Y $F $H $alpha;

// Transparent identity-family name for tele-precomposition of a transfor.
symbol comp_cat_con_func_func_transf [X Y Z : Cat]
  [F K : τ (Functor X Y)]
  (alpha : τ (Transf F K))
  : τ (Transf
      (@comp_cat_con_func X Y Z F)
      (@comp_cat_con_func X Y Z K))
≔ @hom_precomp_along_tele_transf
    Cat_cat
    Cat_cat
    (@id Cat_cat Cat_cat)
    Z
    X
    Y
    F
    K
    alpha;

// Component of tele-precomposition in an arbitrary ambient category.
//
// Surface/formula:
//   comp_cat_con_func_func_transf(alpha)[G] = G alpha.
rule @tapp0_fapp0
      _
      _
      _
      _
      $g
      (@hom_precomp_along_tele_transf $A $B $F $Z $W $X $h $k $alpha)
  ↪ @comp_prod_fapp1_fapp0
      $B
      (@fapp0 $A $B $F $W)
      (@fapp0 $A $B $F $X)
      $Z
      (@Product_pair
        (Hom_cat $B (@fapp0 $A $B $F $W) (@fapp0 $A $B $F $X))
        (Hom_cat $B (@fapp0 $A $B $F $X) $Z)
        (@fapp1_fapp0 $A $B $F $W $X $h)
        $g)
      (@Product_pair
        (Hom_cat $B (@fapp0 $A $B $F $W) (@fapp0 $A $B $F $X))
        (Hom_cat $B (@fapp0 $A $B $F $X) $Z)
        (@fapp1_fapp0 $A $B $F $W $X $k)
        $g)
      (@Product_pair
        (Hom_cat
          (Hom_cat $B (@fapp0 $A $B $F $W) (@fapp0 $A $B $F $X))
          (@fapp1_fapp0 $A $B $F $W $X $h)
          (@fapp1_fapp0 $A $B $F $W $X $k))
        (Hom_cat (Hom_cat $B (@fapp0 $A $B $F $X) $Z) $g $g)
        (@fapp1_fapp0
          (Hom_cat $A $W $X)
          (Hom_cat $B (@fapp0 $A $B $F $W) (@fapp0 $A $B $F $X))
          (@fapp1_func $A $B $F $W $X)
          $h
          $k
          $alpha)
        (@id (Hom_cat $B (@fapp0 $A $B $F $X) $Z) $g));

// Off-diagonal action of postcomposition-in-G.
rule @tapp1_func
      _
      _
      _
      _
      $u
      $v
      (@hom_postcomp_tele_transf $A $B $F $W $X $Y $f $g $eta)
  ↪ @comp_cat_fapp0
      (Hom_cat (Hom_cat $A $W (@fapp0 $B $A $F $X)) $u $v)
      (Hom_cat
        (Product_cat
          (Hom_cat $A $W (@fapp0 $B $A $F $X))
          (Hom_cat $A (@fapp0 $B $A $F $X) (@fapp0 $B $A $F $Y)))
        (@Product_pair
          (Hom_cat $A $W (@fapp0 $B $A $F $X))
          (Hom_cat $A (@fapp0 $B $A $F $X) (@fapp0 $B $A $F $Y))
          $u
          (@fapp1_fapp0 $B $A $F $X $Y $f))
        (@Product_pair
          (Hom_cat $A $W (@fapp0 $B $A $F $X))
          (Hom_cat $A (@fapp0 $B $A $F $X) (@fapp0 $B $A $F $Y))
          $v
          (@fapp1_fapp0 $B $A $F $X $Y $g)))
      (Hom_cat
        (Hom_cat $A $W (@fapp0 $B $A $F $Y))
        (@comp_fapp0
          $A
          $W
          (@fapp0 $B $A $F $X)
          (@fapp0 $B $A $F $Y)
          (@fapp1_fapp0 $B $A $F $X $Y $f)
          $u)
        (@comp_fapp0
          $A
          $W
          (@fapp0 $B $A $F $X)
          (@fapp0 $B $A $F $Y)
          (@fapp1_fapp0 $B $A $F $X $Y $g)
          $v))
      (@comp_prod_fapp1_func
        $A
        $W
        (@fapp0 $B $A $F $X)
        (@fapp0 $B $A $F $Y)
        (@Product_pair
          (Hom_cat $A $W (@fapp0 $B $A $F $X))
          (Hom_cat $A (@fapp0 $B $A $F $X) (@fapp0 $B $A $F $Y))
          $u
          (@fapp1_fapp0 $B $A $F $X $Y $f))
        (@Product_pair
          (Hom_cat $A $W (@fapp0 $B $A $F $X))
          (Hom_cat $A (@fapp0 $B $A $F $X) (@fapp0 $B $A $F $Y))
          $v
          (@fapp1_fapp0 $B $A $F $X $Y $g)))
      (Struct_sigma
        (@id_func (Hom_cat (Hom_cat $A $W (@fapp0 $B $A $F $X)) $u $v))
        (@Const_func
          (Hom_cat (Hom_cat $A $W (@fapp0 $B $A $F $X)) $u $v)
          (Hom_cat
            (Hom_cat $A (@fapp0 $B $A $F $X) (@fapp0 $B $A $F $Y))
            (@fapp1_fapp0 $B $A $F $X $Y $f)
            (@fapp1_fapp0 $B $A $F $X $Y $g))
          (@fapp1_fapp0
            (Hom_cat $B $X $Y)
            (Hom_cat $A (@fapp0 $B $A $F $X) (@fapp0 $B $A $F $Y))
            (@fapp1_func $B $A $F $X $Y)
            $f
            $g
            $eta)));

// Capped horizontal composite of two ordinary transfors.
rule @tapp1_fapp0
      _
      _
      _
      _
      $u
      $v
      (@hom_postcomp_tele_transf $A $B $F $W $X $Y $f $g $eta)
      $beta
  ↪ @comp_prod_fapp1_fapp0
      $A
      $W
      (@fapp0 $B $A $F $X)
      (@fapp0 $B $A $F $Y)
      (@Product_pair
        (Hom_cat $A $W (@fapp0 $B $A $F $X))
        (Hom_cat $A (@fapp0 $B $A $F $X) (@fapp0 $B $A $F $Y))
        $u
        (@fapp1_fapp0 $B $A $F $X $Y $f))
      (@Product_pair
        (Hom_cat $A $W (@fapp0 $B $A $F $X))
        (Hom_cat $A (@fapp0 $B $A $F $X) (@fapp0 $B $A $F $Y))
        $v
        (@fapp1_fapp0 $B $A $F $X $Y $g))
      (@Product_pair
        (Hom_cat (Hom_cat $A $W (@fapp0 $B $A $F $X)) $u $v)
        (Hom_cat
          (Hom_cat $A (@fapp0 $B $A $F $X) (@fapp0 $B $A $F $Y))
          (@fapp1_fapp0 $B $A $F $X $Y $f)
          (@fapp1_fapp0 $B $A $F $X $Y $g))
        $beta
        (@fapp1_fapp0
          (Hom_cat $B $X $Y)
          (Hom_cat $A (@fapp0 $B $A $F $X) (@fapp0 $B $A $F $Y))
          (@fapp1_func $B $A $F $X $Y)
          $f
          $g
          $eta));

// Off-diagonal action of precomposition-in-F.
rule @tapp1_func
      _
      _
      _
      _
      $g
      $j
      (@hom_precomp_along_tele_transf $A $B $F $Z $W $X $h $k $alpha)
  ↪ @comp_cat_fapp0
      (Hom_cat (Hom_cat $B (@fapp0 $A $B $F $X) $Z) $g $j)
      (Hom_cat
        (Product_cat
          (Hom_cat $B (@fapp0 $A $B $F $W) (@fapp0 $A $B $F $X))
          (Hom_cat $B (@fapp0 $A $B $F $X) $Z))
        (@Product_pair
          (Hom_cat $B (@fapp0 $A $B $F $W) (@fapp0 $A $B $F $X))
          (Hom_cat $B (@fapp0 $A $B $F $X) $Z)
          (@fapp1_fapp0 $A $B $F $W $X $h)
          $g)
        (@Product_pair
          (Hom_cat $B (@fapp0 $A $B $F $W) (@fapp0 $A $B $F $X))
          (Hom_cat $B (@fapp0 $A $B $F $X) $Z)
          (@fapp1_fapp0 $A $B $F $W $X $k)
          $j))
      (Hom_cat
        (Hom_cat $B (@fapp0 $A $B $F $W) $Z)
        (@comp_fapp0
          $B
          (@fapp0 $A $B $F $W)
          (@fapp0 $A $B $F $X)
          $Z
          $g
          (@fapp1_fapp0 $A $B $F $W $X $h))
        (@comp_fapp0
          $B
          (@fapp0 $A $B $F $W)
          (@fapp0 $A $B $F $X)
          $Z
          $j
          (@fapp1_fapp0 $A $B $F $W $X $k)))
      (@comp_prod_fapp1_func
        $B
        (@fapp0 $A $B $F $W)
        (@fapp0 $A $B $F $X)
        $Z
        (@Product_pair
          (Hom_cat $B (@fapp0 $A $B $F $W) (@fapp0 $A $B $F $X))
          (Hom_cat $B (@fapp0 $A $B $F $X) $Z)
          (@fapp1_fapp0 $A $B $F $W $X $h)
          $g)
        (@Product_pair
          (Hom_cat $B (@fapp0 $A $B $F $W) (@fapp0 $A $B $F $X))
          (Hom_cat $B (@fapp0 $A $B $F $X) $Z)
          (@fapp1_fapp0 $A $B $F $W $X $k)
          $j))
      (Struct_sigma
        (@Const_func
          (Hom_cat (Hom_cat $B (@fapp0 $A $B $F $X) $Z) $g $j)
          (Hom_cat
            (Hom_cat $B (@fapp0 $A $B $F $W) (@fapp0 $A $B $F $X))
            (@fapp1_fapp0 $A $B $F $W $X $h)
            (@fapp1_fapp0 $A $B $F $W $X $k))
          (@fapp1_fapp0
            (Hom_cat $A $W $X)
            (Hom_cat $B (@fapp0 $A $B $F $W) (@fapp0 $A $B $F $X))
            (@fapp1_func $A $B $F $W $X)
            $h
            $k
            $alpha))
        (@id_func (Hom_cat (Hom_cat $B (@fapp0 $A $B $F $X) $Z) $g $j)));

// Capped horizontal action of tele-precomposition on beta.
rule @tapp1_fapp0
      _
      _
      _
      _
      $g
      $j
      (@hom_precomp_along_tele_transf $A $B $F $Z $W $X $h $k $alpha)
      $beta
  ↪ @comp_prod_fapp1_fapp0
      $B
      (@fapp0 $A $B $F $W)
      (@fapp0 $A $B $F $X)
      $Z
      (@Product_pair
        (Hom_cat $B (@fapp0 $A $B $F $W) (@fapp0 $A $B $F $X))
        (Hom_cat $B (@fapp0 $A $B $F $X) $Z)
        (@fapp1_fapp0 $A $B $F $W $X $h)
        $g)
      (@Product_pair
        (Hom_cat $B (@fapp0 $A $B $F $W) (@fapp0 $A $B $F $X))
        (Hom_cat $B (@fapp0 $A $B $F $X) $Z)
        (@fapp1_fapp0 $A $B $F $W $X $k)
        $j)
      (@Product_pair
        (Hom_cat
          (Hom_cat $B (@fapp0 $A $B $F $W) (@fapp0 $A $B $F $X))
          (@fapp1_fapp0 $A $B $F $W $X $h)
          (@fapp1_fapp0 $A $B $F $W $X $k))
        (Hom_cat (Hom_cat $B (@fapp0 $A $B $F $X) $Z) $g $j)
        (@fapp1_fapp0
          (Hom_cat $A $W $X)
          (Hom_cat $B (@fapp0 $A $B $F $W) (@fapp0 $A $B $F $X))
          (@fapp1_func $A $B $F $W $X)
          $h
          $k
          $alpha)
        $beta);

// Cat-specialized generalized precomposition agrees proof-time with ordinary
// precomposition. Runtime object action remains owned by
// `hom_precomp_along_fapp0`.
unif_rule @hom_precomp_along_func Cat_cat Cat_cat $F $Z $W $X $h
  ≡ @hom_precomp_along_func
      Cat_cat
      Cat_cat
      (@id Cat_cat Cat_cat)
      $Z
      _
      _
      (@fapp1_fapp0 Cat_cat Cat_cat $F $W $X $h)
  ↪ [ tt ≡ tt ];

/*
  Deferred Cat-specialized higher-action folds.

  After `hom_precomp_along_fapp0` became the runtime owner of precomposition
  object action, these previous folds no longer preserve the runtime endpoint
  normal form: `comp_cat_con_*` exposes raw `comp_cat_fapp0` endpoints. Keep
  the object-level Cat fold above, and keep the broad arbitrary-family
  higher-action folds deferred. The identity-family bridge below is narrower:
  it exposes the ordinary Cat transfor projection ladder after the pure
  `comp_cat_con_func` alias has already unfolded to `hom_precomp_along_func`.

  rule @hom_precomp_along_fapp1_func Cat_cat Cat_cat $F $Z $W $X $h $G $H
    ↪ @comp_cat_con_fapp1_func
        (@fapp0 Cat_cat Cat_cat $F $W)
        (@fapp0 Cat_cat Cat_cat $F $X)
        $Z
        (@fapp1_fapp0 Cat_cat Cat_cat $F $W $X $h)
        $G
        $H;

  The capped fold now targets the identity-first `comp_prod_fapp1_fapp0
  Cat_cat` owner directly; the older one-slot compatibility name has been
  removed.
*/

// Cat-valued capped precomposition exposes ordinary transfor projections.
rule @hom_precomp_along_fapp1_fapp0
      $K
      Cat_cat
      $E
      $Z
      $X
      $Y
      $F
      $G
      $H
      $eta
  ↪ @comp_prod_fapp1_fapp0
      Cat_cat
      (@fapp0 $K Cat_cat $E $X)
      (@fapp0 $K Cat_cat $E $Y)
      $Z
      (@Product_pair
        (Functor_cat (@fapp0 $K Cat_cat $E $X) (@fapp0 $K Cat_cat $E $Y))
        (Functor_cat (@fapp0 $K Cat_cat $E $Y) $Z)
        (@fapp1_fapp0 $K Cat_cat $E $X $Y $F)
        $G)
      (@Product_pair
        (Functor_cat (@fapp0 $K Cat_cat $E $X) (@fapp0 $K Cat_cat $E $Y))
        (Functor_cat (@fapp0 $K Cat_cat $E $Y) $Z)
        (@fapp1_fapp0 $K Cat_cat $E $X $Y $F)
        $H)
      (@Product_pair
        (Hom_cat
          (Functor_cat (@fapp0 $K Cat_cat $E $X) (@fapp0 $K Cat_cat $E $Y))
          (@fapp1_fapp0 $K Cat_cat $E $X $Y $F)
          (@fapp1_fapp0 $K Cat_cat $E $X $Y $F))
        (Hom_cat (Functor_cat (@fapp0 $K Cat_cat $E $Y) $Z) $G $H)
        (@id
          (Functor_cat (@fapp0 $K Cat_cat $E $X) (@fapp0 $K Cat_cat $E $Y))
          (@fapp1_fapp0 $K Cat_cat $E $X $Y $F))
        $eta);

// The old `comp_cat_con_transf` compatibility name has been removed; the Cat
// product-composition owner exposes its projections and identity collapse.

// Product-valued capped off-diagonal components project componentwise.
rule sigma_Fst (@tapp1_fapp0 $X (Product_cat $A $B) $F $G $i $j $eta $p)
  ↪ @tapp1_fapp0 $X $A (sigma_Fst $F) (sigma_Fst $G) $i $j (sigma_Fst $eta) $p;

// Right projection of product-valued capped off-diagonal action is pointwise.
rule sigma_Snd (@tapp1_fapp0 $X (Product_cat $A $B) $F $G $i $j $eta $p)
  ↪ @tapp1_fapp0 $X $B (sigma_Snd $F) (sigma_Snd $G) $i $j (sigma_Snd $eta) $p;

// Identity transfor capped off-diagonal action is ordinary functor action.
rule @tapp1_fapp0 $A $B $F $F $X $Y (@id (Functor_cat $A $B) $F) $p
  ↪ @fapp1_fapp0 $A $B $F $X $Y $p;

// Off-diagonal action at an identity base arrow is the ordinary component.
rule @tapp1_fapp0 $A $B $F $G $X $X $ϵ (@id $A $X)
  ↪ @tapp0_fapp0 $A $B $F $G $X $ϵ;

// Off-diagonal vertical-composite folds for ordinary transfors.
rule @comp_fapp0
      $B
      _
      _
      _
      (@tapp0_fapp0 $A $B $G $H $Y $η)
      (@tapp1_fapp0 $A $B $F $G $X $Y $ϵ $f)
  ↪ @tapp1_fapp0
      $A
      $B
      $F
      $H
      $X
      $Y
      (@comp_fapp0 (Functor_cat $A $B) $F $G $H $η $ϵ)
      $f;

// Vertical composition can also accumulate an off-diagonal component on the left.
rule @comp_fapp0
      $B
      _
      _
      _
      (@tapp1_fapp0 $A $B $G $H $X $Y $η $f)
      (@tapp0_fapp0 $A $B $F $G $X $ϵ)
  ↪ @tapp1_fapp0
      $A
      $B
      $F
      $H
      $X
      $Y
      (@comp_fapp0 (Functor_cat $A $B) $F $G $H $η $ϵ)
      $f;

// Two off-diagonal components compose by accumulating both base arrows.
rule @comp_fapp0
      $B
      _
      _
      _
      (@tapp1_fapp0 $A $B $G $H $Y $Z $η $q)
      (@tapp1_fapp0 $A $B $F $G $X $Y $ϵ $p)
  ↪ @tapp1_fapp0
      $A
      $B
      $F
      $H
      $X
      $Z
      (@comp_fapp0 (Functor_cat $A $B) $F $G $H $η $ϵ)
      (@comp_fapp0 $A $X $Y $Z $q $p);

// Pre-configured four-cell interchange for the Cat-valued representable
// `hom_` (postcomposition).
symbol hom_postcomp_representable_interchange_eq
  [B : Cat]
  [M N L : τ (Obj B)]
  [f g h : τ (Hom B N L)]
  (e_fg : τ (Hom (Hom_cat B N L) f g))
  (e_gh : τ (Hom (Hom_cat B N L) g h))
  [X Y Z : τ (Hom B M N)]
  (alpha : τ (Hom (Hom_cat B M N) X Y))
  (beta : τ (Hom (Hom_cat B M N) Y Z))
  : τ (
      @comp_fapp0
        (Hom_cat B M L)
        (@hom_postcomp_fapp0 B B (@id_func B) M N L f X)
        (@hom_postcomp_fapp0 B B (@id_func B) M N L g Y)
        (@hom_postcomp_fapp0 B B (@id_func B) M N L h Z)
        (@tapp1_fapp0
          (Hom_cat B M N)
          (Hom_cat B M L)
          (@hom_postcomp_func B B (@id_func B) M N L g)
          (@hom_postcomp_func B B (@id_func B) M N L h)
          Y
          Z
          (@hom_postcomp_tele_fapp1_fapp0 B B (@id_func B) M N L g h e_gh)
          beta)
        (@tapp1_fapp0
          (Hom_cat B M N)
          (Hom_cat B M L)
          (@hom_postcomp_func B B (@id_func B) M N L f)
          (@hom_postcomp_func B B (@id_func B) M N L g)
          X
          Y
          (@hom_postcomp_tele_fapp1_fapp0 B B (@id_func B) M N L f g e_fg)
          alpha)
      =
      @tapp1_fapp0
        (Hom_cat B M N)
        (Hom_cat B M L)
        (@hom_postcomp_func B B (@id_func B) M N L f)
        (@hom_postcomp_func B B (@id_func B) M N L h)
        X
        Z
        (@hom_postcomp_tele_fapp1_fapp0
          B
          B
          (@id_func B)
          M
          N
          L
          f
          h
          (@comp_fapp0 (Hom_cat B N L) f g h e_gh e_fg))
        (@comp_fapp0 (Hom_cat B M N) X Y Z beta alpha))
≔ eq_refl
    (@tapp1_fapp0
      (Hom_cat B M N)
      (Hom_cat B M L)
      (@hom_postcomp_func B B (@id_func B) M N L f)
      (@hom_postcomp_func B B (@id_func B) M N L h)
      X
      Z
      (@hom_postcomp_tele_fapp1_fapp0
        B
        B
        (@id_func B)
        M
        N
        L
        f
        h
        (@comp_fapp0 (Hom_cat B N L) f g h e_gh e_fg))
      (@comp_fapp0 (Hom_cat B M N) X Y Z beta alpha));

// 6d. Full ordinary naturality and projection-order joins

// Full strict naturality for ordinary transfors, oriented as cut elimination.
// The post/left rule accumulates a codomain arrow through the off-diagonal
// hom-action:
//   postcomp(G[g]) ∘ epsilon[X,Y] ↪ epsilon[X,Z] ∘ postcomp(g).
//
// The represented source endpoint of the postcomposition functor is kept as a
// pattern variable. Typing forces it to be F[X], but this lets the rule still
// match when F[X] has already reduced, as in representable postcomposition
// regressions.
rule @comp_fapp0
      Cat_cat
      _ _ _
      (@hom_postcomp_func $B $A $G $FX $Y $Z $g)
      (@tapp1_func $A $B $F $G $X $Y $ϵ)
  ↪ @comp_fapp0
      Cat_cat
      _ _ _
      (@tapp1_func $A $B $F $G $X $Z $ϵ)
      (@hom_postcomp_func $A $A (@id_func $A) $X $Y $Z $g);

// Full pre/right strict naturality:
//   precomp(F[h]) ∘ epsilon[X,Y] ↪ epsilon[W,Y] ∘ precomp(h).
//
// `hom_precomp_along_func` is the stable projection for the left functor. The
// raw semantic owner over opposites folds to this head above, so the
// accumulation rule does not need to expose `hom_`/`Op_func` internals.
rule @comp_fapp0
      Cat_cat
      _ _ _
      (@hom_precomp_along_func $A $B $F (@fapp0 $A $B $G $Y) $W $X $h)
      (@tapp1_func $A $B $F $G $X $Y $ϵ)
  ↪ @comp_fapp0
      Cat_cat
      _ _ _
      (@tapp1_func $A $B $F $G $W $Y $ϵ)
      (@hom_precomp_along_func $A $A (@id_func $A) $Y $W $X $h);

// Full strict functoriality for ordinary functors. These are first-class
// single-functor accumulation rules; they are distinct from the later rule for
// the hom-action of a composite functor F ∘ G.
rule @comp_fapp0
      Cat_cat
      _ _ _
      (@hom_postcomp_func $B $A $F $FX $Y $Z $g)
      (@fapp1_func $A $B $F $X $Y)
  ↪ @comp_fapp0
      Cat_cat
      _ _ _
      (@fapp1_func $A $B $F $X $Z)
      (@hom_postcomp_func $A $A (@id_func $A) $X $Y $Z $g);

// Contravariant form of full strict functoriality accumulation.
rule @comp_fapp0
      Cat_cat
      _ _ _
      (@hom_precomp_along_func $A $B $F (@fapp0 $A $B $F $Y) $W $X $h)
      (@fapp1_func $A $B $F $X $Y)
  ↪ @comp_fapp0
      Cat_cat
      _ _ _
      (@fapp1_func $A $B $F $W $Y)
      (@hom_precomp_along_func $A $A (@id_func $A) $Y $W $X $h);

// Strict naturality for off-diagonal ordinary transfor components, oriented as
// cut elimination.
//
// Surface/formula:
//   G[g] ∘ epsilon[f] ↪ epsilon[g ∘ f]
//   epsilon[f] ∘ F[g] ↪ epsilon[f ∘ g].
rule comp_fapp0
      (@fapp1_fapp0 $A $B $G $Y $Z $g)
      (@tapp1_fapp0 $A $B $F $G $X $Y $ϵ $f)
  ↪ tapp1_fapp0 $ϵ (comp_fapp0 $g $f);

// Precomposition-side strict naturality for off-diagonal components.
rule comp_fapp0
      (@tapp1_fapp0 $A $B $F $G $X $Y $ϵ $f)
      (@fapp1_fapp0 $A $B $F $X0 $X $g)
  ↪ tapp1_fapp0 $ϵ (comp_fapp0 $f $g);

// Cat-valued object-level projections of strict naturality. Both composites
// fold to the off-diagonal component at the base arrow.
//
// Surface/formula:
//   D[p](eta[x](u)) ↪ eta[p](u)
//   eta[y](E[p](u)) ↪ eta[p](u).
//
// Keep the outer `fapp0` source/target categories implicit. The explicit
// arguments below are the stable ordinary action/component heads themselves,
// not reducible fibre-category expressions.
rule fapp0
      (@fapp1_fapp0 $K Cat_cat $D $x $y $p)
      (fapp0 (@tapp0_fapp0 $K Cat_cat $E $D $x $eta) $u)
  ↪ fapp0 (@tapp1_fapp0 $K Cat_cat $E $D $x $y $eta $p) $u;

// Target-component route of Cat-valued naturality joins the same off-diagonal action.
rule fapp0
      (@tapp0_fapp0 $K Cat_cat $E $D $y $eta)
      (fapp0 (@fapp1_fapp0 $K Cat_cat $E $x $y $p) $u)
  ↪ fapp0 (@tapp1_fapp0 $K Cat_cat $E $D $x $y $eta $p) $u;

// -------------------------------------------------------------------------------------------------
// 7. Product functor packages, evaluation, curry, and ordinary internal action
// -------------------------------------------------------------------------------------------------

// 7a. Internalized product formation and product maps
/*
  Internalized product formation in Cat.

  Mathematical notation:
    Product_cat_func[A][B] = A × B
    Product_cat_fapp0_func(A)[B] = A × B

    Product_cat_fapp1_func(A,A')[G]
      = Product_cat_fapp1_fapp0_functord(G)
      : Product_cat_func[A] => Product_cat_func[A']

    Product_cat_fapp1_tapp0_func(G,B)
      = G * 1_B : A × B ⊢ A' × B

    (G * 1_B)[(x,y)] = (G[x],y)
    (G * 1_B)[(p,q)] = (G[p],q)

  Canonical comment syntax:
    A × B
    G * 1_B

  `Product_cat_fapp1_tapp0_func` is the stable fixed-right projection of the
  arrow-action of `Product_cat_func`. `Product_mapL_func_func` is only the
  defined functorial package G |-> G * 1_B.
*/
// Internalized binary product constructor.
//
// Surface/formula:
//   Product_cat_func[A][B] = A × B.
constant symbol Product_cat_func
  : τ (Functor Cat_cat (Functor_cat Cat_cat Cat_cat));

// Partial product constructor at fixed left factor A.
//
// Surface/formula:
//   Product_cat_fapp0_func(A)[B] = A × B.
injective symbol Product_cat_fapp0_func (A : Cat)
  : τ (Functor Cat_cat Cat_cat);

// Object projection ladder for the internalized product constructor.
rule @fapp0 _ _ Product_cat_func $A
  ↪ @Product_cat_fapp0_func $A;

// Second object projection: Product_cat_fapp0_func(A)[B] ↪ A × B.
rule @fapp0 Cat_cat Cat_cat (@Product_cat_fapp0_func $A) $B
  ↪ Product_cat $A $B;

// Hom-action of product formation in the left factor.
//
// Surface/formula:
//   Product_cat_fapp1_func(A,A')[G] : (A × -) => (A' × -).
symbol Product_cat_fapp1_func [A A' : Cat]
  : τ (Functor
      (Functor_cat A A')
      (Functord_cat
        (Product_cat_fapp0_func A)
        (Product_cat_fapp0_func A')));

// Capped hom-action of product formation at G.
//
// Surface/formula:
//   Product_cat_fapp1_fapp0_functord(G) = Product_cat_func[G].
symbol Product_cat_fapp1_fapp0_functord [A A' : Cat]
  (G : τ (Functor A A'))
  : τ (Functord
      (Product_cat_fapp0_func A)
      (Product_cat_fapp0_func A'));

// Component of the product hom-action at a fixed right factor B.
//
// Surface/formula:
//   Product_cat_fapp1_tapp0_func(G,B) = G * 1_B.
symbol Product_cat_fapp1_tapp0_func [A A' B : Cat]
  (G : τ (Functor A A'))
  : τ (Functor (Product_cat A B) (Product_cat A' B));

// Functor-level and capped projections of product formation hom-action.
rule @fapp1_func _ _ Product_cat_func $A $A'
  ↪ Product_cat_fapp1_func;

// Capped left-factor action: Product_cat_fapp1_func(A,A')[G].
rule fapp0 (@Product_cat_fapp1_func $A $A') $G
  ↪ Product_cat_fapp1_fapp0_functord $G;

// Direct capped projection of the same left-factor hom-action at G.
rule @fapp1_fapp0 _ _ Product_cat_func $A $A' $G
  ↪ Product_cat_fapp1_fapp0_functord $G;

// Component projection of `G * 1_B` from the displayed product hom-action.
rule @tapp0_fapp0
      Cat_cat
      Cat_cat
      _
      _
      $B
      (@Product_cat_fapp1_fapp0_functord $A $A' $G)
  ↪ Product_cat_fapp1_tapp0_func $G;

// Projection rules for the fixed-right product map.
//
// Surface/formula:
//   π₁ ∘ (G * 1_B) = G ∘ π₁
//   π₂ ∘ (G * 1_B) = π₂.
// First projection: π₁ ∘ (G * 1_B) ↪ G ∘ π₁.
rule sigma_Fst (@Product_cat_fapp1_tapp0_func $A $A' $B $G)
  ↪ comp_cat_fapp0 $G Product_projL_func;

// Second projection: π₂ ∘ (G * 1_B) ↪ π₂.
rule sigma_Snd (@Product_cat_fapp1_tapp0_func $A $A' $B $G)
  ↪ Product_projR_func;

// Object action of the fixed-right product map.
//
// Surface/formula:
//   (G * 1_B)[(x,y)] = (G[x],y).
rule @fapp0 _ _ (@Product_cat_fapp1_tapp0_func $A $A' $B $G) (Struct_sigma $x $y)
  ↪ Struct_sigma
      (fapp0 $G $x)
      $y;

// Full hom-action of the fixed-right product map.
//
// Surface/formula:
//   (G * 1_B)_1 = G_1 × 1.
// lhs-audit: keep 4 -- pair endpoint is decomposed by the rule
rule @fapp1_func _ _ (@Product_cat_fapp1_tapp0_func $A $A' $B $G)
      (Struct_sigma $x $y)
      (Struct_sigma $x' $y')
  ↪ Struct_sigma
      (@comp_cat_fapp0
        (Product_cat
          (Hom_cat $A $x $x')
          (Hom_cat $B $y $y'))
        (Hom_cat $A $x $x')
        (Hom_cat $A'
          (@fapp0 $A $A' $G $x)
          (@fapp0 $A $A' $G $x'))
        (@fapp1_func $A $A' $G $x $x')
        (@Product_projL_func
          (Hom_cat $A $x $x')
          (Hom_cat $B $y $y')))
      (@Product_projR_func
        (Hom_cat $A $x $x')
        (Hom_cat $B $y $y'));

// Capped arrow action of the fixed-right product map.
//
// Surface/formula:
//   (G * 1_B)[(p,q)] = (G[p],q).
// lhs-audit: keep 4 -- pair endpoint is decomposed by the rule
rule @fapp1_fapp0 _ _ (@Product_cat_fapp1_tapp0_func $A $A' $B $G)
      (Struct_sigma $x $y)
      (Struct_sigma $x' $y')
      (Struct_sigma $p $q)
  ↪ Struct_sigma
      (fapp1_fapp0 $G $p)
      $q;

// Defined functorial package for the fixed-right product action.
//
// Mathematical notation:
//   Product_mapL_func_func(A,A',B)[G] = G * 1_B.
//
// This is a readability alias through the `Product_cat_func` projection
// ladder, not an independent stable-head theory.
symbol Product_mapL_func_func [A A' B : Cat]
  : τ (Functor
      (Functor_cat A A')
      (Functor_cat (Product_cat A B) (Product_cat A' B)))
≔ @comp_cat_fapp0
    (Functor_cat A A')
    (@Functord_cat Cat_cat
      (@Product_cat_fapp0_func A)
      (@Product_cat_fapp0_func A'))
    (Functor_cat (Product_cat A B) (Product_cat A' B))
    (@tapp0_func
      Cat_cat
      Cat_cat
      (@Product_cat_fapp0_func A)
      (@Product_cat_fapp0_func A')
      B)
    (@Product_cat_fapp1_func A A');

// General two-sided product map.
//
// Surface/formula:
//   Product_map_func(F,G)[(a,b)] = (F[a],G[b])
//   Product_map_func(F,G)[(p,q)] = (F[p],G[q]).
//
// Stable two-sided product-map constructor. Its projections retain the
// componentwise semantics without unfolding to a pair of composite functors.
injective symbol Product_map_func [A A' B B' : Cat]
  (F : τ (Functor A A'))
  (G : τ (Functor B B'))
  : τ (Functor (Product_cat A B) (Product_cat A' B'));

// First projection of F × G: π₁ ∘ (F × G) ↪ F ∘ π₁.
rule sigma_Fst (@Product_map_func $A $A' $B $B' $F $G)
  ↪ @comp_cat_fapp0
      (Product_cat $A $B)
      $A
      $A'
      $F
      (@Product_projL_func $A $B);

// Second projection of F × G: π₂ ∘ (F × G) ↪ G ∘ π₂.
rule sigma_Snd (@Product_map_func $A $A' $B $B' $F $G)
  ↪ @comp_cat_fapp0
      (Product_cat $A $B)
      $B
      $B'
      $G
      (@Product_projR_func $A $B);

// Object action is componentwise: (F × G)[(a,b)] ↪ (F[a],G[b]).
rule @fapp0 _ _
      (@Product_map_func $A $A' $B $B' $F $G)
      $ab
  ↪ @Product_pair
      $A'
      $B'
      (@fapp0 $A $A' $F (sigma_Fst $ab))
      (@fapp0 $B $B' $G (sigma_Snd $ab));

// Hom-functor action is the product of the hom-actions of F and G.
rule @fapp1_func _ _
      (@Product_map_func $A $A' $B $B' $F $G)
      $ab
      $ab'
  ↪ @Product_map_func
      (Hom_cat $A (sigma_Fst $ab) (sigma_Fst $ab'))
      (Hom_cat $A'
        (@fapp0 $A $A' $F (sigma_Fst $ab))
        (@fapp0 $A $A' $F (sigma_Fst $ab')))
      (Hom_cat $B (sigma_Snd $ab) (sigma_Snd $ab'))
      (Hom_cat $B'
        (@fapp0 $B $B' $G (sigma_Snd $ab))
        (@fapp0 $B $B' $G (sigma_Snd $ab')))
      (@fapp1_func $A $A' $F (sigma_Fst $ab) (sigma_Fst $ab'))
      (@fapp1_func $B $B' $G (sigma_Snd $ab) (sigma_Snd $ab'));

// Capped arrow action is componentwise: (F × G)[(p,q)] ↪ (F[p],G[q]).
rule @fapp1_fapp0 _ _
      (@Product_map_func $A $A' $B $B' $F $G)
      $ab
      $ab'
      $pq
  ↪ @Product_pair
      (Hom_cat $A'
        (@fapp0 $A $A' $F (sigma_Fst $ab))
        (@fapp0 $A $A' $F (sigma_Fst $ab')))
      (Hom_cat $B'
        (@fapp0 $B $B' $G (sigma_Snd $ab))
        (@fapp0 $B $B' $G (sigma_Snd $ab')))
      (@fapp1_fapp0
        $A $A' $F
        (sigma_Fst $ab) (sigma_Fst $ab')
        (sigma_Fst $pq))
      (@fapp1_fapp0
        $B $B' $G
        (sigma_Snd $ab) (sigma_Snd $ab')
        (sigma_Snd $pq));

// Narrow product projection for two Cat-valued family actions over the same
// base arrow:
//   (B[p] * 1)[C[p]] = B[p] × C[p].
//
// Sharing the literal base arrow is the discriminator. The unrestricted
// off-diagonal projection and its higher naturality closure remain separate.
rule @tapp1_fapp0
      Cat_cat
      Cat_cat
      _
      _
      _
      _
      (@Product_cat_fapp1_fapp0_functord
        _
        _
        (@fapp1_fapp0 $K Cat_cat $B $x $y $p))
      (@fapp1_fapp0 $K Cat_cat $C $x $y $p)
  ↪ @Product_map_func
      (@fapp0 $K Cat_cat $B $x)
      (@fapp0 $K Cat_cat $B $y)
      (@fapp0 $K Cat_cat $C $x)
      (@fapp0 $K Cat_cat $C $y)
      (@fapp1_fapp0 $K Cat_cat $B $x $y $p)
      (@fapp1_fapp0 $K Cat_cat $C $x $y $p);

// Product/one-slot factorizations of the primitive Hom action are proof-time
// comparisons. Runtime preserves the factored cuts and the rigid Unit_prof
// projection as distinct normal forms.
unif_rule @Hom_tele_func $A $x $x' $y $y'
  ≡ @comp_fapp0
      Cat_cat
      _ _ _
      (@comp_prod_func
        Cat_cat
        (Hom_cat $A $x $y)
        (Hom_cat $A $x' $y)
        (Hom_cat $A $x' $y'))
      (@Product_map_func
        (Hom_cat $A $x' $x)
        (Functor_cat
          (Hom_cat $A $x $y)
          (Hom_cat $A $x' $y))
        (Hom_cat $A $y $y')
        (Functor_cat
          (Hom_cat $A $x' $y)
          (Hom_cat $A $x' $y'))
        (@hom_precomp_along_tele_func
          $A $A (@id Cat_cat $A)
          $y
          $x'
          $x)
        (@hom_postcomp_tele_func
          $A $A (@id Cat_cat $A)
          $x'
          $y
          $y'))
  ↪ [ tt ≡ tt ];

// Proof-time comparison: Hom(g,f) equals precomposition followed by postcomposition.
unif_rule @Hom_func $A $x $x' $y $y' $g $f
  ≡ @comp_fapp0
      Cat_cat
      _ _ _
      (@hom_postcomp_func $A $A (@id Cat_cat $A) $x' $y $y' $f)
      (@hom_precomp_along_func $A $A (@id Cat_cat $A) $y $x' $x $g)
  ↪ [ tt ≡ tt ];

// Proof-time comparison: Hom(g,f) also equals postcomposition followed by precomposition.
unif_rule @Hom_func $A $x $x' $y $y' $g $f
  ≡ @comp_fapp0
      Cat_cat
      _ _ _
      (@hom_precomp_along_func $A $A (@id Cat_cat $A) $y' $x' $x $g)
      (@hom_postcomp_func $A $A (@id Cat_cat $A) $x $y $y' $f)
  ↪ [ tt ≡ tt ];

// 7b. Evaluation and fixed-object evaluation
/*
  Product evaluation: apply a functor to an object.

  Mathematical notation:
    Eval_func(A,B) : (A ⊢ B) × A ⊢ B
    Eval_func(A,B)[(F,x)] = F[x]

    Eval_fapp1_func(A,B,F,G,x,y)
      : (F => G) × Hom_A(x,y) ⊢ Hom_B(F[x],G[y])
    Eval_fapp1_func(A,B,F,G,x,y)[(eta,p)] = eta[p]

  Canonical comment syntax:
    F[x]
    eta[p]
*/
// Product evaluation functor.
//
// Surface/formula:
//   Eval_func(A,B)[(F,x)] = F[x].
symbol Eval_func [A B : Cat]
  : τ (Functor (Product_cat (Functor_cat A B) A) B);

// Object action of product evaluation.
rule fapp0 (@Eval_func $A $B) (Struct_sigma $F $x)
  ↪ fapp0 $F $x;

// Hom-action of product evaluation.
//
// Surface/formula:
//   Eval_fapp1_func[(eta,p)] = eta[p].
symbol Eval_fapp1_func [A B : Cat]
  [F G : τ (Functor A B)]
  [x y : τ (Obj A)]
  : τ (Functor
      (Product_cat (Transf_cat F G) (Hom_cat A x y))
      (Hom_cat B (fapp0 F x) (fapp0 G y)));

// Full hom-action of evaluation exposes the off-diagonal transfor component.
rule @fapp1_func _ _ (@Eval_func $A $B) (Struct_sigma $F $x) (Struct_sigma $G $y)
  ↪ Eval_fapp1_func;

// Capped hom-action of evaluation.
rule fapp0 (@Eval_fapp1_func $A $B $F $G $x $y) (Struct_sigma $eta $p)
  ↪ tapp1_fapp0 $eta $p;

// Direct capped evaluation: Eval[(eta,p)] ↪ eta[p].
rule @fapp1_fapp0 _ _ (@Eval_func $A $B)
      (Struct_sigma $F $x)
      (Struct_sigma $G $y)
      (Struct_sigma $eta $p)
  ↪ tapp1_fapp0 $eta $p;

/*
  Fixed-point section for evaluation.

  Mathematical notation:
    Eval_at_func(A,B,x) : (A ⊢ B) ⊢ (A ⊢ B) × A
    Eval_at_func(A,B,x)[F] = (F,x)
    Eval_func(A,B) ∘ Eval_at_func(A,B,x) = fapp0_func(A,B,x)

  Canonical comment syntax:
    F |-> (F,x)
*/
// Pair a functor with the fixed object x for evaluation.
//
// Surface/formula:
//   Eval_at_func(x)[F] = (F,x).
symbol Eval_at_func [A B : Cat] (x : τ (Obj A))
  : τ (Functor
      (Functor_cat A B)
      (Product_cat (Functor_cat A B) A));

// Projections of the fixed-point evaluation section.
rule sigma_Fst (@Eval_at_func $A $B $x)
  ↪ @id_func (Functor_cat $A $B);

// Fixed-object projection: π₂ ∘ Eval_at(x) ↪ const(x).
rule sigma_Snd (@Eval_at_func $A $B $x)
  ↪ Const_func $x;

// Object action of `Eval_at_func`.
rule @fapp0 _ _
      (@Eval_at_func $A $B $x) $F
  ↪ Struct_sigma $F $x;

// Hom-action of `Eval_at_func`: keep eta and the identity at x.
rule @fapp1_func _ _
      (@Eval_at_func $A $B $x) $F $G
  ↪ Struct_sigma
      (@id_func (@Transf_cat $A $B $F $G))
      (@Const_func
        (@Transf_cat $A $B $F $G)
        (Hom_cat $A $x $x)
        (@id $A $x));

// Arrow action pairs eta with id_x: Eval_at(x)[eta] ↪ (eta,id_x).
rule @fapp1_fapp0 _ _
      (@Eval_at_func $A $B $x) $F $G $eta
  ↪ Struct_sigma $eta (id $A $x);

// Evaluation at the fixed-point section folds to ordinary object evaluation.
//
// Surface/formula:
//   Eval_func ∘ Eval_at_func(x) = fapp0_func(x).
rule @comp_fapp0
      Cat_cat
      _
      _
      $B
      (@Eval_func $A $B)
      (@Eval_at_func $A $B $x)
  ↪ fapp0_func $x;

// 7c. Ordinary curry and uncurry
/*
  Ordinary product curry/uncurry scaffold.

  Mathematical notation:
    curry_func_func(A,B,C)[F] = curry(F)
    curry(F)[x][y] = F[(x,y)]

    uncurry_func_func(A,B,C)[G] = uncurry(G)
    uncurry(G)[(x,y)] = G[x][y]
    uncurry(G)[(p,q)] = G[p][q]

  Canonical comment syntax:
    curry F
    uncurry G

  `curry_func_func` and `uncurry_func_func` are the primary semantic packages.
  `curry_func`, `curry_fapp0_func`, and `uncurry_func` are definitional
  projections. Full product/curry adjunction coherence remains future work.
*/
// Semantic curry package through the product-pair telescope.
//
// Surface/formula:
//   curry_func_func[F][x][y] = F[(x,y)].
symbol curry_func_func [A B C : Cat]
  : τ (Functor
      (Functor_cat (Product_cat A B) C)
      (Functor_cat A (Functor_cat B C)))
≔ @comp_cat_fapp0
    (Functor_cat (Product_cat A B) C)
    (Functor_cat (Functor_cat B (Product_cat A B)) (Functor_cat B C))
    (Functor_cat A (Functor_cat B C))
    (@comp_cat_con_func
      A
      (Functor_cat B (Product_cat A B))
      (Functor_cat B C)
      (@Product_pair_tele_func A B))
    (@comp_cat_cov_func_func B (Product_cat A B) C);

// Object action of semantic curry.
//
// Surface/formula:
//   curry_func(F) = curry(F).
symbol curry_func [A B C : Cat]
  (F : τ (Functor (Product_cat A B) C))
  : τ (Functor A (Functor_cat B C))
≔ fapp0 curry_func_func F;

// Curry evaluated at x.
//
// Surface/formula:
//   curry_fapp0_func(F,x)[y] = F[(x,y)].
symbol curry_fapp0_func [A B C : Cat]
  (F : τ (Functor (Product_cat A B) C))
  (x : τ (Obj A))
  : τ (Functor B C)
≔ fapp0 (curry_func F) x;

// Semantic uncurry package through fixed-right product action and evaluation.
//
// Surface/formula:
//   uncurry_func_func[G][(x,y)] = G[x][y].
symbol uncurry_func_func [A B C : Cat]
  : τ (Functor
      (Functor_cat A (Functor_cat B C))
      (Functor_cat (Product_cat A B) C))
≔ @comp_cat_fapp0
    (Functor_cat A (Functor_cat B C))
    (Functor_cat
      (Product_cat A B)
      (Product_cat (Functor_cat B C) B))
    (Functor_cat (Product_cat A B) C)
    (@comp_cat_cov_func
      (Product_cat A B)
      (Product_cat (Functor_cat B C) B)
      C
      (@Eval_func B C))
    (@Product_mapL_func_func A (Functor_cat B C) B);

// Object action of semantic uncurry.
//
// Surface/formula:
//   uncurry_func(G) = uncurry(G).
symbol uncurry_func [A B C : Cat]
  (G : τ (Functor A (Functor_cat B C)))
  : τ (Functor (Product_cat A B) C)
≔ fapp0 uncurry_func_func G;

// The transfor action of semantic uncurry depends on the higher arrow-action
// of `Product_cat_func` on a transfor `theta`. Keep it deferred rather than
// reinstating an independent `Product_mapL_transf` stable package.

// 7d. Adjunctions and opposite adjunctions
/*
  Indexed ordinary functor adjunctions.

  The already-named functors are indices of the relation:

    J : Adjunction(F,G)
    F : R ⊢ L
    G : L ⊢ R
    unit_adj_transf(J)   : id_R => G ∘ F
    counit_adj_transf(J) : F ∘ G => id_L.

  `left_adj_func` and `right_adj_func` remain transparent compatibility views
  only; semantic consumers use `F` and `G` directly. The unit/counit are stable
  opaque observations because their application heads are the rigid runtime
  discriminators for triangle cut-elimination. Independently named operations
  receive no runtime beta or proof-time equation without declaration-backed
  agreement evidence.
*/
// Indexed relation asserting that F is left adjoint to G.
injective symbol Adjunction
  [R L : Cat]
  (F : τ (Functor R L))
  (G : τ (Functor L R))
  : Grpd;

// Transparent compatibility view of the indexed left adjoint.
//
// Surface/formula:
//   left_adj_func(J) ≔ F : R ⊢ L.
symbol left_adj_func
  [R L : Cat]
  [F : τ (Functor R L)]
  [G : τ (Functor L R)]
  (_ : τ (@Adjunction R L F G))
  : τ (Functor R L)
≔ F;

// Transparent compatibility view of the indexed right adjoint.
//
// Surface/formula:
//   right_adj_func(J) ≔ G : L ⊢ R.
symbol right_adj_func
  [R L : Cat]
  [F : τ (Functor R L)]
  [G : τ (Functor L R)]
  (_ : τ (@Adjunction R L F G))
  : τ (Functor L R)
≔ G;

// Unit of the adjunction.
//
// Surface/formula:
//   unit_adj_transf(J) : id_R => G ∘ F.
symbol unit_adj_transf
  [R L : Cat]
  [F : τ (Functor R L)]
  [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G))
  : τ (Transf
      (@id_func R)
      (@comp_cat_fapp0 R L R G F));

// Counit of the adjunction.
//
// Surface/formula:
//   counit_adj_transf(J) : F ∘ G => id_L.
symbol counit_adj_transf
  [R L : Cat]
  [F : τ (Functor R L)]
  [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G))
  : τ (Transf
      (@comp_cat_fapp0 L R L F G)
      (@id_func L));

// Left triangle cut-elimination.
//
// Surface/formula:
//   counit[f] ∘ left(unit[g]) ↪ f ∘ left(g)
//
// for g : X ->^R X' and f : left(X') ->^L Y.
rule comp_fapp0
      (@tapp1_fapp0 _ _
        _
        _
        (fapp0 $F $X')
        $Y
        (@counit_adj_transf $R $L $F $G $J)
        $f)
      (fapp1_fapp0 $F
        (@tapp1_fapp0 _ _ _ _
          $X
          $X'
          (@unit_adj_transf $R $L $F $G $J)
          $g))
  ↪ comp_fapp0
      $f
      (fapp1_fapp0 $F $g);

// Right triangle cut-elimination.
//
// Surface/formula:
//   right(counit[g]) ∘ unit[f] ↪ right(g) ∘ f
//
// for f : X ->^R right(Y') and g : Y' ->^L Y.
rule comp_fapp0
      (fapp1_fapp0 $G
        (@tapp1_fapp0 _ _ _ _
          $Y'
          $Y
          (@counit_adj_transf $R $L $F $G $J)
          $g))
      (@tapp1_fapp0 _ _
        _
        _
        $X
        (fapp0 $G $Y')
        (@unit_adj_transf $R $L $F $G $J)
        $f)
  ↪ comp_fapp0
      (fapp1_fapp0 $G $g)
      $f;

/*
  Opposite adjunction.

  An adjunction A <-> B dualizes to B^op <-> A^op. The old right adjoint
  becomes the new left adjoint, and the original counit/unit become the dual
  unit/counit through `Op_transf`.
*/
injective symbol Op_adjunction
  [A B : Cat]
  [F : τ (Functor A B)]
  [G : τ (Functor B A)]
  (adj : τ (@Adjunction A B F G))
  : τ (@Adjunction
      (Op_cat B)
      (Op_cat A)
      (@Op_func B A G)
      (@Op_func A B F));

// Opposite is involutive on adjunction packages: (J^op)^op ↪ J.
rule @Op_adjunction
      (Op_cat $B) (Op_cat $A)
      _
      _
      (@Op_adjunction $A $B _ _ $adj)
  ↪ $adj;

// The transparent functor views of J^op compute from its opposite indices.

// The unit of J^op is the opposite of the counit of J.
rule @unit_adj_transf
      (Op_cat $B) (Op_cat $A)
      _
      _
      (@Op_adjunction $A $B $F $G $adj)
  ↪ @Op_transf
      $B $B
      (@comp_cat_fapp0 $B $A $B $F $G)
      (@id_func $B)
      (@counit_adj_transf $A $B $F $G $adj);

// The counit of J^op is the opposite of the unit of J.
rule @counit_adj_transf
      (Op_cat $B) (Op_cat $A)
      _
      _
      (@Op_adjunction $A $B $F $G $adj)
  ↪ @Op_transf
      $A $A
      (@id_func $A)
      (@comp_cat_fapp0 $A $B $A $G $F)
      (@unit_adj_transf $A $B $F $G $adj);

// 7e. Internal ordinary hom-action packages
/*
  More-internal ordinary hom-action.

  This ports the settled v2 core without also committing to the later
  hom-action packaging heads.  The functor sends a transfor ϵ : F => G to the
  internalized action

    hom_int(id_A) => hom_int(G) ∘ F^op.

  Surface/formula:
    tapp1_int_func_transf(F,G)[ϵ]
      : Hom_A(~,—) => Hom_B(F^op ~,G —)

    fapp1_int_transf(F)
      = tapp1_int_func_transf(F,F)[id_F]
*/
// Internal off-diagonal ordinary hom-action package.
//
// Surface/formula:
//   tapp1_int_func_transf(F,G)[epsilon]
//     : hom_int(id_A) => hom_int(G) ∘ F^op.
symbol tapp1_int_func_transf : Π [A B : Cat], Π [F G : τ (Functor A B)],
  τ (Functor
      (Transf_cat F G)
      (Transf_cat
        (@hom_int A A (@id_func A))
        (comp_cat_fapp0
          (@hom_int B A G)
          (@Op_func A B F))));

// Object action of `tapp1_int_func_transf`.
//
// Surface/formula:
//   tapp1_int_fapp0_transf(epsilon)
//     = tapp1_int_func_transf(F,G)[epsilon].
symbol tapp1_int_fapp0_transf : Π [A B : Cat], Π [F G : τ (Functor A B)],
  Π (ϵ : τ (Transf F G)),
  τ (Transf
      (@hom_int A A (@id_func A))
      (comp_cat_fapp0
        (@hom_int B A G)
        (@Op_func A B F)));

// Object-action projection for internal ordinary hom-action.
rule fapp0 (@tapp1_int_func_transf $A $B $F $G) $ϵ
  ↪ @tapp1_int_fapp0_transf $A $B $F $G $ϵ;

// Hom action of `tapp1_int_func_transf`.
//
// Surface/formula:
//   tapp1_int_fapp1_func_transf(epsilon,epsilon')
//     : Hom(epsilon,epsilon') ⊢ Hom(tapp1_int(epsilon),tapp1_int(epsilon')).
symbol tapp1_int_fapp1_func_transf : Π [A B : Cat], Π [F G : τ (Functor A B)],
  Π (ϵ ϵ' : τ (Transf F G)),
  τ (Functor
      (Hom_cat (Transf_cat F G) ϵ ϵ')
      (Hom_cat
        (Transf_cat
          (@hom_int A A (@id_func A))
          (comp_cat_fapp0
            (@hom_int B A G)
            (@Op_func A B F)))
        (@tapp1_int_fapp0_transf A B F G ϵ)
        (@tapp1_int_fapp0_transf A B F G ϵ')));

// Hom-action projection for internal ordinary hom-action.
rule @fapp1_func _ _ (@tapp1_int_func_transf $A $B $F $G) $ϵ $ϵ'
  ↪ @tapp1_int_fapp1_func_transf $A $B $F $G $ϵ $ϵ';

// Identity-specialized ordinary internal hom-action.
//
// Surface/formula:
//   fapp1_int_transf(F) = tapp1_int_func_transf(F,F)[id_F].
symbol fapp1_int_transf : Π [A B : Cat], Π (F : τ (Functor A B)),
  τ (Transf
      (@hom_int A A (@id_func A))
      (comp_cat_fapp0
        (@hom_int B A F)
        (@Op_func A B F)));

// Identity transfor specializes the off-diagonal action to functor hom-action.
rule @tapp1_int_fapp0_transf $A $B $F $F (id (Functor_cat $A $B) $F)
  ↪ @fapp1_int_transf $A $B $F;

// First projection of the identity-specialized ordinary internal hom-action at
// a fixed source object. This is the identity-specialized counterpart of
// `tapp1_at_transf`.
//
// Surface/formula:
//   fapp1_at_transf(F,X) : Hom_A(X,-) => Hom_B(F[X],F[-]).
symbol fapp1_at_transf : Π [A B : Cat], Π (F : τ (Functor A B)),
  Π (X : τ (Obj A)),
  τ (Transf
      (@hom_ A A (@id_func A) X)
      (@hom_ B A F (@fapp0 A B F X)));

// First projection fold for identity-specialized internal hom-action.
rule @tapp0_fapp0
      _
      _
      _
      _
      $X
      (@fapp1_int_transf $A $B $F)
  ↪ @fapp1_at_transf $A $B $F $X;

// First projection of the internal off-diagonal action at a fixed source
// object. This exposes the whole transfor
//   Hom_A(X,-) => Hom_B(F[X],G[-])
// before projecting again to the hom-functor component at Y.
//
// Surface/formula:
//   tapp1_at_transf(epsilon,X) : Hom_A(X,-) => Hom_B(F[X],G[-]).
symbol tapp1_at_transf : Π [A B : Cat], Π [F G : τ (Functor A B)],
  Π (X : τ (Obj A)),
  Π (ϵ : τ (Transf F G)),
  τ (Transf
      (@hom_ A A (@id_func A) X)
      (@hom_ B A G (@fapp0 A B F X)));

// First projection fold for off-diagonal internal hom-action.
rule @tapp0_fapp0
      _
      _
      _
      _
      $X
      (@tapp1_int_fapp0_transf $A $B $F $G $ϵ)
  ↪ @tapp1_at_transf $A $B $F $G $X $ϵ;

// Identity transfor folds the off-diagonal fixed-source action to fapp1.
rule @tapp1_at_transf $A $B $F $F $X (id (Functor_cat $A $B) $F)
  ↪ @fapp1_at_transf $A $B $F $X;

// Second projection of off-diagonal internal hom-action.
//
// Surface/formula:
//   tapp1_at_transf(epsilon,X)[Y] = tapp1_func(epsilon,X,Y).
rule @tapp0_fapp0
      $A
      Cat_cat
      _
      _
      $Y
      (@tapp1_at_transf $A $B $F $G $X $ϵ)
  ↪ @tapp1_func $A $B $F $G $X $Y $ϵ;

// Second projection of identity-specialized internal hom-action.
//
// Surface/formula:
//   fapp1_at_transf(F,X)[Y] = fapp1_func(F,X,Y).
rule @tapp0_fapp0
      $A
      Cat_cat
      _
      _
      $Y
      (@fapp1_at_transf $A $B $F $X)
  ↪ @fapp1_func $A $B $F $X $Y;

/*
  Ordinary internal hom-action package.

  Surface/formula:
    tapp1_int_func_transf(F,G)[epsilon]
      = internal action Hom_A(~,-) => Hom_B(F^op ~, G -)
    fapp1_int_transf(F) is the identity-specialized action.
*/

// -------------------------------------------------------------------------------------------------
// 8. Directed Cat-valued family constructors
// -------------------------------------------------------------------------------------------------

/*
  Mathematical notation:
    E[k]                      = Fibre_cat E k
    F^*E                      = Pullback_catd E F
    F^*E[a]                   = E[F[a]]
    Const_catd(K,A)[k]        = A
    Terminal_catd(K)          = Const_catd(K,Terminal_cat)
    Op_catd(E)[k]             = E[k]^op
    Pi_cat(E)                 = Π k :^n K, E[k]
                                = k :^n K ; 1[k] ⊢ E[k]
    piapp0(s,k)               = s[k]
*/

// 8a. Fibre notation, pullback, and base-arrow transport

// Fixed-base notation: fibre of a directed family.
//
// Surface/formula:
//   E[k] = Fibre_cat(E,k)
symbol Fibre_cat [K : Cat] (E : τ (Catd K)) (k : τ (Obj K)) : Cat
≔ @fapp0 K Cat_cat E k;

// Fixed-base reindexing of a displayed Cat-valued family along a functor.
//
// Surface/formula:
//   F^*E : A ⊢ Cat
//   (F^*E)[a] = E[F[a]]
//
// This is the canonical Cat-valued precomposition head. A deliberately broad
// fold from every `comp_cat_fapp0(E,F)` was rejected: it interferes with
// unrelated Došen cuts whose codomain can instantiate to `Cat_cat`.
injective symbol Pullback_catd [A B : Cat]
  (E : τ (Catd B))
  (F : τ (Functor A B))
  : τ (Catd A);

// Fibre projection of reindexing: (F^*E)[a] ↪ E[F[a]].
rule @fapp0 _ Cat_cat (@Pullback_catd $A $B $E $F) $a
  ↪ @fapp0 $B Cat_cat $E (@fapp0 $A $B $F $a);

// Internalized-x prerequisite: generic base-arrow transport for displayed
// Cat-valued families.
//
// Surface/formula:
//   E[p] : E[x] ⊢ E[y]
//   catd_transport_func(E,p) = fapp1_fapp0(E,p)
symbol catd_transport_func [K : Cat] (E : τ (Catd K))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  : τ (Functor (Fibre_cat E x) (Fibre_cat E y))
≔ @fapp1_fapp0 K Cat_cat E x y p;


// Strict object transport, oriented as cut elimination.
//
// Surface/formula:
//   E[q](E[p](u)) ↪ E[q ∘ p](u).
//
// Keep the outer `fapp0` source/target categories implicit. The explicit
// arguments below are the stable functor-action heads themselves, not reducible
// fibre-category expressions.
rule fapp0
      (@fapp1_fapp0 $K Cat_cat $E $y $z $q)
      (fapp0 (@fapp1_fapp0 $K Cat_cat $E $x $y $p) $u)
  ↪ fapp0
      (@fapp1_fapp0
        $K
        Cat_cat
        $E
        $x
        $z
        (@comp_fapp0 $K $x $y $z $q $p))
      $u;

// Internalized-x prerequisite: functorial package for pullback/reindexing of
// directed families along a base functor.
//
// Surface/formula:
//   Pullback_catd_func(F) : (B ⊢ Cat) ⊢ (A ⊢ Cat)
//   Pullback_catd_func(F)[E] = F^*E
//
// This is the functor-level owner whose object projection is the stable
// `Pullback_catd` head. The existing `Catd_cat_func` arrow projection is the
// bounded semantic-to-stable bridge; no global `comp_cat_con_func` fold is
// installed.
injective symbol Pullback_catd_func [A B : Cat]
  (F : τ (Functor A B))
  : τ (Functor (Catd_cat B) (Catd_cat A));

// Object projection of the pullback package: Pullback_catd_func(F)[E] ↪ F^*E.
rule @fapp0 _ _
      (@Pullback_catd_func $A $B $F) $E
  ↪ @Pullback_catd $A $B $E $F;

/*
  Proof-time comparison with semantic precomposition.

  These unification rules let reflexive equality proofs and elaboration move
  between the generic composition presentation and the stable pullback heads
  without orienting every Cat-valued composition through Pullback_catd.
  The special outer-composition accumulation for an already-stable
  `Pullback_catd` head is a runtime cut below, after the pullback
  specializations have been declared.
*/
unif_rule
  @comp_fapp0 Cat_cat $A $B Cat_cat $E $F
  ≡ @Pullback_catd $A $B $E $F
  ↪ [ tt ≡ tt ];

unif_rule
  @hom_precomp_along_func Cat_cat Cat_cat (@id Cat_cat Cat_cat) Cat_cat $A $B $F
  ≡ @Pullback_catd_func $A $B $F
  ↪ [ tt ≡ tt ];

// Arrow action of the internalized Catd constructor. `Catd_cat_func` is a
// definition, so the rule matches the canonical unfolded composition head.
rule @fapp1_fapp0
      (Op_cat Cat_cat)
      Cat_cat
      (@comp_fapp0
        Cat_cat
        (Op_cat Cat_cat)
        (Functor_cat Cat_cat Cat_cat)
        Cat_cat
        (@fapp0_func Cat_cat Cat_cat Cat_cat)
        Functor_cat_func)
      $B
      $A
      $F
  ↪ @Pullback_catd_func $A $B $F;

// Pointwise projection for the hom-action of family pullback.
rule @tapp0_fapp0
      $A
      Cat_cat
      _
      _
      $a
      (@fapp1_fapp0
        (@Catd_cat $B)
        (@Catd_cat $A)
        (@Pullback_catd_func $A $B $F)
        $E
        $D
        $η)
  ↪ @tapp0_fapp0
      $B
      Cat_cat
      $E
      $D
      (@fapp0 $A $B $F $a)
      $η;

// 8b. Constant, terminal, opposite, and displayed composition
//
// Fixed-base layer: constant Cat-valued family.
//
// Surface/formula:
//   const_K(A)[k] = A.
injective symbol Const_catd (K : Cat) (A : Cat) : τ (Catd K);

// Proof-time terminal-to-constant object comparison in the ordinary transfor
// presentation. Runtime access uses the section/component projection ladder.
unif_rule
  Obj
    (@Transf_cat
      $K Cat_cat
      (@Const_catd $K Terminal_cat)
      (@Const_catd $K $A))
  ≡ Obj (Functor_cat $K' $A')
  ↪ [ $K ≡ $K'; $A ≡ $A' ];

// Direct proof-time terminal-to-constant object comparison in the displayed
// presentation; do not rely on transitivity through Transf/Functord.
unif_rule
  Obj
    (@Functord_cat
      $K
      (@Const_catd $K Terminal_cat)
      (@Const_catd $K $A))
  ≡ Obj (Functor_cat $K' $A')
  ↪ [ $K ≡ $K'; $A ≡ $A' ];

// Constant-family fibre: const_K(A)[k] ↪ A.
rule @fapp0 $K Cat_cat (@Const_catd $K $A) $_ ↪ $A;
// Reindexing a constant family by composition remains constant.
rule @comp_fapp0 Cat_cat $A $B Cat_cat (@Const_catd $B $C) $F
  ↪ @Const_catd $A $C;
// Stable pullback of a constant family: F^*const_B(C) ↪ const_A(C).
rule @Pullback_catd $A $B (@Const_catd $B $C) $F
  ↪ @Const_catd $A $C;
// Pullback along a constant base map selects the corresponding constant fibre.
rule @Pullback_catd $A $B $E (@Const_func $A $B $b)
  ↪ @Const_catd $A (@fapp0 $B Cat_cat $E $b);
// A represented family along a constant diagram is pointwise Hom(w,u).
rule @hom_ $A $B (@Const_func $B $A $u) $w
  ↪ @Const_catd $B (Hom_cat $A $w $u);

// Constant target diagrams give constant contravariant represented families.
rule @hom_con $A $W $B (@Const_func $B $A $u)
  ↪ @Const_catd (Op_cat $B) (Hom_cat $A $u $W);

// A contravariant representable into the terminal category is the constant
// terminal family. This whole-family degeneration is needed by the
// terminal-source section-action pipeline.
rule @hom_con Terminal_cat _ $B _
  ↪ @Const_catd (Op_cat $B) Terminal_cat;

// Hom-action of a constant family is constantly the identity functor of A.
rule @fapp1_func $K Cat_cat (@Const_catd $K $A) $x $y
  ↪ @Const_func
      (Hom_cat $K $x $y)
      (Functor_cat $A $A)
      (@id_func $A);

// Every base arrow acts as id_A in the constant family.
rule @fapp1_fapp0 $K Cat_cat (@Const_catd $K $A) $x $y $_ ↪ @id_func $A;

// Fixed-base layer: terminal displayed family.
//
// Surface/formula:
//   Terminal_catd(K) = 1_K = const_K(1).
symbol Terminal_catd (K : Cat) : τ (Catd K)
≔ @Const_catd K Terminal_cat;

// Fixed-base layer: pointwise opposite of a directed family.
//
// Surface/formula:
//   Op_catd(E)[k] = E[k]^op.
injective symbol Op_catd [K : Cat] (E : τ (Catd K)) : τ (Catd K);

// Object projection of pointwise opposite: Op_catd_func(K)[E] ↪ E^op.
rule @fapp0 _ _ (@Op_catd_func $K) $E
  ↪ @Op_catd $K $E;

// Semantic composition with op folds to pointwise displayed opposite.
rule @comp_fapp0 Cat_cat $K Cat_cat Cat_cat op $E
  ↪ @Op_catd $K $E;
// Stable pullback notation for the same pointwise opposite construction.
rule @Pullback_catd $K Cat_cat op $E
  ↪ @Op_catd $K $E;

// Fibre projection: E^op[k] ↪ E[k]^op.
rule @fapp0 $K Cat_cat (@Op_catd $K $E) $k
  ↪ Op_cat (@fapp0 $K Cat_cat $E $k);

// Full base action maps the underlying family action through the internal
// opposite functor, retaining action on higher base cells.
rule @fapp1_func
      $K Cat_cat (@Op_catd $K $E) $x $y
  ↪ @comp_cat_fapp0
      (Hom_cat $K $x $y)
      (Functor_cat (Fibre_cat $E $x) (Fibre_cat $E $y))
      (Functor_cat
        (Op_cat (Fibre_cat $E $x))
        (Op_cat (Fibre_cat $E $y)))
      (@fapp1_func
        Cat_cat Cat_cat op
        (Fibre_cat $E $x)
        (Fibre_cat $E $y))
      (@fapp1_func $K Cat_cat $E $x $y);

// Capped base-arrow action of pointwise opposite is the opposite of the
// underlying displayed-family action.
rule @fapp1_fapp0
      $K Cat_cat (@Op_catd $K $E) $x $y $p
  ↪ @Op_func
      (Fibre_cat $E $x)
      (Fibre_cat $E $y)
      (@fapp1_fapp0 $K Cat_cat $E $x $y $p);

// Pointwise opposite is involutive: (E^op)^op ↪ E.
rule @Op_catd $K (@Op_catd $K $E) ↪ $E;
// Opposite of a constant family is the constant family at A^op.
rule @Op_catd $K (@Const_catd $K $A) ↪ @Const_catd $K (Op_cat $A);

// Fixed-base layer: pointwise opposite of a displayed functor.
//
// Surface/formula:
//   Op_funcd(FF)[k] = Op_func(FF[k]).
injective symbol Op_funcd [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  : τ (Functord (Op_catd E) (Op_catd D));

// Pointwise opposite is involutive on displayed functors.
rule @Op_funcd $K (@Op_catd $K $E) (@Op_catd $K $D) (@Op_funcd $K $E $D $FF)
  ↪ $FF;

// Opposite preserves the displayed identity functor.
rule @Op_funcd $K $E $E (@id (@Catd_cat $K) $E)
  ↪ @id (@Catd_cat $K) (@Op_catd $K $E);

// Pointwise projection of displayed opposite. The source/target family slots
// are deliberately implicit; the explicit `Op_funcd` argument is the
// discriminator.
rule @tapp0_fapp0
      $K
      Cat_cat
      _
      _
      $x
      (@Op_funcd $K $E $D $FF)
  ↪ @Op_func
      (Fibre_cat $E $x)
      (Fibre_cat $D $x)
      (@tapp0_fapp0 $K Cat_cat $E $D $x $FF);

// Pointwise projection of displayed composition. This belongs with the
// displayed-functor calculus: at each base object x, the composite displayed
// functor projects to the ordinary composite of fibre functors.
rule @tapp0_fapp0
      $K Cat_cat $E $C $x
      (@comp_fapp0 (@Catd_cat $K) $E $D $C $FF $GG)
  ↪ @comp_fapp0
      Cat_cat
      (Fibre_cat $E $x)
      (Fibre_cat $D $x)
      (Fibre_cat $C $x)
      (@tapp0_fapp0 $K Cat_cat $D $C $x $FF)
      (@tapp0_fapp0 $K Cat_cat $E $D $x $GG);

// Fixed-base fibrewise-product structural owners.
//
// For B,C : K ⊢ Cat, write
//
//   P(B,C) = uncurry(Product_cat_func) o Product_pair(B,C).
//
// The family remains this transparent semantic composite; no Product_catd
// family head is introduced. These three owners supply the fixed-base
// universal property needed for independent displayed siblings.

// Fibrewise left projection: P(B,C) ⊢_K B.
injective symbol Product_projL_funcd [K : Cat]
  (B C : τ (Catd K))
  : τ (Functord
      (@comp_cat_fapp0
        K
        (Product_cat Cat_cat Cat_cat)
        Cat_cat
        (@uncurry_func Cat_cat Cat_cat Cat_cat Product_cat_func)
        (Struct_sigma B C))
      B);

// Fibrewise right projection: P(B,C) ⊢_K C.
injective symbol Product_projR_funcd [K : Cat]
  (B C : τ (Catd K))
  : τ (Functord
      (@comp_cat_fapp0
        K
        (Product_cat Cat_cat Cat_cat)
        Cat_cat
        (@uncurry_func Cat_cat Cat_cat Cat_cat Product_cat_func)
        (Struct_sigma B C))
      C);

// Fibrewise pairing with one literal shared source:
//   FF : E ⊢_K B, GG : E ⊢_K C ⊢ pair(FF,GG) : E ⊢_K P(B,C).
injective symbol Product_pair_funcd [K : Cat]
  [E B C : τ (Catd K)]
  (FF : τ (Functord E B))
  (GG : τ (Functord E C))
  : τ (Functord
      E
      (@comp_cat_fapp0
        K
        (Product_cat Cat_cat Cat_cat)
        Cat_cat
        (@uncurry_func Cat_cat Cat_cat Cat_cat Product_cat_func)
        (Struct_sigma B C)));

// Point projection: the displayed left projection is ordinary π₁ in each
// fibre.
rule @tapp0_fapp0
      $K Cat_cat _ _ $x
      (@Product_projL_funcd $K $B $C)
  ↪ @Product_projL_func
      (Fibre_cat $B $x)
      (Fibre_cat $C $x);

// Full off-diagonal action of the left projection. The returned
// precomposition functor remains iterable at the next cell.
rule @tapp1_func
      $K Cat_cat _ _ $x $y
      (@Product_projL_funcd $K $B $C)
  ↪ @comp_cat_fapp0
      (Hom_cat $K $x $y)
      (Functor_cat (Fibre_cat $B $x) (Fibre_cat $B $y))
      (Functor_cat
        (Fibre_cat
          (@comp_cat_fapp0
            $K
            (Product_cat Cat_cat Cat_cat)
            Cat_cat
            (@uncurry_func Cat_cat Cat_cat Cat_cat Product_cat_func)
            (Struct_sigma $B $C))
          $x)
        (Fibre_cat $B $y))
      (@comp_cat_con_func
        (Fibre_cat
          (@comp_cat_fapp0
            $K
            (Product_cat Cat_cat Cat_cat)
            Cat_cat
            (@uncurry_func Cat_cat Cat_cat Cat_cat Product_cat_func)
            (Struct_sigma $B $C))
          $x)
        (Fibre_cat $B $x)
        (Fibre_cat $B $y)
        (@Product_projL_func
          (Fibre_cat $B $x)
          (Fibre_cat $C $x)))
      (@fapp1_func $K Cat_cat $B $x $y);

// Capped base-arrow action of the left projection.
rule @tapp1_fapp0
      $K Cat_cat _ _ $x $y
      (@Product_projL_funcd $K $B $C)
      $p
  ↪ @hom_precomp_along_fapp0
      Cat_cat
      Cat_cat
      (@id Cat_cat Cat_cat)
      (Fibre_cat $B $y)
      (Fibre_cat
        (@comp_cat_fapp0
          $K
          (Product_cat Cat_cat Cat_cat)
          Cat_cat
          (@uncurry_func Cat_cat Cat_cat Cat_cat Product_cat_func)
          (Struct_sigma $B $C))
        $x)
      (Fibre_cat $B $x)
      (@Product_projL_func
        (Fibre_cat $B $x)
        (Fibre_cat $C $x))
      (@fapp1_fapp0 $K Cat_cat $B $x $y $p);

// Point projection: the displayed right projection is ordinary π₂ in each
// fibre.
rule @tapp0_fapp0
      $K Cat_cat _ _ $x
      (@Product_projR_funcd $K $B $C)
  ↪ @Product_projR_func
      (Fibre_cat $B $x)
      (Fibre_cat $C $x);

// Full off-diagonal action of the right projection.
rule @tapp1_func
      $K Cat_cat _ _ $x $y
      (@Product_projR_funcd $K $B $C)
  ↪ @comp_cat_fapp0
      (Hom_cat $K $x $y)
      (Functor_cat (Fibre_cat $C $x) (Fibre_cat $C $y))
      (Functor_cat
        (Fibre_cat
          (@comp_cat_fapp0
            $K
            (Product_cat Cat_cat Cat_cat)
            Cat_cat
            (@uncurry_func Cat_cat Cat_cat Cat_cat Product_cat_func)
            (Struct_sigma $B $C))
          $x)
        (Fibre_cat $C $y))
      (@comp_cat_con_func
        (Fibre_cat
          (@comp_cat_fapp0
            $K
            (Product_cat Cat_cat Cat_cat)
            Cat_cat
            (@uncurry_func Cat_cat Cat_cat Cat_cat Product_cat_func)
            (Struct_sigma $B $C))
          $x)
        (Fibre_cat $C $x)
        (Fibre_cat $C $y)
        (@Product_projR_func
          (Fibre_cat $B $x)
          (Fibre_cat $C $x)))
      (@fapp1_func $K Cat_cat $C $x $y);

// Capped base-arrow action of the right projection.
rule @tapp1_fapp0
      $K Cat_cat _ _ $x $y
      (@Product_projR_funcd $K $B $C)
      $p
  ↪ @hom_precomp_along_fapp0
      Cat_cat
      Cat_cat
      (@id Cat_cat Cat_cat)
      (Fibre_cat $C $y)
      (Fibre_cat
        (@comp_cat_fapp0
          $K
          (Product_cat Cat_cat Cat_cat)
          Cat_cat
          (@uncurry_func Cat_cat Cat_cat Cat_cat Product_cat_func)
          (Struct_sigma $B $C))
        $x)
      (Fibre_cat $C $x)
      (@Product_projR_func
        (Fibre_cat $B $x)
        (Fibre_cat $C $x))
      (@fapp1_fapp0 $K Cat_cat $C $x $y $p);

// Pointwise displayed pairing.
rule @tapp0_fapp0
      $K Cat_cat _ _ $x
      (@Product_pair_funcd $K $E $B $C $FF $GG)
  ↪ Struct_sigma
      (@tapp0_fapp0 $K Cat_cat $E $B $x $FF)
      (@tapp0_fapp0 $K Cat_cat $E $C $x $GG);

// Full off-diagonal action of pairing remains a product-valued functor.
rule @tapp1_func
      $K Cat_cat _ _ $x $y
      (@Product_pair_funcd $K $E $B $C $FF $GG)
  ↪ Struct_sigma
      (@tapp1_func $K Cat_cat $E $B $x $y $FF)
      (@tapp1_func $K Cat_cat $E $C $x $y $GG);

// Capped base-arrow action of pairing is componentwise.
rule @tapp1_fapp0
      $K Cat_cat _ _ $x $y
      (@Product_pair_funcd $K $E $B $C $FF $GG)
      $p
  ↪ Struct_sigma
      (@tapp1_fapp0 $K Cat_cat $E $B $x $y $FF $p)
      (@tapp1_fapp0 $K Cat_cat $E $C $x $y $GG $p);

// Fixed-base product universal-property betas.
// lhs-audit: keep 1 -- Catd_cat is the subject-reduction guard for the displayed left beta.
rule @comp_fapp0
      (@Catd_cat $K)
      _
      _
      _
      (@Product_projL_funcd $K $B $C)
      (@Product_pair_funcd $K _ $B $C $FF _)
  ↪ $FF;

// lhs-audit: keep 1 -- Catd_cat is the subject-reduction guard for the displayed right beta.
rule @comp_fapp0
      (@Catd_cat $K)
      _
      _
      _
      (@Product_projR_funcd $K $B $C)
      (@Product_pair_funcd $K _ $B $C _ $GG)
  ↪ $GG;

// 8c. Section categories and Pi action
//
// Fixed-base layer: stable section-category facade for a displayed family.
//
// Surface/formula:
//   Pi_cat(E) = Π k :^n K, E[k]
//             = k :^n K ; 1[k] ⊢ E[k]
//   section object s has components s[k] : E[k].
injective symbol Pi_cat [K : Cat] (E : τ (Catd K)) : Cat;

// Proof-time comparison between the stable section facade and its displayed
// terminal-source presentation.
unif_rule
  @Pi_cat $K $E
  ≡ @Functord_cat $K' (@Const_catd $K' Terminal_cat) $E'
  ↪ [ $K ≡ $K'; $E ≡ $E' ];

// Direct proof-time comparison with the corresponding ordinary Cat-valued
// transfor category; do not rely on unification-rule transitivity.
unif_rule
  @Pi_cat $K $E
  ≡ @Transf_cat $K' Cat_cat (@Const_catd $K' Terminal_cat) $E'
  ↪ [ $K ≡ $K'; $E ≡ $E' ];

// Runtime classifier projection for section objects.
rule Obj (@Pi_cat $K $E)
  ↪ Obj (@Functord_cat $K (@Const_catd $K Terminal_cat) $E);

// Runtime next-hom projection for arrows between sections.
rule Hom_cat (@Pi_cat $K $E) $s $t
  ↪ @Transfd_cat $K (@Const_catd $K Terminal_cat) $E $s $t;

// Proof-time comparison only: sections of a constant family are ordinary
// functors, while the displayed section-category head remains stable.
unif_rule
  @Pi_cat $K (@Const_catd $K $A)
  ≡ Functor_cat $K' $A'
  ↪ [ $K ≡ $K'; $A ≡ $A' ];

unif_rule
  @Functord_cat $K (@Const_catd $K Terminal_cat) (@Const_catd $K $A)
  ≡ Functor_cat $K' $A'
  ↪ [ $K ≡ $K'; $A ≡ $A' ];

// Direct proof-time comparison of arrows between constant sections with
// ordinary transfors. This avoids unification-rule transitivity.
unif_rule
  @Transfd_cat
    $K
    (@Const_catd $K Terminal_cat)
    (@Const_catd $K $A)
    $F $G
  ≡ @Transf_cat $K' $A' $F' $G'
  ↪ [
      $K ≡ $K';
      $A ≡ $A';
      $F ≡ $F';
      $G ≡ $G'
    ];

// Fixed-base layer: functorial section-category constructor at a fixed base.
//
// Surface/formula:
//   Pi_func(K)[E] = Π k :^n K, E[k].
//                 = k :^n K ; 1[k] ⊢ E[k].
injective symbol Pi_func (K : Cat) : τ (Functor (Catd_cat K) Cat_cat);
// Object projection of the section-category package: Pi_func(K)[E] ↪ Pi_cat(E).
rule @fapp0 _ Cat_cat (@Pi_func $K) $E
  ↪ @Pi_cat $K $E;

// Stable displayed-identity bridge for Pi. Generic strict functoriality
// catches `Pi_func(K)[id]`, while this development often keeps the displayed
// identity visible as `id_funcd`; this rule is the same identity preservation
// computation at that stable head.
rule @fapp1_fapp0
      _
      Cat_cat
      (@Pi_func $K)
      $E
      $E
      (@id_funcd $K $E)
  ↪ @id_func (@Pi_cat $K $E);

// Internalized-x layer: global natural package for Pi over varying bases.
//
// Surface/formula:
//   Pi_int_funcd : K :^n Cat^op ; (K ⊢ Cat) ⊢ Cat
//   Pi_int_funcd[K] = Pi_func(K)
//
// The base is Op(Cat) because section categories pull back contravariantly
// along functors.
constant symbol Pi_int_funcd
  : τ (Functord
      Catd_cat_func
      (@Const_catd (Op_cat Cat_cat) Cat_cat));

// Base component of internal Pi: Pi_int_funcd[K] ↪ Pi_func(K).
rule @tapp0_fapp0
      (Op_cat Cat_cat)
      Cat_cat
      _
      _
      $K
      Pi_int_funcd
  ↪ @Pi_func $K;

// Internalized-x layer: stable normal form for pulling the internal Pi package
// back along a Cat-valued contravariant base functor.
//
// Surface/formula:
//   for G : K ⊢ Cat^op,
//   Pi_pullback_funcd(G) : x :^n K ; (G[x] ⊢ Cat) ⊢ Cat
//   Pi_pullback_funcd(G)[x] = Pi_func(G[x])
//   Sigma_catd_transport_func(Pi_pullback_funcd(G),p,E)
//     = section_pullback_func(G[p],E)
//
// The fold rule routes the semantic `Pi_int_funcd`/`Pullback_catd_func`
// expression into this head while keeping the reducible endpoint family slots
// implicit on the LHS.
injective symbol Pi_pullback_funcd [K : Cat]
  (G : τ (Functor K (Op_cat Cat_cat)))
  : τ (Functord
      (@Pullback_catd K (Op_cat Cat_cat) Catd_cat_func G)
      (@Const_catd K Cat_cat));

// Pulling back internal Pi along G folds to the stable Pi_pullback_funcd(G).
rule @fapp1_fapp0
      (@Catd_cat (Op_cat Cat_cat))
      _
      (@Pullback_catd_func $K (Op_cat Cat_cat) $G)
      _
      _
      Pi_int_funcd
  ↪ @Pi_pullback_funcd $K $G;

// Pointwise projection: Pi_pullback_funcd(G)[x] ↪ Pi_func(G[x]).
rule @tapp0_fapp0
      $K
      Cat_cat
      _
      _
      $x
      (@Pi_pullback_funcd $K $G)
  ↪ @Pi_func (@fapp0 $K (Op_cat Cat_cat) $G $x);

// Fixed-base layer: functorial section evaluation at k.
//
// Surface/formula:
//   piapp0_func(E,k) : (Π i :^n K, E[i]) ⊢ E[k].
symbol piapp0_func [K : Cat] (E : τ (Catd K)) (k : τ (Obj K))
  : τ (Functor (Pi_cat E) (Fibre_cat E k))
≔ comp_cat_fapp0
     (@fapp0_func Terminal_cat (Fibre_cat E k) Terminal_obj)
     (@tapp0_func K Cat_cat (@Const_catd K Terminal_cat) E k);

// Fixed-base layer: section object evaluation.
//
// Surface/formula:
//   piapp0(s,k) = s[k] : E[k].
symbol piapp0 : Π [K : Cat], Π [E : τ (Catd K)],
  Π (s : τ (Obj (Pi_cat E))),
  Π (k : τ (Obj K)),
  τ (Obj (Fibre_cat E k))
≔ λ K E s k, @fapp0 (Pi_cat E) (Fibre_cat E k) (@piapp0_func K E k) s;

// 8d. Fibre covariance and dependent-hom endpoint notation
//
// Fixed-base covariant transport from a fibre object.
//
// Surface/formula:
//   fib_cov_tapp0_func(E,x,u,y) : Hom_K(x,y) ⊢ E[y]
//   fib_cov_tapp0_func(E,x,u,y)[f] = E[f](u).
symbol fib_cov_tapp0_func [K : Cat] (E : τ (Catd K))
  [x y : τ (Obj K)]
  (u : τ (Obj (Fibre_cat E x)))
  : τ (Functor (Hom_cat K x y) (Fibre_cat E y))
≔ comp_cat_fapp0
     (@fapp0_func (Fibre_cat E x) (Fibre_cat E y) u)
     (@fapp1_func K Cat_cat E x y);

// General endpoint notation for dependent homs along a displayed functor. The
// old one-family endpoint is the identity-family specialization.
//
// Surface/formula:
//   homd_(FF,x,u,y,v) : Hom_Z(x,y)^op ⊢ Cat
//   homd_(FF,x,u,y,v)[f : x ->^Z y]
//     = Hom_{E[y]}(E[f](u), FF[y](v)).
//
// Here FF : D ⊢_Z E, so the source endpoint u lies in E[x] and the target
// endpoint v lies in D[y].
injective symbol homd_ [Z : Cat] [D E : τ (Catd Z)]
  (FF : τ (Functord D E))
  (x : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj Z))
  (v : τ (Obj (Fibre_cat D y)))
  : τ (Functor (Op_cat (Hom_cat Z x y)) Cat_cat)
≔ @hom_con
     (Fibre_cat E y)
     (fapp0
       (@tapp0_fapp0 Z Cat_cat D E y FF)
       v)
     (Hom_cat Z x y)
     (@fib_cov_tapp0_func Z E x y u);

// Fibre transport is introduced later as a defined projection from the
// reordered functor `fib_cov_tapp0_func`. v3.2 deliberately avoids the v3.1
// generic strict identity/composition transport rewrites for arbitrary
// Cat-valued families.

// -------------------------------------------------------------------------------------------------
// 9. Directed Sigma categories and maps between totals
// -------------------------------------------------------------------------------------------------

// Sigma totalization is a stable constructor package. Its map/projection heads
// are injective in the syntactic kernel sense: equality of these packaged
// constructors may recover their displayed-family data.
/*
  Mathematical notation:
    Sigma_cat(E)              = Σ k :^n K, E[k]
    Obj(Sigma_cat(E))         = Σ (k : Obj K), Obj(E[k])
    Sigma_proj1_func(E)(k,u)  = k
    Sigma_proj1_pullback(R,D) = D pulled back along Sigma_proj1_func(R)
    Π (k,r) :^n Sigma_cat(R), D[k] = Functord_cat(R,D)
    Sigma_func[K][E]          = Sigma_cat(E)
    sigma_map_func(η)(k,u)    = (k, η_k(u))
*/

// 9a. Sigma totals, Sigma homs, and projection

// Fixed-base layer: total category of a directed family.
//
// Surface/formula:
//   Sigma_cat(E) = Σ k :^n K, E[k]
//   Obj(Sigma_cat(E)) has objects (k,u).
//
// Current computational status:
//   The Sigma rules below expose object action, capped 1-arrow action
//   (`fapp1_fapp0`), fixed-endpoint hom-action (`fapp1_func`), and 1-arrow
//   composition. They are deliberately enough for path/arrow transitivity,
//   total transports, rho coherence, and the current Sigma-map hom-action
//   package. Higher hom-action data can still be refined as the omega layer
//   grows.
injective symbol Sigma_cat [K : Cat] (E : τ (Catd K)) : Cat;

// Non-dependent Sigma is ordinary product. This must reduce before the generic
// dependent `Hom(Sigma)` presentation, so constant-family totals inherit the
// pointwise Product normal forms directly.
rule @Sigma_cat $K (@Const_catd $K $A)
  ↪ Product_cat $K $A;

// Fixed-base layer: functorial total-category constructor.
//
// Surface/formula:
//   Sigma_func(K)[E] = Sigma_cat(E).
injective symbol Sigma_func (K : Cat) : τ (Functor (Catd_cat K) Cat_cat);
// Object projection of totalization: Sigma_func(K)[E] ↪ Sigma_cat(E).
rule @fapp0 _ Cat_cat (@Sigma_func $K) $E
  ↪ @Sigma_cat $K $E;

// Objects of Sigma_cat(E) are dependent pairs (k,u) with u : E[k].
rule τ (Obj (@Sigma_cat $K $E))
  ↪ `τΣ_ k : τ (Obj $K), Obj (Fibre_cat $E k);

// Hom categories of Sigma totals are the dependent-hom Sigma over base arrows.
//
// Simplicial reading:
//   A total arrow is a base arrow plus a dependent-hom fibre arrow. Thus Sigma
//   totals provide the iteration step from edges to cells over edges; when the
//   family E is itself hom-shaped, the same Sigma-of-hom pattern becomes the
//   next simplex layer.
//
// Mathematical reading:
//   Hom_{Σ E}((x,u),(y,v))
//     = Σ (p : Hom_K(x,y)), Hom_{E[y]}(E[p](u),v).
//
// Kernel normal form:
//   Hom_{Σ E}((x,u),(y,v))
//     ↪ Op_cat(Σ (p : Hom_K(x,y)^op), homd_(id_E,x,u,y,v)[p]).
rule Hom_cat (@Sigma_cat $K $E) (Struct_sigma $x $u) (Struct_sigma $y $v)
  ↪ Op_cat
      (@Sigma_cat
        (Op_cat (Hom_cat $K $x $y))
        (@homd_ $K $E $E (@id_funcd $K $E) $x $u $y $v));

// Constructor for arrows in a Sigma category, using the Sigma-hom
// characterization above. The explicit fibre arrow is the second component of
// the encoded dependent pair in the reduced hom category.
symbol sigma_arrow [K : Cat] (E : τ (Catd K))
  [x y : τ (Obj K)]
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y)))
  (p : τ (Hom K x y))
  (alpha : τ (Hom
      (Fibre_cat E y)
      (@fapp0
        (Fibre_cat E x)
        (Fibre_cat E y)
        (@catd_transport_func K E x y p)
        u)
      v))
  : τ (Hom
      (@Sigma_cat K E)
      (Struct_sigma x u)
      (Struct_sigma y v))
≔ @Struct_sigma
    (Obj (Op_cat (Hom_cat K x y)))
    (λ f : τ (Obj (Op_cat (Hom_cat K x y))),
      Obj (Fibre_cat (@homd_ K E E (@id_funcd K E) x u y v) f))
    p
    alpha;

// Composition of Sigma arrows.
//
// Surface/formula:
//   (q,beta) ∘ (p,alpha)
//     = (q ∘ p, beta ∘ E[q](alpha)).
//
// The source of E[q](alpha) computes from E[q](E[p](u)) to
// E[q ∘ p](u) by strict object transport. The LHS matches the reduced
// Sigma-hom pair form; the Sigma category itself is the discriminator needed to
// recover K and E.
rule @comp_fapp0
      (@Sigma_cat $K $E)
      (Struct_sigma $x $u)
      (Struct_sigma $y $v)
      (Struct_sigma $z $w)
      (Struct_sigma $q $beta)
      (Struct_sigma $p $alpha)
  ↪ @sigma_arrow
      $K
      $E
      $x
      $z
      $u
      $w
      (@comp_fapp0 $K $x $y $z $q $p)
      (@comp_fapp0
        (Fibre_cat $E $z)
        (@fapp0
          (Fibre_cat $E $x)
          (Fibre_cat $E $z)
          (@catd_transport_func
            $K
            $E
            $x
            $z
            (@comp_fapp0 $K $x $y $z $q $p))
          $u)
        (@fapp0
          (Fibre_cat $E $y)
          (Fibre_cat $E $z)
          (@catd_transport_func $K $E $y $z $q)
          $v)
        $w
        $beta
        (@fapp1_fapp0
          (Fibre_cat $E $y)
          (Fibre_cat $E $z)
          (@catd_transport_func $K $E $y $z $q)
          (@fapp0
            (Fibre_cat $E $x)
            (Fibre_cat $E $y)
            (@catd_transport_func $K $E $x $y $p)
            $u)
          $v
          $alpha));

// Fixed-base layer: first projection from a total category.
//
// Surface/formula:
//   Sigma_proj1_func(E) : Sigma_cat(E) ⊢ K
//   Sigma_proj1_func(E)[(k,u)] = k.
injective symbol Sigma_proj1_func [K : Cat] (E : τ (Catd K))
  : τ (Functor (Sigma_cat E) K);

// First projection on objects: pi_1[(k,u)] ↪ k.
rule fapp0 (Sigma_proj1_func $E) (Struct_sigma $k $u) ↪ $k;

// Structured-arrow projection: pi_1[(p,alpha)] = p.
// lhs-audit: keep 1,2 -- the Sigma source and base target guard the
// projection action.
rule @fapp1_fapp0
      (@Sigma_cat $K $E)
      $K
      (@Sigma_proj1_func $K $E)
      (Struct_sigma _ _)
      (Struct_sigma _ _)
      (Struct_sigma $p _)
  ↪ $p;

// Stable head for the computationally important projection pullback. General
// `Pullback_catd` stays a definition by composition, but this special case is
// discriminable so sections over the total category can contract to displayed
// functors out of the displayed family.
//
// Surface/formula:
//   Sigma_proj1_pullback_catd(R,D)[(k,r)] = D[k].
injective symbol Sigma_proj1_pullback_catd [K : Cat]
  (R D : τ (Catd K))
  : τ (Catd (@Sigma_cat K R));

// Composition presentation of D pulled back along the Sigma first projection.
rule @comp_fapp0
      Cat_cat
      _
      $K
      Cat_cat
      $D
      (@Sigma_proj1_func $K $R)
  ↪ @Sigma_proj1_pullback_catd $K $R $D;

// Stable pullback presentation of the same projection family.
rule @Pullback_catd
      _
      $K
      $D
      (@Sigma_proj1_func $K $R)
  ↪ @Sigma_proj1_pullback_catd $K $R $D;

// Fibre over (k,r): Sigma_proj1_pullback_catd(R,D)[(k,r)] ↪ D[k].
rule @fapp0
      _
      Cat_cat
      (@Sigma_proj1_pullback_catd $K $R $D)
      (Struct_sigma $k $r)
  ↪ @Fibre_cat $K $D $k;

// Structured-arrow action of the stable projection pullback. It is exactly
// D[p]; the fibre component of the Sigma arrow is irrelevant.
// lhs-audit: keep 1,2 -- the Sigma source and Cat target guard the stable
// pullback action.
rule @fapp1_fapp0
      (@Sigma_cat $K $R)
      Cat_cat
      (@Sigma_proj1_pullback_catd $K $R $D)
      (Struct_sigma $x _)
      (Struct_sigma $y _)
      (Struct_sigma $p _)
  ↪ @fapp1_fapp0 $K Cat_cat $D $x $y $p;

// Proof-time uncurrying comparison: sections over a Sigma-projection
// pullback and displayed functors R => D are stable presentations.
unif_rule
  @Pi_cat
    (@Sigma_cat $K $R)
    (@Sigma_proj1_pullback_catd $K $R $D)
  ≡ @Functord_cat $K' $R' $D'
  ↪ [ $K ≡ $K'; $R ≡ $R'; $D ≡ $D' ];

// DISPLAYED-CHAIN-1A explicit object-level bridge from a displayed functor to
// its section over the Sigma total. A stable wrapper is required: the
// proof-time category comparison alone is insufficient to establish subject
// reduction for a rewrite that reinterprets an arbitrary section object as a
// displayed functor.
injective symbol sigma_functord_sec [K : Cat] [R D : τ (Catd K)]
  (FF : τ (Functord R D))
  : τ (Obj
      (@Pi_cat
        (@Sigma_cat K R)
        (@Sigma_proj1_pullback_catd K R D)));

// Component at (k,r): uncurry(FF)[(k,r)] = FF[k](r).
// lhs-audit: keep 1,3,4 -- the Sigma source, terminal source family, and
// projection-pullback target family are the semantic discriminator and
// subject-reduction guard.
rule @tapp0_fapp0
      (@Sigma_cat $K $R)
      Cat_cat
      (@Const_catd (@Sigma_cat $K $R) Terminal_cat)
      (@Sigma_proj1_pullback_catd $K $R $D)
      (Struct_sigma $k $r)
      (@sigma_functord_sec $K $R $D $FF)
  ↪ @Obj_func
      (Fibre_cat $D $k)
      (@fapp0
        (Fibre_cat $R $k)
        (Fibre_cat $D $k)
        (@tapp0_fapp0 $K Cat_cat $R $D $k $FF)
        $r);

// Runtime classifier join after the general Pi and displayed-facade
// projections expose the ordinary Cat-valued-transfor presentation. This is
// the minimal measured join required by path_ind_sec -> fib_cov_transf.
rule Obj
      (@Transf_cat
        (@Sigma_cat $K $R)
        Cat_cat
        (@Const_catd (@Sigma_cat $K $R) Terminal_cat)
        (@Sigma_proj1_pullback_catd $K $R $D))
  ↪ Obj (@Transf_cat $K Cat_cat $R $D);

// Runtime next-hom projection: transformations between Sigma sections are
// displayed transformations between the corresponding displayed functors.
rule @Transfd_cat
      (@Sigma_cat $K $R)
      (@Const_catd (@Sigma_cat $K $R) Terminal_cat)
      (@Sigma_proj1_pullback_catd $K $R $D)
      $s $t
  ↪ @Transfd_cat $K $R $D $s $t;

// 9b. Sigma maps and canonical transport arrows
//
// Fixed-base layer: total map induced by a displayed functor.
//
// Surface/formula:
//   sigma_map_func(η) : Sigma_cat(E) ⊢ Sigma_cat(D)
//   sigma_map_func(η)[(k,u)] = (k,η[k](u)).
injective symbol sigma_map_func [K : Cat] [E D : τ (Catd K)]
  (η : τ (Functord E D))
  : τ (Functor (Sigma_cat E) (Sigma_cat D));

// Stable second-hom projection of Sigma totalization. A displayed transfor
// between displayed maps induces an ordinary transfor between total maps.
injective symbol sigma_map_transf [K : Cat] [E D : τ (Catd K)]
  [FF GG : τ (Functord E D)]
  (eta : τ (Transfd FF GG))
  : τ (@Transf
      (@Sigma_cat K E)
      (@Sigma_cat K D)
      (@sigma_map_func K E D FF)
      (@sigma_map_func K E D GG));

// Hom-action of totalization: Sigma_func(K)[η] ↪ sigma_map_func(η).
rule @fapp1_fapp0 _ Cat_cat (@Sigma_func $K) $E $D $η
  ↪ @sigma_map_func $K $E $D $η;

// Higher hom projection: the generic next action of Sigma_func totalizes a
// displayed transfor. Generic `fapp*` remains the functoriality owner.
// lhs-audit: keep 1,2 -- measured critical-pair guards for the iterated Sigma action
rule @fapp1_fapp0
      (@Functord_cat $K $E $D)
      (Functor_cat (@Sigma_cat $K $E) (@Sigma_cat $K $D))
      (@fapp1_func
        (@Catd_cat $K)
        Cat_cat
        (@Sigma_func $K)
        $E $D)
      $FF $GG $eta
  ↪ @sigma_map_transf $K $E $D $FF $GG $eta;

// Object action of a Sigma map: Sigma(η)[(k,u)] ↪ (k,η[k][u]).
rule @fapp0 _ _
      (@sigma_map_func $K $E $D $η)
      (Struct_sigma $k $u)
  ↪ Struct_sigma
      $k
      (fapp0 (@tapp0_fapp0 $K Cat_cat $E $D $k $η) $u);

// A Sigma map lies over the identity on K: pi_1 ∘ Sigma(η) ↪ pi_1.
rule @comp_fapp0 Cat_cat _ _ _
      (@Sigma_proj1_func $K $D)
      (@sigma_map_func $K $E $D $η)
  ↪ @Sigma_proj1_func $K $E;

// Internalized-x prerequisite: canonical total arrow over a base arrow.
//
// Surface/formula:
//   sigma_transport_arrow(E,p,u) : (x,u) ->^Sigma_cat(E) (y,E[p](u))
//   in Sigma_cat(E) = Σ k :^n K, E[k].
// Canonical total arrow over a base arrow, defined by the smaller Sigma-arrow
// constructor pairing the base arrow with the identity fibre arrow at the
// transported endpoint.
symbol sigma_transport_arrow [K : Cat] (E : τ (Catd K))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x)))
  : τ (Hom
      (@Sigma_cat K E)
      (Struct_sigma x u)
      (Struct_sigma y
        (@fapp0
          (Fibre_cat E x)
          (Fibre_cat E y)
          (@catd_transport_func K E x y p)
          u)))
≔ @sigma_arrow
    K
    E
    x
    y
    u
    (@fapp0
      (Fibre_cat E x)
      (Fibre_cat E y)
      (@catd_transport_func K E x y p)
      u)
    p
    (@id
      (Fibre_cat E y)
      (@fapp0
        (Fibre_cat E x)
        (Fibre_cat E y)
        (@catd_transport_func K E x y p)
        u));

// Generic action of a Sigma map on a canonical total transport arrow.
//
// Surface/formula:
//   sigma_map_transport_arrow(η,p,u)
//     = Sigma(η)[sigma_transport_arrow(E,p,u)]
//     : (x,η[x](u)) ->^Sigma_cat(D) (y,η[y](E[p](u))).
//
// This is a transparent alias for ordinary functor action on the canonical
// total arrow; it deliberately exposes the displayed-functor laxity target
// rather than pretending to be strict transport to D[p](η[x](u)).
symbol sigma_map_transport_arrow [K : Cat] [E D : τ (Catd K)]
  (η : τ (Functord E D))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x)))
  : τ (Hom
      (@Sigma_cat K D)
      (Struct_sigma x
        (@fapp0
          (Fibre_cat E x)
          (Fibre_cat D x)
          (@tapp0_fapp0 K Cat_cat E D x η)
          u))
      (Struct_sigma y
        (@fapp0
          (Fibre_cat E y)
          (Fibre_cat D y)
          (@tapp0_fapp0 K Cat_cat E D y η)
          (@fapp0
            (Fibre_cat E x)
            (Fibre_cat E y)
            (@catd_transport_func K E x y p)
            u))))
≔ @fapp1_fapp0
    (@Sigma_cat K E)
    (@Sigma_cat K D)
    (@sigma_map_func K E D η)
    (Struct_sigma x u)
    (Struct_sigma y
      (@fapp0
        (Fibre_cat E x)
        (Fibre_cat E y)
	    (@catd_transport_func K E x y p)
	    u))
    (@sigma_transport_arrow K E x y p u);

// Total functor induced by asymmetric family pullback.
//
// Surface/formula:
//   sigma_pullback_total_func(F,D) : Sigma(F^*D) ⊢ Sigma(D)
//   sigma_pullback_total_func(F,D)[(a,u)] = (F[a],u).
//
// This is the Grothendieck totalization of the already-active family
// reindexing `Pullback_catd D F`. It is not a pullback constructor for
// arbitrary functors between total categories.
injective symbol sigma_pullback_total_func [A K : Cat]
  (F : τ (Functor A K))
  (D : τ (Catd K))
  : τ (Functor
      (@Sigma_cat A (@Pullback_catd A K D F))
      (@Sigma_cat K D));

// Object projection of pullback totalization: (a,u) ↦ (F[a],u).
rule @fapp0
      _
      _
      (@sigma_pullback_total_func $A $K $F _)
      (Struct_sigma $a $u)
  ↪ Struct_sigma (@fapp0 $A $K $F $a) $u;

// 9c. Families over Sigma totals and displayed-transfor uncurrying
//
// Internalized-x prerequisite: Cat-valued family over a total category induced
// by a displayed functor into the constant category universe.
//
// Surface/formula:
//   if FF : k :^n K ; R[k] ⊢ Cat, then
//   Sigma_catd_functord_catd(FF) : (Σ k :^n K, R[k]) ⊢ Cat
//   Sigma_catd_functord_catd(FF)[(k,r)] = FF[k][r].
symbol Sigma_catd_functord_catd [K : Cat] [R : τ (Catd K)]
  (FF : τ (Functord R (@Const_catd K Cat_cat)))
  : τ (Catd (@Sigma_cat K R));

// Fibre projection: Sigma_catd_functord_catd(FF)[(k,r)] ↪ FF[k][r].
rule @fapp0
      _
      Cat_cat
      (@Sigma_catd_functord_catd $K $R $FF)
      (Struct_sigma $k $r)
  ↪ @fapp0
      (Fibre_cat $R $k)
      Cat_cat
      (@tapp0_fapp0 $K Cat_cat $R (@Const_catd $K Cat_cat) $k $FF)
      $r;

// Internalized-x prerequisite: stable action of a Sigma-induced Cat-valued
// family along the canonical total transport arrow.
//
// Surface/formula:
//   Sigma_catd_transport_func(FF,p,r)
//     : FF[x][r] ⊢ FF[y][R[p](r)]
//   (Sigma_catd_functord_catd(FF))[sigma_transport_arrow(R,p,r)]
//     = Sigma_catd_transport_func(FF,p,r).
//
symbol Sigma_catd_transport_func [K : Cat] [R : τ (Catd K)]
  (FF : τ (Functord R (@Const_catd K Cat_cat)))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  (r : τ (Obj (Fibre_cat R x)))
  : τ (Functor
      (Fibre_cat (@Sigma_catd_functord_catd K R FF) (Struct_sigma x r))
      (Fibre_cat
        (@Sigma_catd_functord_catd K R FF)
        (Struct_sigma y
          (@fapp0
            (Fibre_cat R x)
            (Fibre_cat R y)
            (@catd_transport_func K R x y p)
            r))))
≔ @fapp1_fapp0
    (@Sigma_cat K R)
    Cat_cat
    (@Sigma_catd_functord_catd K R FF)
    (Struct_sigma x r)
    (Struct_sigma y
      (@fapp0
        (Fibre_cat R x)
        (Fibre_cat R y)
        (@catd_transport_func K R x y p)
        r))
    (@sigma_transport_arrow K R x y p r);

// Generic uncurrying of a displayed transfor over a telescope into a displayed
// functor over the Sigma-total category.
//
// Surface/formula:
//   Sigma_transfd_funcd(eta)[(k,r)] = eta[k][r].
//
// The object-component projection rule is installed later, after the generic
// displayed-transfor component head `tdapp0_fapp0` is declared.
constant symbol Sigma_transfd_funcd [K : Cat] [R : τ (Catd K)]
  [S T : τ (Functord R (@Const_catd K Cat_cat))]
  (eta : τ (Transfd S T))
  : τ (Functord
      (@Sigma_catd_functord_catd K R S)
      (@Sigma_catd_functord_catd K R T));

// -------------------------------------------------------------------------------------------------
// 10. Mixed-variance family functor
// -------------------------------------------------------------------------------------------------

/*
  These mixed-variance heads are stable syntactic constructors.  Their
  injectivity is a kernel contract used by unification, not a claim that the
  corresponding categorical data are invariantly recoverable up to equivalence.
  The `_func` suffix is reserved for functor-valued constructor packages.

  Surface/formula:
    Functor_catd(M,N)[k]       = M[k^-] ⊢_[k] N[k]
    Functor_catd_func(K)[M][N] = Functor_catd(M,N)
    Hom_catd(E,X,Y)[k]         = X[k^-] ->_[k]^E Y[k]
    Transf_catd(M,N,FF,GG)[k]  = FF[k^-] =>_[k] GG[k]
*/

injective symbol Functor_catd [K : Cat]
  (A : τ (Catd (Op_cat K)))
  (B : τ (Catd K))
  : τ (Catd K);

// Fibre projection: Functor_catd(A,B)[k] ↪ (A[k] ⊢ B[k]).
rule @fapp0 $K Cat_cat (@Functor_catd $K $A $B) $k
  ↪ Functor_cat (Fibre_cat $A $k) (Fibre_cat $B $k);

// Full base action pairs the negative and positive endpoint actions and then
// applies the ambient Hom telescope used by Unit_prof's full projection.
rule @fapp1_func
      $K Cat_cat (@Functor_catd $K $A $B) $x $y
  ↪ @comp_cat_fapp0
      (Hom_cat $K $x $y)
      (Product_cat
        (Functor_cat (Fibre_cat $A $y) (Fibre_cat $A $x))
        (Functor_cat (Fibre_cat $B $x) (Fibre_cat $B $y)))
      (Functor_cat
        (Functor_cat (Fibre_cat $A $x) (Fibre_cat $B $x))
        (Functor_cat (Fibre_cat $A $y) (Fibre_cat $B $y)))
      (@Hom_tele_func
        Cat_cat
        (Fibre_cat $A $x)
        (Fibre_cat $A $y)
        (Fibre_cat $B $x)
        (Fibre_cat $B $y))
      (Struct_sigma
        (@fapp1_func (Op_cat $K) Cat_cat $A $y $x)
        (@fapp1_func $K Cat_cat $B $x $y));

// Capped base action is exactly Unit_prof(Cat)'s existing Hom_func
// projection at the paired negative/positive endpoint actions.
rule @fapp1_fapp0
      $K Cat_cat (@Functor_catd $K $A $B) $x $y $p
  ↪ @Hom_func
      Cat_cat
      (Fibre_cat $A $x)
      (Fibre_cat $A $y)
      (Fibre_cat $B $x)
      (Fibre_cat $B $y)
      (@fapp1_fapp0 (Op_cat $K) Cat_cat $A $y $x $p)
      (@fapp1_fapp0 $K Cat_cat $B $x $y $p);

// Coherent evaluation for a constant-domain displayed functor family.
//
// For B : K ⊢ Cat and an ordinary category A, write
//
//   S(A,B) = Functor_catd(const_(K^op)(A),B).
//
// Then Eval_funcd(B) : P(S(A,B),const_K(A)) ⊢_K B and
// Eval_funcd(B)[k] = Eval_func(A,B[k]).  The generic tapp/fapp calculus
// carries the base-arrow action and higher naturality; no constructor-specific
// identity, composition, or naturality rule is added here.
injective symbol Eval_funcd [K A : Cat] (B : τ (Catd K))
  : τ (Functord
      (@comp_cat_fapp0
        K
        (Product_cat Cat_cat Cat_cat)
        Cat_cat
        (@uncurry_func Cat_cat Cat_cat Cat_cat Product_cat_func)
        (Struct_sigma
          (@Functor_catd K (@Const_catd (Op_cat K) A) B)
          (@Const_catd K A)))
      B);

// Point component of coherent displayed evaluation.
rule @tapp0_fapp0 _ Cat_cat _ _ $k (@Eval_funcd _ $A $B)
  ↪ @Eval_func $A (Fibre_cat $B $k);

// Internalized constructor package for mixed-variance functor families.
injective symbol Functor_catd_func (K : Cat)
  : τ (Functor
      (Op_cat (Catd_cat (Op_cat K)))
      (Functor_cat (Catd_cat K) (Catd_cat K)));

// Partial application of `Functor_catd_func`.
injective symbol Functor_catd_fapp0_func [K : Cat]
  (A : τ (Catd (Op_cat K)))
  : τ (Functor (Catd_cat K) (Catd_cat K));

// First object projection: Functor_catd_func(K)[A] ↪ Functor_catd_fapp0_func(A).
rule @fapp0 _ _
      (@Functor_catd_func $K) $A
  ↪ @Functor_catd_fapp0_func $K $A;

// Second object projection: Functor_catd_fapp0_func(A)[B] ↪ Functor_catd(A,B).
rule @fapp0 _ _ (@Functor_catd_fapp0_func $K $A) $B
  ↪ @Functor_catd $K $A $B;

// Covariant target-family action projected at k and consumed by H remains a
// whole functor: G[k] o H.  The existing Cat-valued postcomposition owner
// then supplies object and hom action through generic fapp0/fapp1.
rule @fapp0
      _ _
      (@tapp0_fapp0
        $K Cat_cat _ _ $k
        (@fapp1_fapp0
          (Catd_cat $K)
          (Catd_cat $K)
          (@Functor_catd_fapp0_func $K $A)
          $B $D $G))
      $H
  ↪ @hom_postcomp_fapp0
      Cat_cat Cat_cat (@id Cat_cat Cat_cat)
      (Fibre_cat $A $k)
      (Fibre_cat $B $k)
      (Fibre_cat $D $k)
      (@tapp0_fapp0 $K Cat_cat $B $D $k $G)
      $H;

// Contravariant source-family action projected at k and consumed by H remains
// a whole functor: H o L[k]. Generic ordinary action then owns both its object
// and hom projections, so iterated source maps require no capped point rule.
rule @fapp0
      _ _
      (@tapp0_fapp0
        $K Cat_cat _ _ $k
        (@tapp0_fapp0
          (Catd_cat $K)
          (Catd_cat $K)
          (@Functor_catd_fapp0_func $K $A)
          (@Functor_catd_fapp0_func $K $A')
          $B
          (@fapp1_fapp0
            (Op_cat (Catd_cat (Op_cat $K)))
            (Functor_cat (Catd_cat $K) (Catd_cat $K))
            (@Functor_catd_func $K)
            $A $A' $L)))
      $H
  ↪ @comp_cat_fapp0
      (Fibre_cat $A' $k)
      (Fibre_cat $A $k)
      (Fibre_cat $B $k)
      $H
      (@tapp0_fapp0 (Op_cat $K) Cat_cat $A' $A $k $L);

// Pointwise distribution of a pair of mixed functors into a product target.
//
//   dist(A;B,C)
//     : P(Functor_catd(A,B),Functor_catd(A,C))
//         ⊢_K Functor_catd(A,P(B,C)).
//
// Its fibre component is the identity at the ordinary product normal form
// Fun(A[k],B[k]) × Fun(A[k],C[k]). The source-family action owns the
// selected whole base action, so generic fapp1 remains iterable at higher
// cells.
injective symbol Functor_catd_product_funcd [K : Cat]
  [A : τ (Catd (Op_cat K))]
  [B C : τ (Catd K)]
  : τ (Functord
      (@comp_cat_fapp0
        K
        (Product_cat Cat_cat Cat_cat)
        Cat_cat
        (@uncurry_func Cat_cat Cat_cat Cat_cat Product_cat_func)
        (Struct_sigma
          (@Functor_catd K A B)
          (@Functor_catd K A C)))
      (@Functor_catd
        K
        A
        (@comp_cat_fapp0
          K
          (Product_cat Cat_cat Cat_cat)
          Cat_cat
          (@uncurry_func Cat_cat Cat_cat Cat_cat Product_cat_func)
          (Struct_sigma B C))));

// Point component: ordinary product-valued functor normalization makes the
// source and target categories definitionally identical.
rule @tapp0_fapp0
      $K Cat_cat _ _ $k
      (@Functor_catd_product_funcd $K $A $B $C)
  ↪ @id_func
      (Product_cat
        (Functor_cat (Fibre_cat $A $k) (Fibre_cat $B $k))
        (Functor_cat (Fibre_cat $A $k) (Fibre_cat $C $k)));

// Full base action remains the whole action of the product source family.
rule @tapp1_func
      $K Cat_cat _ _ $x $y
      (@Functor_catd_product_funcd $K $A $B $C)
  ↪ @fapp1_func
      $K
      Cat_cat
      (@comp_cat_fapp0
        $K
        (Product_cat Cat_cat Cat_cat)
        Cat_cat
        (@uncurry_func Cat_cat Cat_cat Cat_cat Product_cat_func)
        (Struct_sigma
          (@Functor_catd $K $A $B)
          (@Functor_catd $K $A $C)))
      $x
      $y;

// Capped base action selects the corresponding product-family transport.
rule @tapp1_fapp0
      $K Cat_cat _ _ $x $y
      (@Functor_catd_product_funcd $K $A $B $C)
      $p
  ↪ @fapp1_fapp0
      $K
      Cat_cat
      (@comp_cat_fapp0
        $K
        (Product_cat Cat_cat Cat_cat)
        Cat_cat
        (@uncurry_func Cat_cat Cat_cat Cat_cat Product_cat_func)
        (Struct_sigma
          (@Functor_catd $K $A $B)
          (@Functor_catd $K $A $C)))
      $x
      $y
      $p;

// Mixed-variance hom family for two sections of a displayed family.
//
// Surface/formula:
//   Hom_catd(E,X,Y)[k] = X[k^-] ->_[k]^E Y[k].
injective symbol Hom_catd [K : Cat]
  (E : τ (Catd K))
  (X : τ (Obj (Pi_cat (Op_catd E))))
  (Y : τ (Obj (Pi_cat E)))
  : τ (Catd K);

// Fibre projection: Hom_catd(E,X,Y)[k] ↪ Hom_{E[k]}(X[k^-],Y[k]).
rule @fapp0 $K Cat_cat (@Hom_catd $K $E $X $Y) $k
  ↪ Hom_cat
      (Fibre_cat $E $k)
      (@piapp0 $K (@Op_catd $K $E) $X $k)
      (@piapp0 $K $E $Y $k);

// Mixed-variance transfor family for two displayed functors.
//
// Surface/formula:
//   Transf_catd(M,N,FF,GG)[k] = FF[k^-] =>_[k] GG[k].
//
// Since `Transf_catd(M,N,FF,GG)` is already a Cat-valued family, sections of
// mixed-variance transfors are expressed by `Pi_cat (Transf_catd M N FF GG)`.
// No extra `Pid_cat` alias is needed unless a later computation requires a
// dedicated stable head for that shape.
injective symbol Transf_catd [K : Cat]
  (A : τ (Catd (Op_cat K)))
  (B : τ (Catd K))
  (FF : τ (Obj (Pi_cat (Op_catd (Functor_catd A B)))))
  (GG : τ (Obj (Pi_cat (Functor_catd A B))))
  : τ (Catd K);

// Fibre projection: Transf_catd(A,B,FF,GG)[k] ↪ Transf(FF[k^-],GG[k]).
rule @fapp0 $K Cat_cat (@Transf_catd $K $A $B $FF $GG) $k
  ↪ Transf_cat
      (@piapp0 $K (@Op_catd $K (@Functor_catd $K $A $B)) $FF $k)
      (@piapp0 $K (@Functor_catd $K $A $B) $GG $k);

// Constant-Cat hom families fold to mixed-variance functor families.
rule @Hom_catd $K (@Const_catd $K Cat_cat) $X $Y
  ↪ @Functor_catd $K (@Op_func $K (Op_cat Cat_cat) $X) $Y;

// Hom in a mixed-variance functor family folds to its transfor family.
rule @Hom_catd $K (@Functor_catd $K $A $B) $FF $GG
  ↪ @Transf_catd $K $A $B $FF $GG;

// -------------------------------------------------------------------------------------------------
// 11. Representables and presheaf-family classifiers
// -------------------------------------------------------------------------------------------------

// These named classifiers are defined composition pipelines.  Keep them named
// for readability, but do not use them as primitive discriminators unless a
// later rule genuinely requires that stronger unification contract.
/*
  Mathematical notation:
    Rep_Z(x)[y]               = Hom_Z(x,y)
    Edge_Z(x)[y]              = Hom_Z(x,y)^op
    Presheaf_catd(K)(A)[k]    = Functor_cat(A[k],Cat)
    HomPresheaf_Z(x)[y]       = Functor_cat(Hom_Z(x,y)^op,Cat)
*/

// 11a. Representables

symbol Rep_catd_func [Z : Cat]
  : τ (Functor (Op_cat Z) (Catd_cat Z))
≔ @hom_int Z Z (@id Cat_cat Z);

// Fixed-source representable family.
//
// Surface/formula:
//   Rep_Z(x)[y] = Hom_Z(x,y).
symbol Rep_catd [Z : Cat] (x : τ (Obj Z))
  : τ (Catd Z)
≔ @fapp0 (Op_cat Z) (Catd_cat Z) (@Rep_catd_func Z) x;

// Stable representable transport/precomposition head.
//
// Mathematical notation:
//   Rep_transport(p) : Rep_Z(y) ⊢ Rep_Z(x)
//   Rep_transport(p)[z][q] = q ∘ p.
//
// Canonical comment syntax:
//   (q : y ->^Z z) |-> q ∘ p.
symbol Rep_transport_func [Z : Cat] [x y : τ (Obj Z)]
  (p : τ (Hom Z x y))
  : τ (Functord (@Rep_catd Z y) (@Rep_catd Z x))
≔ @hom_int_precomp_func Z Z (@id Cat_cat Z) y x p;

// 11b. Opposite-edge and presheaf classifiers

// Internalized classifier: pointwise opposite representable.
//
// Surface/formula:
//   Edge_Z(x)[y] = Hom_Z(x,y)^op.
symbol Edge_catd_func [Z : Cat]
  : τ (Functor (Op_cat Z) (Catd_cat Z))
≔ comp_cat_fapp0
     (@Op_catd_func Z)
     (@hom_int Z Z (@id Cat_cat Z));

// Internalized classifier: presheaf category over each fibre of a family.
//
// Surface/formula:
//   Presheaf_catd(K)[A][k] = A[k] ⊢ Cat.
symbol Presheaf_catd_func (K : Cat)
  : τ (Functor
      (Op_cat (Catd_cat (Op_cat K)))
      (Catd_cat K))
≔ comp_cat_fapp0
     (@fapp0_func (Catd_cat K) (Catd_cat K) (@Const_catd K Cat_cat))
     (@Functor_catd_func K);

// Internalized classifier: hom-presheaf family for a represented object.
//
// Surface/formula:
//   HomPresheaf_Z(x)[y] = Hom_Z(x,y)^op ⊢ Cat.
symbol HomPresheaf_catd_func [Z : Cat]
  : τ (Functor Z (Catd_cat (Op_cat Z)))
≔ comp_cat_fapp0
     (@Presheaf_catd_func (Op_cat Z))
     (@Op_func (Op_cat Z) (Catd_cat Z) (@Edge_catd_func Z));

// -------------------------------------------------------------------------------------------------
// 12. Directed homd target and internal homd functor
// -------------------------------------------------------------------------------------------------

/*
  Homd target architecture note:

  Mathematical notation:

    Edge_Z(x)(y)              = Hom_Z(x,y)^op
    HomPsh_Z(x)(y)            = Functor_cat(Hom_Z(x,y)^op, Cat)
    HomdTargetSection_E(x)(y) = E[y^-] ⊢_[y] HomPsh_Z(x)[y]
    HomdTarget_E[x]           = Π y :^n Z^op, HomdTargetSection_E(x)[y]

  `Homd_target_section_catd` and `Homd_target_catd` name these target-family
  expressions for readability and assertions. They are not used as required
  discriminants in the projection-rule LHSs below, because those positions are
  inferred implicit arguments and may reduce to canonical compound terms before
  matching.
*/

symbol Homd_target_section_catd [Z : Cat] (E : τ (Catd Z))
  (x : τ (Obj Z))
  : τ (Catd (Op_cat Z))
≔ @Functor_catd
     (Op_cat Z)
     E
     (@fapp0 Z (Catd_cat (Op_cat Z)) (@HomPresheaf_catd_func Z) x);

// Full target family of the internal displayed hom constructor.
//
// Surface/formula:
//   HomdTarget_E[x] =
//     Π y :^n Z^op, E[y^-] ⊢_[y] HomPsh_Z(x)[y].
symbol Homd_target_catd [Z : Cat] (E : τ (Catd Z))
  : τ (Catd Z)
≔ comp_cat_fapp0
     (comp_cat_fapp0
       (@Pi_func (Op_cat Z))
       (fapp0 (@Functor_catd_func (Op_cat Z)) E))
     (@HomPresheaf_catd_func Z);

// `homd_int` is a syntactic constructor package: its family arguments and
// displayed functor are recoverable from the head. Terminal-source behavior is
// still exposed through the stable projection rules below; avoid adding broad
// whole-family `homd_int` rewrites unless a later design explicitly needs them.
//
// Design/SOP note:
//   The displayed-functor argument is intentional. Prefer `homd_int(FF)` when
//   the target endpoint varies through a displayed functor FF; do not first
//   express the situation as `homd_int(id_D) ∘ Op_funcd(FF)` unless the point of
//   the theorem is that comparison itself. The explicit argument keeps the
//   dependent hom-action and its cut-elimination rules under one stable owner.
//
// Simplicial iteration note:
//   `homd_int(FF)` is the dependent step of the same Sigma-of-hom pattern. Its
//   projection ladder externalizes x and then u:
//
//     homd_int(FF)[x](u) = homd_src_sec(FF,x,u).
//
//   With x,u fixed, this section classifies fibre arrows over base arrows; its
//   Sigma total supplies the next "cell over a cell" layer. This remains a
//   conceptual reading of the existing `homd_int`/Sigma-hom architecture, not a
//   reason to add broad whole-family rewrite rules.
injective symbol homd_int : Π [Z : Cat], Π [D E : τ (Catd Z)],
  Π (FF : τ (Functord D E)),
  τ (Functord (Op_catd E) (@Homd_target_catd Z D));


// -------------------------------------------------------------------------------------------------
// 13. Dependent-hom projections and covariant fibre transport
// -------------------------------------------------------------------------------------------------

/*
  Covariant fibre-transport architecture:

    FibCovTarget_E[x]            = Transf_cat(hom_Z(x,-), E)
                                  ≡ Functord_cat(hom_Z(x,-), E)
    fib_cov_int(E)               : E ⊢ FibCovTarget_E
    fib_cov_src_func(E,x)        : E[x] ⊢ FibCovTarget_E[x]
    fib_cov_transf(E,x,u)        : hom_Z(x,-) => E
                                  ≡ Functord(hom_Z(x,-), E)
    fib_cov_tapp0_func(E,x,u,y)  : Hom_Z(x,y) ⊢ E[y]
    fib_cov_tapp0_func(E,x,u,y)(f) = E[f](u)

  A Cat-valued transfor and the corresponding displayed functor category are
  stable, proof-time-comparable presentations. The declarations below keep
  the conceptual `FibCov_target_catd` family visible; assertions exercise the
  displayed head and its ordinary comparison explicitly.

  `fib_cov_tapp0_func` remains the functor-level normal form. The object-level
  action is just `fapp0 (fib_cov_tapp0_func E x y u) f`, so it is not named by
  a separate `fib_cov_tapp0_fapp0` alias in v3.2.
*/

// Internalized target family for covariant fibre transport.
//
// Surface/formula:
//   FibCov_target(E)[x] = Functord_cat(Rep_K(x),E).
symbol FibCov_target_catd [K : Cat] (E : τ (Catd K)) : τ (Catd K)
≔ @hom_con
    (@Catd_cat K)
    E
    (Op_cat K)
    (@hom_int K K (@id_func K));

// Internalized covariant fibre transport package.
//
// Surface/formula:
//   fib_cov_int(E)[x](u) : Rep_K(x) ⊢ E
//   fib_cov_int(E)[x](u)[y][f] = E[f](u).
constant symbol fib_cov_int : Π [K : Cat], Π (E : τ (Catd K)),
  τ (Functord E (@FibCov_target_catd K E));

// Component functor of `fib_cov_int` at x.
symbol fib_cov_src_func [K : Cat] (E : τ (Catd K))
  (x : τ (Obj K))
  : τ (Functor
      (Fibre_cat E x)
      (Fibre_cat (@FibCov_target_catd K E) x));

// Object component of `fib_cov_src_func`.
injective symbol fib_cov_transf [K : Cat] (E : τ (Catd K))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  : τ (Obj (Fibre_cat (@FibCov_target_catd K E) x));

// First projection: fib_cov_int(E)[x] ↪ fib_cov_src_func(E,x).
rule @tapp0_fapp0
      $K
      Cat_cat
      _
      _
      $x
      (@fib_cov_int $K $E)
  ↪ @fib_cov_src_func $K $E $x;

// Second projection: fib_cov_src_func(E,x)[u] ↪ fib_cov_transf(E,x,u).
rule fapp0 (@fib_cov_src_func $K $E $x) $u
  ↪ @fib_cov_transf $K $E $x $u;

// Third projection: fib_cov_transf(E,x,u)[y] ↪ (f ↦ E[f](u)).
rule @tapp0_fapp0
      $K
      Cat_cat
      _
      _
      $y
      (@fib_cov_transf $K $E $x $u)
  ↪ @fib_cov_tapp0_func $K $E $x $y $u;


/*
  Internal dependent-hom projection cascade:

    homd_int(FF) at x               ↪ homd_src_func(FF,x)
    homd_src_func(FF,x) at u        ↪ homd_src_sec(FF,x,u)
    homd_src_sec(FF,x,u) at y       ↪ homd_tgt_func(FF,x,u,y)
    homd_tgt_func(FF,x,u,y) at v    ↪ homd_(FF,x,u,y,v)

  The identity-specialized compatibility heads from v3.1/v3.2 migration have
  been retired; identity cases are written with `FF := id_funcd E`.
*/

// General first projection of `homd_int`: externalize x and the source fibre
// object in E, while the probe family D remains internal.
//
// Surface/formula:
//   homd_src_func(FF,x) : E[x]^op ⊢ Π y :^n Z^op, ...
symbol homd_src_func [Z : Cat] [D E : τ (Catd Z)]
  (FF : τ (Functord D E))
  (x : τ (Obj Z))
  : τ (Functor
        (Fibre_cat (@Op_catd Z E) x)
        (Pi_cat (@Homd_target_section_catd Z D x)));

// First projection fold. The source and target family arguments are
// deliberately `_`: their canonical forms contain reducible expressions such
// as `fapp0 (Op_catd_func Z) E` and `Homd_target_catd E`.  The Transf_cat
// unification helper above supplies the needed endpoint information.
rule @tapp0_fapp0
      $Z
      Cat_cat
      _
      _
      $x
      (@homd_int $Z $D $E $FF)
  ↪ @homd_src_func $Z $D $E $FF $x;

// General source-fixed projection after evaluating the component functor at u.
//
// Surface/formula:
//   homd_src_sec(FF,x,u)[y] = homd_tgt_func(FF,x,u,y).
symbol homd_src_sec [Z : Cat] [D E : τ (Catd Z)]
  (FF : τ (Functord D E))
  (x : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x)))
  : τ (Obj (Pi_cat (@Homd_target_section_catd Z D x)));

// Second projection fold: externalize x,u and keep the y,v endpoint internal.
rule fapp0 (@homd_src_func $Z $D $E $FF $x) $u
  ↪ @homd_src_sec $Z $D $E $FF $x $u;

// If the target family of FF is terminal, the first projection is a constant
// functor out of the terminal source fibre. This generalizes the old
// identity-specialized terminal-source normal form.
rule @homd_src_func $Z $D (@Const_catd $Z Terminal_cat) $FF $x
  ↪ @Obj_func
      (Pi_cat (@Homd_target_section_catd $Z $D $x))
      (@homd_src_sec $Z $D (@Const_catd $Z Terminal_cat) $FF $x Terminal_obj);

// General inner endpoint functor after projecting the source-fixed section at y.
//
// Surface/formula:
//   homd_tgt_func(FF,x,u,y)[v] = homd_(FF,x,u,y,v).
symbol homd_tgt_func [Z : Cat] [D E : τ (Catd Z)]
  (FF : τ (Functord D E))
  (x : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj Z))
  : τ (Functor
        (Fibre_cat D y)
        (Functor_cat (Op_cat (Hom_cat Z x y)) Cat_cat));

// Terminal-source normal form for the generalized inner endpoint. This exposes
// the same homd-valued family used by piapp1_func without adding a broad
// whole-family homd_int rewrite.
rule @homd_tgt_func $Z (@Const_catd $Z Terminal_cat) $E $s $x $u $y
  ↪ Obj_func
      (homd_
        (@id_funcd $Z $E)
        $x $u
        $y (@piapp0 $Z $E $s $y));

// Third projection fold. In v3.2 `piapp0` is a definition through ordinary
// terminal-source component evaluation, so this rule lives one layer down at
// the `tapp0_fapp0` component. The inferred source/target family arguments are
// deliberately `_` for the same stable-head hygiene as the other homd folds.
rule @tapp0_fapp0
      _
      Cat_cat
      _
      _
      $y
      (@homd_src_sec $Z $D $E $FF $x $u)
  ↪ @Obj_func
      (Fibre_cat (@Homd_target_section_catd $Z $D $x) $y)
      (@homd_tgt_func $Z $D $E $FF $x $u $y);

// Constant-family section evaluation follows ordinary functor application.
// lhs-audit: keep 3 -- terminal-source family is the semantic discriminator
rule @tapp0_fapp0
      $K
      Cat_cat
      (@Const_catd $K Terminal_cat)
      (@Const_catd $K $A)
      $k
      $F
  ↪ @Obj_func $A (@fapp0 $K $A $F $k);

// Final endpoint fold. At this point the stable head `homd_` carries the
// endpoint family; pointwise object-action is handled by unfolding `homd_`.
rule fapp0 (@homd_tgt_func $Z $D $E $FF $x $u $y) $v
  ↪ @homd_ $Z $D $E $FF $x $u $y $v;

// -------------------------------------------------------------------------------------------------
// 14. Section action over dependent homs
// -------------------------------------------------------------------------------------------------

/*
  Section action source endpoint.

  Mathematical notation:
    s[x]                = piapp0 s x
    piapp1_src_obj(s,f) = E[f](s[x]).

  The full `piapp1_func`/`piapp1_fapp0` package is defined after the displayed
  internal-hom projection heads it unfolds through.
*/
symbol piapp1_src_obj [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  [x y : τ (Obj K)]
  (f : τ (Hom K x y))
  : τ (Obj (Fibre_cat E y))
≔ fapp0 (@fib_cov_tapp0_func K E x y (@piapp0 K E s x)) f;

// -------------------------------------------------------------------------------------------------
// 15. Internal displayed hom-action heads
// -------------------------------------------------------------------------------------------------

/*
  Mathematical notation:
    tdapp1_int_func_transfd(FF,GG)
      : Transfd(FF,GG) ⊢ Transfd(homd_int(id_E), homd_int(GG) ∘ FF^op)

    tdapp1_int_fapp0_transfd(ϵ)
      = the internal displayed hom-action of ϵ

    fdapp1_int_transfd(FF)
      = tdapp1_int_fapp0_transfd(id_FF)

  Current laxity architecture:

    internal hom-action, then extracted laxity, then Sigma action consumes laxity.

  The Sigma-total presentation is the externalization/test surface where a
  laxity cell is visible as a fibre component of a total arrow. It is not the
  primitive source of that same laxity; otherwise `Sigma(FF)` would be defined
  using `laxity(FF,p)` and `laxity(FF,p)` would be extracted back from
  `Sigma(FF)`, which is circular.

  The intended non-circular source for displayed functor laxity is the
  identity-specialized internal displayed hom-action:

    fdapp1_int_transfd(FF)
      : Transfd(homd_int(id_E), homd_int(FF) ∘ Op_funcd(FF)).

  Applying this to a canonical/cartesian dependent-hom triangle should expose
  the component

    D[p](FF[x](u)) ->^(D[y]) FF[y](E[p](u)).

  The active implementation stops at this component-level normal form,
  `fdapp1_int_cell(FF,p,u)`. A future whole-transfor interface
  should be added only after the source object `u` can be internalized without
  obscuring this extraction path. Strict constructors then need explicit folds
  making their laxity collapse to the identity/cartesian component.
*/
symbol tdapp1_int_func_transfd : Π [K : Cat], Π [E D : τ (Catd K)],
  Π [FF GG : τ (Functord E D)],
  τ (Functor
      (Transfd_cat FF GG)
      (Transfd_cat
        (homd_int (@id_funcd K E))
        (comp_catd_fapp0
          (homd_int GG)
          (Op_funcd FF))));

// Object action of `tdapp1_int_func_transfd`.
symbol tdapp1_int_fapp0_transfd : Π [K : Cat], Π [E D : τ (Catd K)],
  Π [FF GG : τ (Functord E D)],
  Π (ϵ : τ (Transfd FF GG)),
  τ (Transfd
      (homd_int (@id_funcd K E))
      (comp_catd_fapp0
        (homd_int GG)
        (Op_funcd FF)));

// Object projection: tdapp1_int_func_transfd(FF,GG)[epsilon].
rule fapp0 (@tdapp1_int_func_transfd $K $E $D $FF $GG) $ϵ
  ↪ @tdapp1_int_fapp0_transfd $K $E $D $FF $GG $ϵ;

// Hom action of `tdapp1_int_func_transfd`.
symbol tdapp1_int_fapp1_func_transfd : Π [K : Cat], Π [E D : τ (Catd K)],
  Π [FF GG : τ (Functord E D)],
  Π (ϵ ϵ' : τ (Transfd FF GG)),
  τ (Functor
      (Hom_cat (Transfd_cat FF GG) ϵ ϵ')
      (Hom_cat
        (Transfd_cat
          (homd_int (@id_funcd K E))
          (comp_catd_fapp0
            (homd_int GG)
            (Op_funcd FF)))
        (tdapp1_int_fapp0_transfd ϵ)
        (tdapp1_int_fapp0_transfd ϵ')));

// Hom-functor projection between internal displayed hom-action components.
rule @fapp1_func _ _ (@tdapp1_int_func_transfd $K $E $D $FF $GG) $ϵ $ϵ'
  ↪ @tdapp1_int_fapp1_func_transfd $K $E $D $FF $GG $ϵ $ϵ';

// Identity-specialized displayed internal hom-action.
symbol fdapp1_int_transfd : Π [K : Cat], Π [E D : τ (Catd K)],
  Π (FF : τ (Functord E D)),
  τ (Transfd
      (homd_int (@id_funcd K E))
      (comp_catd_fapp0
        (homd_int FF)
        (Op_funcd FF)));

// Identity-specialization fold for the internal displayed hom-action.
rule @tdapp1_int_fapp0_transfd $K $E $D $FF $FF
      (@id (@Functord_cat $K $E $D) $FF)
  ↪ @fdapp1_int_transfd $K $E $D $FF
with @tdapp1_int_fapp0_transfd $K $E $D $FF $FF
      (@id (@Transf_cat $K Cat_cat $E $D) $FF)
  ↪ @fdapp1_int_transfd $K $E $D $FF;


// -------------------------------------------------------------------------------------------------
// 16. Displayed components, displayed hom-action, and laxity extraction
// -------------------------------------------------------------------------------------------------

// 16a. Fibre-level displayed components
/*
  Fibre-level notation for displayed functors and displayed transfors.

  Mathematical notation:

    Fibre_func(FF,z)          = FF[z] : E[z] ⊢ D[z]
    tdapp0_func(z)            : Transfd(FF,GG) ⊢ Transf(FF[z],GG[z])
    tdapp0_fapp0(z,ϵ)         = ϵ_z : FF[z] => GG[z]
    Fibre_transf(ϵ,z)         = ϵ_z
    Fibre_transf_app(ϵ,z,u)   = ϵ_z(u)

  `tdapp0_func` and `tdapp0_fapp0` are stable projection heads: later rewrite
  rules attach to them directly. The `Fibre_*` names are readable definitions
  over these heads, not additional kernel rewrite surfaces.
*/
// Fibre functor of a displayed functor at z.
//
// Surface/formula:
//   Fibre_func(FF,z) = FF[z] : E[z] ⊢ D[z].
symbol Fibre_func [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  (z : τ (Obj K))
  : τ (Functor (Fibre_cat E z) (Fibre_cat D z))
≔ @tapp0_fapp0 K Cat_cat E D z FF;

// Component projection functor for displayed transfors at z.
//
// Surface/formula:
//   tdapp0_func(z)[epsilon] = epsilon[z].
symbol tdapp0_func [K : Cat] [E D : τ (Catd K)]
  [FF GG : τ (Functord E D)]
  (z : τ (Obj K))
  : τ (Functor
      (Transfd_cat FF GG)
      (Transf_cat (Fibre_func FF z) (Fibre_func GG z)));

// Capped displayed-transfor component.
//
// Surface/formula:
//   tdapp0_fapp0(z,epsilon) = epsilon[z] : FF[z] => GG[z].
symbol tdapp0_fapp0 [K : Cat] [E D : τ (Catd K)]
  [FF GG : τ (Functord E D)]
  (z : τ (Obj K))
  (ϵ : τ (Transfd FF GG))
  : τ (Transf (Fibre_func FF z) (Fibre_func GG z));

// Projection from displayed-transfor component functor to capped component.
rule fapp0 (@tdapp0_func $K $E $D $FF $GG $z) $ϵ
  ↪ @tdapp0_fapp0 $K $E $D $FF $GG $z $ϵ;

// Cat-valued higher component: the hom action of ordinary component
// evaluation is the displayed-transfor component at the same base object.
// This is the generic owner used, in particular, by the hom action of
// `piapp0_func`; it is not a Pi-specific commuting bridge.
rule @fapp1_func
      _
      _
      (@tapp0_func $K Cat_cat $E $D $z)
      $FF $GG
  ↪ @tdapp0_func $K $E $D $FF $GG $z;

// Direct capped projection joins the full hom-action route above.
rule @fapp1_fapp0
      _
      _
      (@tapp0_func $K Cat_cat $E $D $z)
      $FF $GG $eta
  ↪ @tdapp0_fapp0 $K $E $D $FF $GG $z $eta;

// Displayed component of an identity transfor. The two clauses expose the
// same generic identity through the stable displayed and ordinary category
// presentations without introducing a second identity constructor.
rule @tdapp0_fapp0
      $K $E $D $FF $FF $z
      (@id (@Functord_cat $K $E $D) $FF)
  ↪ @id
      (Functor_cat (Fibre_cat $E $z) (Fibre_cat $D $z))
      (@Fibre_func $K $E $D $FF $z)
with @tdapp0_fapp0
      $K $E $D $FF $FF $z
      (@id (@Transf_cat $K Cat_cat $E $D) $FF)
  ↪ @id
      (Functor_cat (Fibre_cat $E $z) (Fibre_cat $D $z))
      (@Fibre_func $K $E $D $FF $z);

// Displayed vertical-composite components compose pointwise. The outer
// inferred slots are reconstructed from the rigid category and endpoints of
// the inner composite; this is projection beta, not a second functoriality
// owner.
rule @tdapp0_fapp0
      _ _ _ _ _ $z
      (@comp_fapp0
        (@Functord_cat $K $E $D)
        $FF $GG $HH $eta $epsilon)
  ↪ @comp_fapp0
      (Functor_cat (Fibre_cat $E $z) (Fibre_cat $D $z))
      (@Fibre_func $K $E $D $FF $z)
      (@Fibre_func $K $E $D $GG $z)
      (@Fibre_func $K $E $D $HH $z)
      (@tdapp0_fapp0 $K $E $D $GG $HH $z $eta)
      (@tdapp0_fapp0 $K $E $D $FF $GG $z $epsilon)
with @tdapp0_fapp0
      _ _ _ _ _ $z
      (@comp_fapp0
        (@Transf_cat $K Cat_cat $E $D)
        $FF $GG $HH $eta $epsilon)
  ↪ @comp_fapp0
      (Functor_cat (Fibre_cat $E $z) (Fibre_cat $D $z))
      (@Fibre_func $K $E $D $FF $z)
      (@Fibre_func $K $E $D $GG $z)
      (@Fibre_func $K $E $D $HH $z)
      (@tdapp0_fapp0 $K $E $D $GG $HH $z $eta)
      (@tdapp0_fapp0 $K $E $D $FF $GG $z $epsilon);

// Projection-order join for pre/right naturality when the source functor is
// Cat-valued component evaluation. The generic `fapp1_fapp0` component has
// already projected to `tdapp0_fapp0` on the right cut.
// Keep the outer category inferred: a product-valued target fibre can reduce
// `Functor_cat(X,A×B)` before this projection-order bridge is selected. Share
// that inferred head with the ordinary component's codomain.
rule @comp_fapp0
      $B _ _ _
      (@tapp1_fapp0
        (@Transf_cat $K Cat_cat $E $D)
        $B
        (@tapp0_func $K Cat_cat $E $D $z)
        $G
        $GG $HH $epsilon $f)
      (@tdapp0_fapp0 $K $E $D $FF $GG $z $g)
  ↪ @tapp1_fapp0
      (@Transf_cat $K Cat_cat $E $D)
      $B
      (@tapp0_func $K Cat_cat $E $D $z)
      $G
      $FF $HH $epsilon
      (@comp_fapp0
        (@Transf_cat $K Cat_cat $E $D)
        $FF $GG $HH $f $g);

// Projection-order join for post/left naturality when the target functor is
// Cat-valued component evaluation. The generic `fapp1_fapp0` component has
// already projected to `tdapp0_fapp0` on the left cut.
// Keep and share the outer category for the same product-target reason.
rule @comp_fapp0
      $B _ _ _
      (@tdapp0_fapp0 $K $E $D $GG $HH $z $g)
      (@tapp1_fapp0
        (@Transf_cat $K Cat_cat $E $D)
        $B
        $F
        (@tapp0_func $K Cat_cat $E $D $z)
        $FF $GG $epsilon $f)
  ↪ @tapp1_fapp0
      (@Transf_cat $K Cat_cat $E $D)
      $B
      $F
      (@tapp0_func $K Cat_cat $E $D $z)
      $FF $HH $epsilon
      (@comp_fapp0
        (@Transf_cat $K Cat_cat $E $D)
        $FF $GG $HH $g $f);

// Identity-base degeneration of the pre/right bridge. If the off-diagonal
// component reduces first, `tapp1(epsilon,id)` has become `tapp0(epsilon)`.
rule @comp_fapp0
      $B _ _ _
      (@tapp0_fapp0
        (@Transf_cat $K Cat_cat $E $D)
        $B
        (@tapp0_func $K Cat_cat $E $D $z)
        $G
        $GG $epsilon)
      (@tdapp0_fapp0 $K $E $D $FF $GG $z $g)
  ↪ @tapp1_fapp0
      (@Transf_cat $K Cat_cat $E $D)
      $B
      (@tapp0_func $K Cat_cat $E $D $z)
      $G
      $FF $GG $epsilon $g;

// Identity-base degeneration of the post/left bridge.
rule @comp_fapp0
      $B _ _ _
      (@tdapp0_fapp0 $K $E $D $FF $GG $z $g)
      (@tapp0_fapp0
        (@Transf_cat $K Cat_cat $E $D)
        $B
        $F
        (@tapp0_func $K Cat_cat $E $D $z)
        $FF $epsilon)
  ↪ @tapp1_fapp0
      (@Transf_cat $K Cat_cat $E $D)
      $B
      $F
      (@tapp0_func $K Cat_cat $E $D $z)
      $FF $GG $epsilon $g;


// Object-component projection for generic Sigma-total uncurrying.
rule @tapp0_fapp0
      _
      Cat_cat
      _
      _
      (Struct_sigma $k $r)
      (@Sigma_transfd_funcd $K $R $S $T $eta)
  ↪ @tapp0_fapp0
      (Fibre_cat $R $k)
      Cat_cat
      (@Fibre_func $K $R (@Const_catd $K Cat_cat) $S $k)
      (@Fibre_func $K $R (@Const_catd $K Cat_cat) $T $k)
      $r
      (@tdapp0_fapp0
        $K
        $R
        (@Const_catd $K Cat_cat)
        $S
        $T
        $k
        $eta);

// Point component of the totalized displayed transfor at (k,u): the
// fibrewise component lies over the identity base arrow.
rule @tapp0_fapp0
      _ _
      _ _
      (Struct_sigma $k $u)
      (@sigma_map_transf $K $E $D $FF $GG $eta)
  ↪ @sigma_arrow
      $K $D
      $k $k
      (@fapp0
        (Fibre_cat $E $k)
        (Fibre_cat $D $k)
        (@Fibre_func $K $E $D $FF $k)
        $u)
      (@fapp0
        (Fibre_cat $E $k)
        (Fibre_cat $D $k)
        (@Fibre_func $K $E $D $GG $k)
        $u)
      (@id $K $k)
      (@tapp0_fapp0
        (Fibre_cat $E $k)
        (Fibre_cat $D $k)
        (@Fibre_func $K $E $D $FF $k)
        (@Fibre_func $K $E $D $GG $k)
        $u
        (@tdapp0_fapp0 $K $E $D $FF $GG $k $eta));

// Readable component alias.
//
// Surface/formula:
//   Fibre_transf(epsilon,z) = epsilon[z].
symbol Fibre_transf [K : Cat] [E D : τ (Catd K)]
  [FF GG : τ (Functord E D)]
  (ϵ : τ (Transfd FF GG))
  (z : τ (Obj K))
  : τ (Transf (Fibre_func FF z) (Fibre_func GG z))
≔ @tdapp0_fapp0 K E D FF GG z ϵ;

// Object action of a displayed-transfor component.
//
// Surface/formula:
//   Fibre_transf_app(epsilon,z,u) = epsilon[z][u].
symbol Fibre_transf_app [K : Cat] [E D : τ (Catd K)]
  [FF GG : τ (Functord E D)]
  (ϵ : τ (Transfd FF GG))
  (z : τ (Obj K))
  (u : τ (Obj (Fibre_cat E z)))
  : τ (Hom
      (Fibre_cat D z)
      (fapp0 (Fibre_func FF z) u)
      (fapp0 (Fibre_func GG z) u))
≔ @tapp0_fapp0
     (Fibre_cat E z)
     (Fibre_cat D z)
     (@Fibre_func K E D FF z)
     (@Fibre_func K E D GG z)
     u
     (@Fibre_transf K E D FF GG ϵ z);

// Fixed-base layer: component of an arrow between sections.
//
// Mathematical notation:
//   pi_hom_fapp0(eta,k) = eta[k] : s[k] ->^(E[k]) t[k]
//   for eta : Hom_{Π i :^n K, E[i]}(s,t).
//
// Canonical comment syntax:
//   eta[k] : s[k] ->^(E[k]) t[k].
//
// This is a semantic definition over the existing displayed component
// projection. There is intentionally no rewrite rule targeting `piapp0_func`:
// that head is definable, so it is not a rewrite discriminator.
symbol pi_hom_fapp0 [K : Cat] [E : τ (Catd K)]
  [s t : τ (Obj (Pi_cat E))]
  (eta : τ (Hom (Pi_cat E) s t))
  (k : τ (Obj K))
  : τ (Hom (Fibre_cat E k) (piapp0 s k) (piapp0 t k))
≔ tapp0_fapp0 Terminal_obj (tdapp0_fapp0 k eta);

// Internalized-x prerequisite: heterogeneous action of a displayed functor over
// a base arrow. This is the Cat-valued specialization of the ordinary transfor
// hom-action.
//
// Surface/formula:
//   FF[p] : E[x] ⊢ D[y]
//   for FF : k :^n K ; E[k] ⊢ D[k] and p : x ->^K y.
symbol functord_transport_func [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  : τ (Functor (Fibre_cat E x) (Fibre_cat D y))
≔ @tapp1_fapp0 K Cat_cat E D x y FF p;

// Internalized-x coherence route: first apply FF at x, then transport in D.
//
// Surface/formula:
//   D[p] ∘ FF[x] : E[x] ⊢ D[y].
symbol functord_transport_lhs_func [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  : τ (Functor (Fibre_cat E x) (Fibre_cat D y))
≔ @comp_cat_fapp0
    (Fibre_cat E x)
    (Fibre_cat D x)
    (Fibre_cat D y)
    (@catd_transport_func K D x y p)
    (@Fibre_func K E D FF x);

// Internalized-x coherence route: first transport in E, then apply FF at y.
//
// Surface/formula:
//   FF[y] ∘ E[p] : E[x] ⊢ D[y].
symbol functord_transport_rhs_func [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  : τ (Functor (Fibre_cat E x) (Fibre_cat D y))
≔ @comp_cat_fapp0
    (Fibre_cat E x)
    (Fibre_cat E y)
    (Fibre_cat D y)
    (@Fibre_func K E D FF y)
    (@catd_transport_func K E x y p);

// 16b. Identity-specialized displayed hom action and Sigma-map action
/*
  Deferred whole-transfor displayed laxity interface.

  Intended future surface:

    functord_laxity_transf(FF,p)
      : D[p] ∘ FF[x] => FF[y] ∘ E[p].

  Intended declaration, deliberately not active yet:

    symbol functord_laxity_transf [K : Cat] [E D : τ (Catd K)]
      (FF : τ (Functord E D))
      [x y : τ (Obj K)]
      (p : τ (Hom K x y))
      : τ (@Transf
          (Fibre_cat E x)
          (Fibre_cat D y)
          (@functord_transport_lhs_func K E D FF x y p)
          (@functord_transport_rhs_func K E D FF x y p));

  The active implementation stops at the component-level cell
  `fdapp1_int_cell(FF,p,u)`. Reintroduce the live symbol only after
  the `fdapp1_int_transfd` extraction internalizes `u` cleanly enough to support
  the whole `Transf` computationally.
*/

// Capped object action of the extracted displayed internal-hom functor.
//
// Mathematical notation:
//   fdapp1_int(FF)[x,u][y,v][p][alpha]
//     : D[p](FF[x]u) ->^(D[y]) FF[y]v.
//
// Canonical comment syntax:
//   the Sigma-map fibre component induced by the internal displayed hom-action.
//
// This is deliberately the owner of the Sigma-map fibre component. The surface
// reading may be `FF[y][alpha] ∘ laxity(FF,p)[u]`, but the kernel normal form is
// this direct projection from the internal-hom action, not a reconstructed
// composite through an artificial `FF[y][alpha]` head.
symbol fdapp1_int_hom_fapp0 [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x)))
  [v : τ (Obj (Fibre_cat E y))]
  (alpha : τ (Hom
      (Fibre_cat E y)
      (@fapp0
        (Fibre_cat E x)
        (Fibre_cat E y)
        (@catd_transport_func K E x y p)
        u)
      v))
  : τ (Hom
      (Fibre_cat D y)
      (@fapp0
        (Fibre_cat E x)
        (Fibre_cat D y)
        (@functord_transport_lhs_func K E D FF x y p)
        u)
      (@fapp0
        (Fibre_cat E y)
        (Fibre_cat D y)
        (@Fibre_func K E D FF y)
        v));

// Arrow action of a Sigma map on the canonical Sigma-hom constructor.
//
// Surface/formula:
//   Sigma(FF)[(p,alpha)]
//     = (p, fdapp1_int(FF)[x,u][y,v][p][alpha]).
//
// This is the capped action `fapp1_fapp0` of `sigma_map_func`. The corresponding
// fixed-endpoint hom-action package is folded later, after
// `fdapp1_int_presheaf_arrow` is available.
rule @fapp1_fapp0
      _
      _
      (@sigma_map_func $K $E $D $η)
      (Struct_sigma $x $u)
      (Struct_sigma $y $v)
      (Struct_sigma $p $alpha)
  ↪ @sigma_arrow
      $K
      $D
      $x
      $y
      (@fapp0
        (Fibre_cat $E $x)
        (Fibre_cat $D $x)
        (@tapp0_fapp0 $K Cat_cat $E $D $x $η)
        $u)
      (@fapp0
        (Fibre_cat $E $y)
        (Fibre_cat $D $y)
        (@tapp0_fapp0 $K Cat_cat $E $D $y $η)
        $v)
      $p
      (@fdapp1_int_hom_fapp0
        $K
        $E
        $D
        $η
        $x
        $y
        $p
        $u
        $v
        $alpha);

// Source dependent-hom section used by the internal-hom extraction.
//
// Mathematical notation:
//   homd_id_src_sec(E,x,u)
//     = homd_int(id_E)[x](u)
//     : Π y :^n K^op, E[y^-] ⊢_[y] (Hom_K(x,y)^op ⊢ Cat).
//
// Canonical comment syntax:
//   Homd_E(x,u,—,—).
symbol homd_id_src_sec [K : Cat] (E : τ (Catd K))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  : τ (Obj (Pi_cat (Homd_target_section_catd E x)))
≔ homd_src_sec (@id_funcd K E) x u;

// Target dependent-hom section obtained by applying FF to the source object.
//
// Mathematical notation:
//   homd_ff_src_sec(FF,x,u)
//     = homd_int(FF)[x](FF[x](u))
//     : Π y :^n K^op, E[y^-] ⊢_[y] (Hom_K(x,y)^op ⊢ Cat).
//
// Canonical comment syntax:
//   Homd_D(x,FF[x](u),—,FF[—](—)).
symbol homd_ff_src_sec [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  : τ (Obj (Pi_cat (Homd_target_section_catd E x)))
≔ homd_src_sec FF x (fapp0 (Fibre_func FF x) u);

// First concrete stage of the non-circular laxity extraction path. This is the
// component of the internal displayed hom-action at the represented source x
// and source fibre object u. Its source is the identity dependent-hom section;
// its target is the section obtained by first applying FF at x and then using
// `homd_int(FF)`.
//
// Mathematical notation:
//   fdapp1_section(FF,x,u) :
//     homd_int(id_E)[x](u) ->^(HomdTarget_E[x]) homd_int(FF)[x](FF[x](u)).
//
// Canonical comment syntax:
//   fdapp1_int(FF)[x,u] :
//     Homd_E(x,u,—,—) ->^(HomdTarget_E[x]) Homd_D(x,FF[x](u),—,FF[—](—)).
//
// Further projections at y, at the transported object E[p](u), and at the base
// arrow p produce the component-level displayed laxity cell.
symbol fdapp1_int_section_arrow [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  : τ (Hom
      (Fibre_cat (Homd_target_catd E) x)
      (homd_id_src_sec E x u)
      (homd_ff_src_sec FF x u));

// First projection fold for identity-specialized displayed hom-action.
//
// Surface/formula:
//   fdapp1_int_transfd(FF)[x][u] = fdapp1_int_section_arrow(FF,x,u).
rule @tapp0_fapp0
      _
      _
      _
      _
      $u
      (@tdapp0_fapp0
        $K
        _
        _
        _
        _
        $x
        (@fdapp1_int_transfd $K $E $D $FF))
  ↪ @fdapp1_int_section_arrow $K $E $D $FF $x $u;

// Source y-component of the identity dependent-hom section.
//
// Mathematical notation:
//   homd_id_tgt_func(E,x,u,y)
//     = homd_int(id_E)[x](u)[y].
//
// Canonical comment syntax:
//   Homd_E(x,u,y,—).
symbol homd_id_tgt_func [K : Cat] (E : τ (Catd K))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj K))
  : τ (Functor
      (Fibre_cat E y)
      (Functor_cat (Op_cat (Hom_cat K x y)) Cat_cat))
≔ piapp0 (homd_id_src_sec E x u) y;

// Target y-component after applying FF to the source object.
//
// Mathematical notation:
//   homd_ff_tgt_func(FF,x,u,y)
//     = homd_int(FF)[x](FF[x](u))[y].
//
// Canonical comment syntax:
//   Homd_D(x,FF[x](u),y,FF[y](—)).
symbol homd_ff_tgt_func [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj K))
  : τ (Functor
      (Fibre_cat E y)
      (Functor_cat (Op_cat (Hom_cat K x y)) Cat_cat))
≔ piapp0 (homd_ff_src_sec FF x u) y;

// Second projection stage of the same internal-hom extraction path.
//
// Mathematical notation:
//   fdapp1_section(FF,x,u)[y] :
//     homd_int(id_E)[x](u)[y]
//       => homd_int(FF)[x](FF[x](u))[y].
//
// Canonical comment syntax:
//   fdapp1_int(FF)[x,u][y] :
//     Homd_E(x,u,y,—) => Homd_D(x,FF[x](u),y,FF[y](—)).
//
// The type is written in the reduced `Transf` form because the next projection
// consumes it through `tapp0_fapp0`. This still keeps the codomain functor in
// the canonical `Hom_K(x,y)^op ⊢ Cat` form, avoiding the reducible
// `Fibre_cat(HomPresheaf_Z(x),y)` classifier pipeline.
symbol fdapp1_int_tgt_arrow [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj K))
  : τ (Transf
      (homd_id_tgt_func E x u y)
      (homd_ff_tgt_func FF x u y));

// Second projection fold for identity-specialized displayed hom-action.
//
// Surface/formula:
//   fdapp1_int_section_arrow(FF,x,u)[y] = fdapp1_int_tgt_arrow(FF,x,u,y).
rule @tapp0_fapp0
      _
      _
      _
      _
      Terminal_obj
      (@tdapp0_fapp0
        _
        _
        _
        _
        _
        $y
        (@fdapp1_int_section_arrow $K $E $D $FF $x $u))
  ↪ @fdapp1_int_tgt_arrow $K $E $D $FF $x $u $y;

// Third projection stage: evaluate the y-component at a fibre object v.
//
// Mathematical notation:
//   fdapp1_section(FF,x,u)[y][v] :
//     homd_int(id_E)[x](u)[y](v)
//       ->^(HomPsh_Z(x)[y]) homd_int(FF)[x](FF[x](u))[y](v).
//
// Canonical comment syntax:
//   fdapp1_int(FF)[x,u][y,v] :
//     Hom_E(E[—](u),v) => Hom_D(D[—](FF[x](u)),FF[y](v)).
//
// The ambient category is written directly as `Hom_K(x,y)^op ⊢ Cat`, rather
// than through `Fibre_cat(HomPresheaf_Z(x),y)`. This is the canonical endpoint
// category of the HomPresheaf classifier and avoids making later projections
// depend on unfolding the whole classifier pipeline.
symbol fdapp1_int_presheaf_arrow [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj K))
  (v : τ (Obj (Fibre_cat E y)))
  : τ (Hom
      (Functor_cat (Op_cat (Hom_cat K x y)) Cat_cat)
      (fapp0 (homd_id_tgt_func E x u y) v)
      (fapp0 (homd_ff_tgt_func FF x u y) v));

// Third projection fold for identity-specialized displayed hom-action.
//
// Surface/formula:
//   fdapp1_int_tgt_arrow(FF,x,u,y)[v]
//     = fdapp1_int_presheaf_arrow(FF,x,u,y,v).
rule @tapp0_fapp0
      _
      _
      _
      _
      $v
      (@fdapp1_int_tgt_arrow $K $E $D $FF $x $u $y)
  ↪ @fdapp1_int_presheaf_arrow $K $E $D $FF $x $u $y $v;

// Full hom-action of a Sigma map between fixed endpoints.
//
// The hom category of a Sigma total is stored as the opposite of a dependent
// Sigma over the opposite base hom. Therefore the functor-level action is the
// opposite of the Sigma map induced by the internal displayed-hom projection:
//   (p,alpha) |-> (p, fdapp1_int(FF)[x,u][y,v][p][alpha]).
rule @fapp1_func
      _
      _
      (@sigma_map_func $K $E $D $FF)
      (Struct_sigma $x $u)
      (Struct_sigma $y $v)
  ↪ @Op_func
      (@Sigma_cat
        (Op_cat (Hom_cat $K $x $y))
        (fapp0 (@homd_id_tgt_func $K $E $x $u $y) $v))
      (@Sigma_cat
        (Op_cat (Hom_cat $K $x $y))
        (fapp0 (@homd_ff_tgt_func $K $E $D $FF $x $u $y) $v))
      (@sigma_map_func
        (Op_cat (Hom_cat $K $x $y))
        (fapp0 (@homd_id_tgt_func $K $E $x $u $y) $v)
        (fapp0 (@homd_ff_tgt_func $K $E $D $FF $x $u $y) $v)
        (@fdapp1_int_presheaf_arrow $K $E $D $FF $x $u $y $v));

// Fourth projection stage, with endpoints written directly through `homd_`.
//
// Mathematical notation:
//   fdapp1_int(FF)[x,u][y,v][p] :
//     homd_(id_E,x,u,y,v)[p]
//       ⊢ homd_(FF,x,FF[x](u),y,v)[p].
//
// Canonical comment syntax:
//   fdapp1_int(FF)[x,u][y,v][p].
//
// This deliberately keeps the endpoints at the stable `homd_` layer. A later
// fold/assertion can expose the simplified fibre-hom category
// `Hom_{D[y]}(D[p](FF[x](u)),FF[y](v))` when a theorem needs that shape.
symbol fdapp1_int_hom_func [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y)))
  : τ (Hom
      Cat_cat
      (fapp0
        (homd_
          (@id_funcd K E)
          x
          u
          y
          v)
        p)
      (fapp0
        (homd_
          FF
          x
          (fapp0 (Fibre_func FF x) u)
          y
          v)
        p));

// Fourth projection fold by evaluating the presheaf arrow at p.
//
// Surface/formula:
//   fdapp1_int_presheaf_arrow(FF,x,u,y,v)[p]
//     = fdapp1_int_hom_func(FF,p,u,v).
rule @fapp1_fapp0
      _
      Cat_cat
      (@fapp0_func _ _ $p)
      _
      _
      (@fdapp1_int_presheaf_arrow $K $E $D $FF $x $u $y $v)
  ↪ @fdapp1_int_hom_func $K $E $D $FF $x $y $p $u $v;

// Equivalent transfor-component projection at p of the same presheaf arrow.
rule @tapp0_fapp0
      _
      Cat_cat
      _
      _
      $p
      (@fdapp1_int_presheaf_arrow $K $E $D $FF $x $u $y $v)
  ↪ @fdapp1_int_hom_func $K $E $D $FF $x $y $p $u $v;

// Final capped projection of identity-specialized displayed hom-action.
//
// Surface/formula:
//   fdapp1_int_hom_func(FF,p,u,v)[alpha]
//     = fdapp1_int_hom_fapp0(FF,p,u,alpha).
rule fapp0
      (@fdapp1_int_hom_func $K $E $D $FF $x $y $p $u $v)
      $alpha
  ↪ @fdapp1_int_hom_fapp0 $K $E $D $FF $x $y $p $u $v $alpha;

// 16c. Section action and displayed laxity cells
/*
  Full section action over a base arrow.

  Mathematical notation:
    s[f]                  = piapp1_fapp0 s f : E[f](s[x]) ->^(E[y]) s[y]
    piapp1_func(s,x,y)[f] = s[f].

  The section action is the terminal-source specialization of the displayed
  internal hom action, projected to the presheaf arrow level.
*/
symbol piapp1_func [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  (x y : τ (Obj K))
  : τ (Obj (Pi_cat
      (homd_
        (@id_funcd K E)
        x (@piapp0 K E s x)
        y (@piapp0 K E s y))))
≔ @fdapp1_int_presheaf_arrow
    K
    (@Const_catd K Terminal_cat)
    E
    s
    x
    Terminal_obj
    y
    Terminal_obj;

// Capped section action over a base arrow.
//
// Surface/formula:
//   piapp1_fapp0(s,f) = s[f] : E[f](s[x]) ->^(E[y]) s[y].
symbol piapp1_fapp0 [K : Cat] (E : τ (Catd K))
  (s : τ (Obj (Pi_cat E)))
  [x y : τ (Obj K)]
  (f : τ (Hom K x y))
  : τ (Hom
      (Fibre_cat E y)
      (@piapp1_src_obj K E s x y f)
      (@piapp0 K E s y))
≔ piapp0 (@piapp1_func K E s x y) f;

// Raw canonical-triangle cell extracted from the internal displayed hom-action.
// This is the stable component-level displayed laxity normal form.
// The concrete transported-object identity is consumed directly by the
// `fdapp1_int_hom_fapp0` rule below.
//
// Mathematical notation:
//   fdapp1_int(FF)[x,u][y,E[p]u][p](id)
//     : D[p](FF[x](u)) ->^(D[y]) FF[y](E[p](u)).
//
// Canonical comment syntax:
//   fdapp1_int(FF)[x,u][y,E[p]u][p](id).
symbol fdapp1_int_cell [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x)))
  : τ (Hom
      (Fibre_cat D y)
      (fapp0 (functord_transport_lhs_func FF p) u)
      (fapp0 (functord_transport_rhs_func FF p) u));

// Canonical transported-identity fibre arrow exposes the displayed laxity cell.
//
// Surface/formula:
//   fdapp1_int(FF)[x,u][y,E[p]u][p](id) ↪ fdapp1_int_cell(FF,p,u).
rule @fdapp1_int_hom_fapp0 $K $E $D $FF $x $y $p $u _ (@id _ _)
  ↪ @fdapp1_int_cell $K $E $D $FF $x $y $p $u;

// Terminal-source specialization of the transported-identity laxity fold.
rule @fdapp1_int_hom_fapp0
      $K (@Const_catd $K Terminal_cat) $D $FF $x $y $p
      Terminal_obj Terminal_obj Terminal_obj
  ↪ @fdapp1_int_cell
      $K
      (@Const_catd $K Terminal_cat)
      $D
      $FF
      $x
      $y
      $p
      Terminal_obj;

// Componentwise internalized laxity cell of displayed product pairing.
// This is the fdapp1_int_cell projection of the existing
// Product_pair_funcd owner, not a new displayed-product constructor.
rule @fdapp1_int_cell
      $K
      $E
      _
      (@Product_pair_funcd $K $E $B $C $FF $GG)
      $x
      $y
      $p
      $u
  ↪ @Product_pair
      (Hom_cat
        (Fibre_cat $B $y)
        (@fapp0
          (Fibre_cat $E $x)
          (Fibre_cat $B $y)
          (@functord_transport_lhs_func $K $E $B $FF $x $y $p)
          $u)
        (@fapp0
          (Fibre_cat $E $x)
          (Fibre_cat $B $y)
          (@functord_transport_rhs_func $K $E $B $FF $x $y $p)
          $u))
      (Hom_cat
        (Fibre_cat $C $y)
        (@fapp0
          (Fibre_cat $E $x)
          (Fibre_cat $C $y)
          (@functord_transport_lhs_func $K $E $C $GG $x $y $p)
          $u)
        (@fapp0
          (Fibre_cat $E $x)
          (Fibre_cat $C $y)
          (@functord_transport_rhs_func $K $E $C $GG $x $y $p)
          $u))
      (@fdapp1_int_cell $K $E $B $FF $x $y $p $u)
      (@fdapp1_int_cell $K $E $C $GG $x $y $p $u);

// Section-action projection for the explicit Sigma uncurrying wrapper.
// Action over (p,alpha) is the underlying internalized displayed-functor
// action on alpha.
// lhs-audit: keep 1,2,3 -- the Sigma base, terminal source family, and
// projection-pullback target family guard the uncurrying action.
rule @fdapp1_int_cell
      (@Sigma_cat $K $R)
      (@Const_catd (@Sigma_cat $K $R) Terminal_cat)
      (@Sigma_proj1_pullback_catd $K $R $D)
      (@sigma_functord_sec $K $R $D $FF)
      (Struct_sigma $x $u)
      (Struct_sigma $y $v)
      (Struct_sigma $p $alpha)
      Terminal_obj
  ↪ @fdapp1_int_hom_fapp0
      $K $R $D $FF $x $y $p $u $v $alpha;

// 16d. Arbitrary displayed-transfor hom-action projections
/*
  Generic displayed internal-hom action projections.

  These are the arbitrary displayed-transfor counterparts of the
  identity-specialized `fdapp1_int_*` extraction path.

  Mathematical notation:
    epsilon : FF => GG
    homd_tdapp1_src_sec(FF,GG,x,u)
      = homd_int(GG)[x](FF[x](u))

    tdapp1_int_section_arrow(epsilon,x,u)
      : homd_int(id_E)[x](u)
          ->^(HomdTarget_E[x]) homd_int(GG)[x](FF[x](u))

    tdapp1_int_cell(epsilon,p,u)
      : D[p](FF[x](u)) ->^(D[y]) GG[y](E[p](u)).

  Canonical comment syntax:
    epsilon[p][u] : D[p](FF[x](u)) ->^(D[y]) GG[y](E[p](u))

  The rules below project this cell through the same stages as
  `fdapp1_int_*`: section at x,u; target y; fibre object v; base arrow p; then
  the identity fibre arrow. When epsilon is the displayed identity, these heads
  fold back to the corresponding `fdapp1_int_*` normal forms.
*/
// Source dependent-hom section for an arbitrary displayed transfor.
//
// Surface/formula:
//   homd_tdapp1_src_sec(FF,GG,x,u)
//     = homd_int(GG)[x](FF[x](u)).
symbol homd_tdapp1_src_sec [K : Cat] [E D : τ (Catd K)]
  [FF GG : τ (Functord E D)]
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  : τ (Obj (Pi_cat (Homd_target_section_catd E x)))
≔ @homd_src_sec
    K
    E
    D
    GG
    x
    (fapp0 (@Fibre_func K E D FF x) u);

// y-component of the arbitrary displayed-transfor dependent-hom target.
//
// Surface/formula:
//   homd_tdapp1_tgt_func(FF,GG,x,u,y)
//     = homd_tdapp1_src_sec(FF,GG,x,u)[y].
symbol homd_tdapp1_tgt_func [K : Cat] [E D : τ (Catd K)]
  [FF GG : τ (Functord E D)]
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj K))
  : τ (Functor
      (Fibre_cat E y)
      (Functor_cat (Op_cat (Hom_cat K x y)) Cat_cat))
≔ piapp0 (@homd_tdapp1_src_sec K E D FF GG x u) y;

// First projection of arbitrary displayed hom-action.
//
// Surface/formula:
//   tdapp1_int_section_arrow(epsilon,x,u)
//     : homd_int(id_E)[x](u) ->^(HomdTarget_E[x]) homd_int(GG)[x](FF[x](u)).
symbol tdapp1_int_section_arrow [K : Cat] [E D : τ (Catd K)]
  [FF GG : τ (Functord E D)]
  (ϵ : τ (Transfd FF GG))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  : τ (Hom
      (Fibre_cat (Homd_target_catd E) x)
      (homd_id_src_sec E x u)
      (@homd_tdapp1_src_sec K E D FF GG x u));

// First projection fold for arbitrary displayed hom-action.
//
// Surface/formula:
//   tdapp1_int_fapp0_transfd(epsilon)[x][u]
//     = tdapp1_int_section_arrow(epsilon,x,u).
rule @tapp0_fapp0
      _
      _
      _
      _
      $u
      (@tdapp0_fapp0
        $K
        _
        _
        _
        _
        $x
        (@tdapp1_int_fapp0_transfd $K $E $D $FF $GG $ϵ))
  ↪ @tdapp1_int_section_arrow $K $E $D $FF $GG $ϵ $x $u;

// Displayed identity folds arbitrary section-arrow action to fdapp1.
rule @tdapp1_int_section_arrow
      $K $E $D $FF $FF (@id (@Functord_cat $K $E $D) $FF) $x $u
  ↪ @fdapp1_int_section_arrow $K $E $D $FF $x $u
with @tdapp1_int_section_arrow
      $K $E $D $FF $FF (@id (@Transf_cat $K Cat_cat $E $D) $FF) $x $u
  ↪ @fdapp1_int_section_arrow $K $E $D $FF $x $u;

// Second projection of arbitrary displayed hom-action at y.
//
// Surface/formula:
//   tdapp1_int_tgt_arrow(epsilon,x,u,y)
//     : homd_int(id_E)[x](u)[y] => homd_int(GG)[x](FF[x](u))[y].
symbol tdapp1_int_tgt_arrow [K : Cat] [E D : τ (Catd K)]
  [FF GG : τ (Functord E D)]
  (ϵ : τ (Transfd FF GG))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj K))
  : τ (Transf
      (homd_id_tgt_func E x u y)
      (@homd_tdapp1_tgt_func K E D FF GG x u y));

// Second projection fold for arbitrary displayed hom-action.
//
// Surface/formula:
//   tdapp1_int_section_arrow(epsilon,x,u)[y]
//     = tdapp1_int_tgt_arrow(epsilon,x,u,y).
rule @tapp0_fapp0
      _
      _
      _
      _
      Terminal_obj
      (@tdapp0_fapp0
        _
        _
        _
        _
        _
        $y
        (@tdapp1_int_section_arrow $K $E $D $FF $GG $ϵ $x $u))
  ↪ @tdapp1_int_tgt_arrow $K $E $D $FF $GG $ϵ $x $u $y;

// Displayed identity folds arbitrary target-arrow action to fdapp1.
rule @tdapp1_int_tgt_arrow
      $K $E $D $FF $FF (@id (@Functord_cat $K $E $D) $FF) $x $u $y
  ↪ @fdapp1_int_tgt_arrow $K $E $D $FF $x $u $y
with @tdapp1_int_tgt_arrow
      $K $E $D $FF $FF (@id (@Transf_cat $K Cat_cat $E $D) $FF) $x $u $y
  ↪ @fdapp1_int_tgt_arrow $K $E $D $FF $x $u $y;

// Third projection of arbitrary displayed hom-action at fibre object v.
//
// Surface/formula:
//   tdapp1_int_presheaf_arrow(epsilon,x,u,y,v)
//     : Hom_E(E[—](u),v) => Hom_D(D[—](FF[x](u)),GG[y](v)).
symbol tdapp1_int_presheaf_arrow [K : Cat] [E D : τ (Catd K)]
  [FF GG : τ (Functord E D)]
  (ϵ : τ (Transfd FF GG))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj K))
  (v : τ (Obj (Fibre_cat E y)))
  : τ (Hom
      (Functor_cat (Op_cat (Hom_cat K x y)) Cat_cat)
      (fapp0 (homd_id_tgt_func E x u y) v)
      (fapp0 (@homd_tdapp1_tgt_func K E D FF GG x u y) v));

// Third projection fold for arbitrary displayed hom-action.
//
// Surface/formula:
//   tdapp1_int_tgt_arrow(epsilon,x,u,y)[v]
//     = tdapp1_int_presheaf_arrow(epsilon,x,u,y,v).
rule @tapp0_fapp0
      _
      _
      _
      _
      $v
      (@tdapp1_int_tgt_arrow $K $E $D $FF $GG $ϵ $x $u $y)
  ↪ @tdapp1_int_presheaf_arrow $K $E $D $FF $GG $ϵ $x $u $y $v;

// Displayed identity folds arbitrary presheaf-arrow action to fdapp1.
rule @tdapp1_int_presheaf_arrow
      $K $E $D $FF $FF
      (@id (@Functord_cat $K $E $D) $FF)
      $x $u $y $v
  ↪ @fdapp1_int_presheaf_arrow $K $E $D $FF $x $u $y $v
with @tdapp1_int_presheaf_arrow
      $K $E $D $FF $FF
      (@id (@Transf_cat $K Cat_cat $E $D) $FF)
      $x $u $y $v
  ↪ @fdapp1_int_presheaf_arrow $K $E $D $FF $x $u $y $v;

// Fourth projection of arbitrary displayed hom-action at base arrow p.
//
// Surface/formula:
//   tdapp1_int_hom_func(epsilon,p,u,v)
//     : homd_(id_E,x,u,y,v)[p] ⊢ homd_(GG,x,FF[x](u),y,v)[p].
symbol tdapp1_int_hom_func [K : Cat] [E D : τ (Catd K)]
  [FF GG : τ (Functord E D)]
  (ϵ : τ (Transfd FF GG))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y)))
  : τ (Hom
      Cat_cat
      (fapp0
        (homd_
          (@id_funcd K E)
          x
          u
          y
          v)
        p)
      (fapp0
        (homd_
          GG
          x
          (fapp0 (Fibre_func FF x) u)
          y
          v)
        p));

// Fourth projection fold by evaluating the arbitrary presheaf arrow at p.
rule @fapp1_fapp0
      _
      Cat_cat
      (@fapp0_func _ _ $p)
      _
      _
      (@tdapp1_int_presheaf_arrow $K $E $D $FF $GG $ϵ $x $u $y $v)
  ↪ @tdapp1_int_hom_func $K $E $D $FF $GG $ϵ $x $y $p $u $v;

// Equivalent transfor-component projection at p for arbitrary epsilon.
rule @tapp0_fapp0
      _
      Cat_cat
      _
      _
      $p
      (@tdapp1_int_presheaf_arrow $K $E $D $FF $GG $ϵ $x $u $y $v)
  ↪ @tdapp1_int_hom_func $K $E $D $FF $GG $ϵ $x $y $p $u $v;

// Displayed identity folds arbitrary hom-action at p to fdapp1.
rule @tdapp1_int_hom_func
      $K $E $D $FF $FF
      (@id (@Functord_cat $K $E $D) $FF)
      $x $y $p $u $v
  ↪ @fdapp1_int_hom_func $K $E $D $FF $x $y $p $u $v
with @tdapp1_int_hom_func
      $K $E $D $FF $FF
      (@id (@Transf_cat $K Cat_cat $E $D) $FF)
      $x $y $p $u $v
  ↪ @fdapp1_int_hom_func $K $E $D $FF $x $y $p $u $v;

// Canonical transported-identity cell for an arbitrary displayed transfor.
//
// Surface/formula:
//   tdapp1_int_cell(epsilon,p,u)
//     : D[p](FF[x](u)) ->^(D[y]) GG[y](E[p](u)).
symbol tdapp1_int_cell [K : Cat] [E D : τ (Catd K)]
  [FF GG : τ (Functord E D)]
  (ϵ : τ (Transfd FF GG))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x)))
  : τ (Hom
      (Fibre_cat D y)
      (fapp0 (functord_transport_lhs_func FF p) u)
      (fapp0 (functord_transport_rhs_func GG p) u));

// Final capped projection for arbitrary displayed hom-action.
//
// Surface/formula:
//   tdapp1_int_hom_func(epsilon,p,u,E[p]u)(id)
//     = tdapp1_int_cell(epsilon,p,u).
rule fapp0 (@tdapp1_int_hom_func $K $E $D $FF $GG $ϵ $x $y $p $u _) (@id _ _)
  ↪ @tdapp1_int_cell $K $E $D $FF $GG $ϵ $x $y $p $u;

// Displayed identity folds arbitrary component cell to fdapp1.
rule @tdapp1_int_cell
      $K $E $D $FF $FF (@id (@Functord_cat $K $E $D) $FF) $x $y $p $u
  ↪ @fdapp1_int_cell $K $E $D $FF $x $y $p $u
with @tdapp1_int_cell
      $K $E $D $FF $FF (@id (@Transf_cat $K Cat_cat $E $D) $FF) $x $y $p $u
  ↪ @fdapp1_int_cell $K $E $D $FF $x $y $p $u;

// 16e. Strict/cartesian and terminal-source specializations

// Proof-time comparison only: terminal-source displayed laxity agrees with
// ordinary functor arrow action. Neither side is selected as a runtime fold.
//
// Surface/formula:
//   fdapp1_int_cell(s,p,*) ≡ s[p].
unif_rule
  @fdapp1_int_cell
    $K (@Const_catd $K Terminal_cat) (@Const_catd $K $A)
    $s $x $y $p Terminal_obj
  ≡ @fapp1_fapp0 $K $A $s $x $y $p
  ↪ [ tt ≡ tt ];

// Transparent theorem exposing the terminal-source proof-time comparison.
// Its reflexive body exercises the unification rule; this is not runtime beta.
symbol terminal_fdapp1_int_cell_eq
  [K A : Cat]
  (s : τ (Functord
      (@Const_catd K Terminal_cat)
      (@Const_catd K A)))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  : τ (@=
      (Hom A
        (@fapp0 K A s x)
        (@fapp0 K A s y))
      (@fdapp1_int_cell
        K
        (@Const_catd K Terminal_cat)
        (@Const_catd K A)
        s x y p Terminal_obj)
      (@fapp1_fapp0 K A s x y p))
≔ @eq_refl
    (Hom A
      (@fapp0 K A s x)
      (@fapp0 K A s y))
    (@fapp1_fapp0 K A s x y p);

// Constant-section arrow action agrees propositionally with ordinary functor
// action. The section projection computes to `fdapp1_int_cell`; the preceding
// proof-time comparison supplies the final ordinary view.
symbol piapp1_const_fapp0_eq
  [K A : Cat]
  (s : τ (Obj (Pi_cat (@Const_catd K A))))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  : τ (@=
      (Hom A
        (@fapp0 K A s x)
        (@fapp0 K A s y))
      (@piapp1_fapp0 K (@Const_catd K A) s x y p)
      (@fapp1_fapp0 K A s x y p))
≔ @terminal_fdapp1_int_cell_eq K A s x y p;

// Representable precomposition is strict/cartesian: its displayed laxity
// component is the identity at the composite arrow. The rule keys on the
// generic `hom_int_precomp_func(id,...)` owner and keeps the family slots
// implicit.
rule @fdapp1_int_cell
      $Z _ _
      (@hom_int_precomp_func $Z $Z (@id Cat_cat $Z) $y $x $p)
      $y $z $q (@id $Z $y)
  ↪ @id
      (Hom_cat $Z $x $z)
      (@hom_precomp_along_fapp0
        $Z $Z (@id Cat_cat $Z) $z $x $y $p $q);

// Representable precomposition is strict/cartesian already at the Sigma-map
// fibre projection: applying the internal-hom action to the canonical identity
// fibre arrow gives the identity at the composite arrow.
rule @fdapp1_int_hom_fapp0
      $Z _ _
      (@hom_int_precomp_func $Z $Z (@id Cat_cat $Z) $y $x $p)
      $y $z $q
      (@id $Z $y) $q (@id (Hom_cat $Z $y $z) $q)
  ↪ @id
      (Hom_cat $Z $x $z)
      (@hom_precomp_along_fapp0
        $Z $Z (@id Cat_cat $Z) $z $x $y $p $q);


// -------------------------------------------------------------------------------------------------
// 17. Generic Sigma/Pi weakening, ordinary structural logic, and delayed projection helpers
// -------------------------------------------------------------------------------------------------

/*
  Generic Sigma/Pi weakening/evaluation helpers.

    sigma_intro_transf(E)             : E ⊢ const(ΣE)
    sigma_intro_tapp0_func(E,k)       : E[k] ⊢ ΣE
    sigma_intro_tapp0_func(E,k)(u)    = (k,u)

    pi_eval_transf(E)                 : const(ΠE) ⊢ E
    pi_eval_transf(E)[k]              = piapp0_func(E,k) : ΠE ⊢ E[k]

    const_section_func(K,A)           : A ⊢ Π (k :^n K), A
    const_section_func(K,A)(a)        = const(a)

    section_pullback_func(F,E)        : Π_B E ⊢ Π_A F^*E
    section_pullback_func(F,E)(s)[a]  = s[F[a]]

  The arrow action of `sigma_intro_tapp0_func` is intentionally deferred. It
  should eventually send a fibre arrow α : u ->^(E[k]) v to the corresponding
  total arrow (id_k, α), but the clean rule needs the identity/fibre-transport
  normal forms for Sigma homs.

  `section_pullback_func` remains the current surface helper. A future internal
  version should be `section_pullback_int`, indexed over the functor argument F,
  with the pullback-family functor built from `comp_cat_cov_func E` and then
  composed with `Pi_func`, in the same style as the remaining `homd_int` and
  displayed-action projection packages.
*/

// 17a. Generic Sigma/Pi introduction and evaluation

// Generic Sigma helper: include a fibre object as a total object.
//
// Surface/formula:
//   sigma_intro_transf(E)[k](u) = (k,u).
injective symbol sigma_intro_transf [K : Cat] (E : τ (Catd K))
  : τ (Functord E (@Const_catd K (@Sigma_cat K E)));

// Component of `sigma_intro_transf` at k.
//
// Surface/formula:
//   sigma_intro_tapp0_func(E,k)(u) = (k,u).
symbol sigma_intro_tapp0_func [K : Cat] (E : τ (Catd K)) (k : τ (Obj K))
  : τ (Functor (Fibre_cat E k) (Sigma_cat E));

// Component projection: sigma_intro_transf(E)[k] ↪ sigma_intro_tapp0_func(E,k).
rule @tapp0_fapp0
      $K Cat_cat $E _ $k (@sigma_intro_transf $K $E)
  ↪ @sigma_intro_tapp0_func $K $E $k;

// Object introduction into the total category: u ↦ (k,u).
rule fapp0 (@sigma_intro_tapp0_func $K $E $k) $u
  ↪ Struct_sigma $k $u;

// Generic Pi helper: evaluation transfor from a constant section to a family.
//
// Surface/formula:
//   pi_eval_transf(E)[k] = piapp0_func(E,k).
injective symbol pi_eval_transf [K : Cat] (E : τ (Catd K))
  : τ (Functord
      (@Const_catd K (@Pi_cat K E))
      E);

// LHS indexing guard: this source family is reconstructible from
// `pi_eval_transf`, but replacing it with `_` makes bounded kernel checking
// exceed 30 seconds. Keep it explicit as a decision-tree discriminator.
// lhs-audit: keep 3 -- measured decision-tree performance guard
rule @tapp0_fapp0
      $K Cat_cat
      (@Const_catd $K (@Pi_cat $K $E))
      $E $k
      (@pi_eval_transf $K $E)
  ↪ @piapp0_func $K $E $k;

// Reusable displayed weakening to the constant terminal family.
//
// Surface/formula:
//   Terminal_funcd(E) : E ⊢_K const_K(1)
//   Terminal_funcd(E)[k] = Terminal_func(E[k]).
//
// Composing this owner with Const_func(a) derives a coherent constant map
// from any displayed source.  In particular it supplies the fixed argument
// of Eval_funcd without a specialized third evaluation owner.
injective symbol Terminal_funcd [K : Cat] (E : τ (Catd K))
  : τ (Functord E (@Const_catd K Terminal_cat));

// Point component of displayed terminal weakening.
rule @tapp0_fapp0 _ Cat_cat _ _ $k (@Terminal_funcd _ $E)
  ↪ Terminal_func (Fibre_cat $E $k);

// 17b. Constant sections and delayed product-pair telescope rules
//
// Fixed-base layer: constant section constructor.
//
// Surface/formula:
//   const_section_func(K,A)(a) = (k :^n K) ↦ a
//   as an object of Π k :^n K, A.
injective symbol const_section_func (K : Cat) (A : Cat)
  : τ (Functor A (@Pi_cat K (@Const_catd K A)));

// Displayed hom action of the constant-section constructor.
//
// Surface/formula:
//   Const_transfd_func(K,A,x,y) : Hom_A(x,y) ⊢ const(x) =>_[K] const(y).
injective symbol Const_transfd_func [K A : Cat] [x y : τ (Obj A)]
  : τ (Functor
      (Hom_cat A x y)
      (@Transfd_cat
        K
        (@Const_catd K Terminal_cat)
        (@Const_catd K A)
        (@Const_func K A x)
        (@Const_func K A y)));

// Displayed constant transformation selected by p.
injective symbol Const_transfd [K A : Cat] [x y : τ (Obj A)]
  (p : τ (Hom A x y))
  : τ (@Transfd
      K
      (@Const_catd K Terminal_cat)
      (@Const_catd K A)
      (@Const_func K A x)
      (@Const_func K A y));

// Object action: const_section_func(K,A)[a] ↪ const_K(a).
rule @fapp0 $A _ (@const_section_func $K $A) $a ↪ @Const_func $K $A $a;

// Hom-functor action stays in the displayed next-hom facade.
rule @fapp1_func $A _ (@const_section_func $K $A) $x $y
  ↪ @Const_transfd_func $K $A $x $y;

// Capped arrow action: p ↦ the displayed constant transfor.
rule @fapp1_fapp0 $A _ (@const_section_func $K $A) $x $y $p
  ↪ @Const_transfd $K $A $x $y $p;

// Fibre component of a displayed constant transfor: the ordinary constant
// transfor on the terminal source fibre.
// lhs-audit: keep 2,3,4,5 -- measured section-facade component discriminators
rule @tdapp0_fapp0
      $K
      (@Const_catd $K Terminal_cat)
      (@Const_catd $K $A)
      (@Const_func $K $A $x)
      (@Const_func $K $A $y)
      $_
      (@Const_transfd $K $A $x $y $p)
  ↪ @Const_transf Terminal_cat $A $x $y $p;

// Pairing telescope for products.
//
// Surface/formula:
//   Product_pair_tele_func(A,B) : A ⊢ (B ⊢ A × B)
//   Product_pair_tele_func[x][y] = (x,y)
//   Product_pair_tele_func[p][y] = (p,id_y).
rule sigma_Fst (@Product_pair_tele_func $A $B) ↪ @const_section_func $B $A;

// Second telescope projection is constantly id_B.
rule sigma_Snd (@Product_pair_tele_func $A $B) ↪ @Const_func $A (Functor_cat $B $B) (@id_func $B);

// Object projection: Product_pair_tele_func[x] ↪ (const_B(x),id_B).
rule @fapp0 _ _
      (@Product_pair_tele_func $A $B) $x
  ↪ Struct_sigma (@Const_func $B $A $x) (@id_func $B);

// Hom-functor projection pairs constant-transfor action with constant id_{id_B}.
rule @fapp1_func _ _
      (@Product_pair_tele_func $A $B) $x $x'
  ↪ Struct_sigma
      (@Const_transf_func $B $A $x $x')
      (@Const_func
        (Hom_cat $A $x $x')
        (@Transf_cat $B $B (@id_func $B) (@id_func $B))
        (@id (Functor_cat $B $B) (@id_func $B)));

// Capped arrow action: Product_pair_tele_func[p] ↪ (const(p),id_{id_B}).
rule @fapp1_fapp0 _ _
      (@Product_pair_tele_func $A $B) $x $x' $p
  ↪ Struct_sigma
      (@Const_transf $B $A $x $x' $p)
      (@id (Functor_cat $B $B) (@id_func $B));

// 17c. Ordinary functor structural logic

/*
  Usual structural operations for nested ordinary functor categories.

  Surface/formula:
    Const_func_func(A,B) : B ⊢ (A ⊢ B)
    sym_func_func(A,B,C) : (A ⊢ (B ⊢ C)) ⊢ (B ⊢ (A ⊢ C))
    diag_func_func(A,C)  : (A ⊢ (A ⊢ C)) ⊢ (A ⊢ C)

  Ordinary weakening is a stable owner separate from the displayed
  `const_section_func` facade. Exchange and contraction are also stable heads
  because later displayed analogues should recognize these structural
  operations directly, rather than through product/curry encodings.
*/

// Stable weakening owner for ordinary functor categories. This does not fold
// through the proof-time-only constant-section facade.
//
// Surface/formula:
//   Const_func_func(A,B)[b] = const_A(b) : A ⊢ B.
injective symbol Const_func_func [A B : Cat]
  : τ (Functor B (Functor_cat A B));

// Object action of ordinary weakening.
// lhs-audit: keep 2 -- measured ordinary-weakening codomain discriminator
rule @fapp0 $B (Functor_cat $A $B) (@Const_func_func $A $B) $b
  ↪ @Const_func $A $B $b;

// Full hom action of ordinary weakening.
// lhs-audit: keep 2 -- measured ordinary-weakening codomain discriminator
rule @fapp1_func $B (Functor_cat $A $B) (@Const_func_func $A $B) $x $y
  ↪ @Const_transf_func $A $B $x $y;

// Capped arrow action of ordinary weakening.
// lhs-audit: keep 2 -- measured ordinary-weakening codomain discriminator
rule @fapp1_fapp0 $B (Functor_cat $A $B) (@Const_func_func $A $B) $x $y $p
  ↪ @Const_transf $A $B $x $y $p;

// Direct displayed weakening for a mixed functor source slot.
//
// Surface/formula:
//   Functor_catd_const_funcd(A,B) : B ⊢_K Functor_catd(A,B)
//   Functor_catd_const_funcd(A,B)[k] = Const_func_func(A[k],B[k]).
//
// This is the primary structural owner. Product/curry presentations are
// comparison forms rather than prerequisites of the direct binder.
injective symbol Functor_catd_const_funcd [K : Cat]
  [A : τ (Catd (Op_cat K))]
  [B : τ (Catd K)]
  : τ (Functord B (@Functor_catd K A B));

// Point component is ordinary functorial weakening in the fibre.
rule @tapp0_fapp0
      $K Cat_cat _ _ $k
      (@Functor_catd_const_funcd $K $A $B)
  ↪ @Const_func_func
      (Fibre_cat $A $k)
      (Fibre_cat $B $k);

// Full base action maps B[p] to postcomposition by the fibrewise constant-
// functor embedding at the target endpoint. The result remains a whole
// functor over Hom_K(x,y), so higher base cells remain iterable.
rule @tapp1_func
      $K Cat_cat _ _ $x $y
      (@Functor_catd_const_funcd $K $A $B)
  ↪ @comp_cat_fapp0
      (Hom_cat $K $x $y)
      (Functor_cat (Fibre_cat $B $x) (Fibre_cat $B $y))
      (Functor_cat
        (Fibre_cat $B $x)
        (Functor_cat (Fibre_cat $A $y) (Fibre_cat $B $y)))
      (@comp_cat_cov_func
        (Fibre_cat $B $x)
        (Fibre_cat $B $y)
        (Functor_cat (Fibre_cat $A $y) (Fibre_cat $B $y))
        (@Const_func_func
          (Fibre_cat $A $y)
          (Fibre_cat $B $y)))
      (@fapp1_func $K Cat_cat $B $x $y);

// Capped base action is the corresponding composite at p.
rule @tapp1_fapp0
      $K Cat_cat _ _ $x $y
      (@Functor_catd_const_funcd $K $A $B)
      $p
  ↪ @comp_cat_fapp0
      (Fibre_cat $B $x)
      (Fibre_cat $B $y)
      (Functor_cat (Fibre_cat $A $y) (Fibre_cat $B $y))
      (@Const_func_func
        (Fibre_cat $A $y)
        (Fibre_cat $B $y))
      (@fapp1_fapp0 $K Cat_cat $B $x $y $p);

// Exchange of two ordinary functor arguments.
//
// Surface/formula:
//   sym_func_func(A,B,C)[H][b][a] = H[a][b].
symbol sym_func_func [A B C : Cat]
  : τ (Functor
      (Functor_cat A (Functor_cat B C))
      (Functor_cat B (Functor_cat A C)));

// Object action of exchange.
//
// Surface/formula:
//   sym_func(H) : B ⊢ (A ⊢ C).
symbol sym_func [A B C : Cat]
  (H : τ (Functor A (Functor_cat B C)))
  : τ (Functor B (Functor_cat A C));

// Exchange evaluated at the B-object b.
//
// Surface/formula:
//   sym_fapp0_func(H,b)[a] = H[a][b].
symbol sym_fapp0_func [A B C : Cat]
  (H : τ (Functor A (Functor_cat B C)))
  (b : τ (Obj B))
  : τ (Functor A C);

// A-arrow action after exchange at fixed b.
//
// Surface/formula:
//   sym_fapp0_func(H,b)[p] = H[p][b].
symbol sym_fapp0_fapp1_func [A B C : Cat]
  (H : τ (Functor A (Functor_cat B C)))
  (b : τ (Obj B))
  [a a' : τ (Obj A)]
  : τ (Functor
      (Hom_cat A a a')
      (Hom_cat C
        (@fapp0 B C (@fapp0 A (Functor_cat B C) H a) b)
        (@fapp0 B C (@fapp0 A (Functor_cat B C) H a') b)));

// B-arrow action of the exchanged functor.
//
// Surface/formula:
//   sym_func(H)[q] : sym(H)[b] => sym(H)[b'].
symbol sym_fapp1_func [A B C : Cat]
  (H : τ (Functor A (Functor_cat B C)))
  [b b' : τ (Obj B)]
  : τ (Functor
      (Hom_cat B b b')
      (@Transf_cat
        A
        C
        (@sym_fapp0_func A B C H b)
        (@sym_fapp0_func A B C H b')));

// Capped B-arrow action of exchange.
//
// Surface/formula:
//   sym_tapp1_fapp0_transf(H,q)[a] = H[a][q].
symbol sym_tapp1_fapp0_transf [A B C : Cat]
  (H : τ (Functor A (Functor_cat B C)))
  [b b' : τ (Obj B)]
  (q : τ (Hom B b b'))
  : τ (Transf
      (@sym_fapp0_func A B C H b)
      (@sym_fapp0_func A B C H b'));

// Hom-action of exchange on ordinary transfors.
//
// Surface/formula:
//   sym_func_func[eta] : sym(H) => sym(K).
symbol sym_func_func_fapp1_func [A B C : Cat]
  [H K : τ (Functor A (Functor_cat B C))]
  : τ (Functor
      (@Transf_cat A (Functor_cat B C) H K)
      (@Transf_cat
        B
        (Functor_cat A C)
        (@sym_func A B C H)
        (@sym_func A B C K)));

// Capped hom-action of exchange on an ordinary transfor.
//
// Surface/formula:
//   sym_func_func_transf(eta)[b][a] = eta[a][b].
symbol sym_func_func_transf [A B C : Cat]
  [H K : τ (Functor A (Functor_cat B C))]
  (eta : τ (Transf H K))
  : τ (Transf
      (@sym_func A B C H)
      (@sym_func A B C K));

// Component of exchanged transfor at b.
//
// Surface/formula:
//   sym_transf_tapp0_transf(eta,b)[a] = eta[a][b].
symbol sym_transf_tapp0_transf [A B C : Cat]
  [H K : τ (Functor A (Functor_cat B C))]
  (eta : τ (Transf H K))
  (b : τ (Obj B))
  : τ (Transf
      (@sym_fapp0_func A B C H b)
      (@sym_fapp0_func A B C K b));

// Projection ladder for exchange: object action and hom-action.
rule @fapp0 _ _ (@sym_func_func $A $B $C) $H
  ↪ @sym_func $A $B $C $H;

// Hom-functor projection: exchange sends eta : H => K to sym(eta).
rule @fapp1_func _ _ (@sym_func_func $A $B $C) $H $K
  ↪ @sym_func_func_fapp1_func $A $B $C $H $K;

// Object projection of exchanged hom-action: eta ↦ sym_func_func_transf(eta).
rule fapp0 (@sym_func_func_fapp1_func $A $B $C $H $K) $eta
  ↪ @sym_func_func_transf $A $B $C $H $K $eta;

// Direct capped projection of the same exchanged transfor.
rule @fapp1_fapp0 _ _ (@sym_func_func $A $B $C) $H $K $eta
  ↪ @sym_func_func_transf $A $B $C $H $K $eta;

// Object and A-arrow action after exchange at fixed b.
rule @fapp0 _ _ (@sym_func $A $B $C $H) $b
  ↪ @sym_fapp0_func $A $B $C $H $b;

// Exchanged object action: sym(H)[b][a] ↪ H[a][b].
rule @fapp0 $A $C (@sym_fapp0_func $A $B $C $H $b) $a
  ↪ @fapp0 $B $C (@fapp0 $A (Functor_cat $B $C) $H $a) $b;

// A-arrow hom-action of sym(H)[b].
rule @fapp1_func $A $C (@sym_fapp0_func $A $B $C $H $b) $a $a'
  ↪ @sym_fapp0_fapp1_func $A $B $C $H $b $a $a';

// Capped A-arrow action: sym(H)[b][p] ↪ H[p][b].
rule fapp0 (@sym_fapp0_fapp1_func $A $B $C $H $b $a $a') $p
  ↪ @tapp0_fapp0
      $B
      $C
      (@fapp0 $A (Functor_cat $B $C) $H $a)
      (@fapp0 $A (Functor_cat $B $C) $H $a')
      $b
      (@fapp1_fapp0 $A (Functor_cat $B $C) $H $a $a' $p);

// Direct capped projection of the same A-arrow action.
rule @fapp1_fapp0 $A $C (@sym_fapp0_func $A $B $C $H $b) $a $a' $p
  ↪ @tapp0_fapp0
      $B
      $C
      (@fapp0 $A (Functor_cat $B $C) $H $a)
      (@fapp0 $A (Functor_cat $B $C) $H $a')
      $b
      (@fapp1_fapp0 $A (Functor_cat $B $C) $H $a $a' $p);

// B-arrow action after exchange and its mixed off-diagonal component.
rule @fapp1_func _ _ (@sym_func $A $B $C $H) $b $b'
  ↪ @sym_fapp1_func $A $B $C $H $b $b';

// Capped B-arrow action: sym(H)[q] ↪ (a ↦ H[a][q]).
rule fapp0 (@sym_fapp1_func $A $B $C $H $b $b') $q
  ↪ @sym_tapp1_fapp0_transf $A $B $C $H $b $b' $q;

// Direct capped projection of the same B-arrow action.
rule @fapp1_fapp0 _ _ (@sym_func $A $B $C $H) $b $b' $q
  ↪ @sym_tapp1_fapp0_transf $A $B $C $H $b $b' $q;

// Component at a: sym(H)[q][a] ↪ H[a][q].
rule @tapp0_fapp0
      $A
      $C
      _
      _
      $a
      (@sym_tapp1_fapp0_transf $A $B $C $H $b $b' $q)
  ↪ @fapp1_fapp0
      $B
      $C
      (@fapp0 $A (Functor_cat $B $C) $H $a)
      $b
      $b'
      $q;

// Mixed component: the (p,q)-cell of sym(H) is H[p][q].
rule @tapp1_fapp0
      $A
      $C
      _
      _
      $a
      $a'
      (@sym_tapp1_fapp0_transf $A $B $C $H $b $b' $q)
      $p
  ↪ @tapp1_fapp0
      $B
      $C
      (@fapp0 $A (Functor_cat $B $C) $H $a)
      (@fapp0 $A (Functor_cat $B $C) $H $a')
      $b
      $b'
      (@fapp1_fapp0 $A (Functor_cat $B $C) $H $a $a' $p)
      $q;

// Component projection for exchanged transfors.
// First component: sym(eta)[b] ↪ (a ↦ eta[a][b]).
rule @tapp0_fapp0
      _
      _
      _
      _
      $b
      (@sym_func_func_transf $A $B $C $H $K $eta)
  ↪ @sym_transf_tapp0_transf $A $B $C $H $K $eta $b;

// Second component: sym(eta)[b][a] ↪ eta[a][b].
rule @tapp0_fapp0
      $A
      $C
      _
      _
      $a
      (@sym_transf_tapp0_transf $A $B $C $H $K $eta $b)
  ↪ @tapp0_fapp0
      $B
      $C
      (@fapp0 $A (Functor_cat $B $C) $H $a)
      (@fapp0 $A (Functor_cat $B $C) $K $a)
      $b
      (@tapp0_fapp0 $A (Functor_cat $B $C) $H $K $a $eta);

// Contraction/diagonal for ordinary functor categories.
//
// Surface/formula:
//   diag_func_func(A,C)[H][a] = H[a][a].
symbol diag_func_func [A C : Cat]
  : τ (Functor
      (Functor_cat A (Functor_cat A C))
      (Functor_cat A C));

// Object action of contraction.
//
// Surface/formula:
//   diag_func(H) : A ⊢ C.
symbol diag_func [A C : Cat]
  (H : τ (Functor A (Functor_cat A C)))
  : τ (Functor A C);

// Arrow action of contraction.
//
// Surface/formula:
//   diag_func(H)[p] = H[p][p].
symbol diag_fapp1_func [A C : Cat]
  (H : τ (Functor A (Functor_cat A C)))
  [a a' : τ (Obj A)]
  : τ (Functor
      (Hom_cat A a a')
      (Hom_cat C
        (@fapp0 A C (@fapp0 A (Functor_cat A C) H a) a)
        (@fapp0 A C (@fapp0 A (Functor_cat A C) H a') a')));

// Hom-action of contraction on ordinary transfors.
//
// Surface/formula:
//   diag_func_func[eta] : diag(H) => diag(K).
symbol diag_func_func_fapp1_func [A C : Cat]
  [H K : τ (Functor A (Functor_cat A C))]
  : τ (Functor
      (@Transf_cat A (Functor_cat A C) H K)
      (@Transf_cat
        A
        C
        (@diag_func A C H)
        (@diag_func A C K)));

// Capped hom-action of contraction on an ordinary transfor.
//
// Surface/formula:
//   diag_func_func_transf(eta)[a] = eta[a][a].
symbol diag_func_func_transf [A C : Cat]
  [H K : τ (Functor A (Functor_cat A C))]
  (eta : τ (Transf H K))
  : τ (Transf
      (@diag_func A C H)
      (@diag_func A C K));

// Projection ladder for contraction: object action and hom-action.
rule @fapp0 _ _ (@diag_func_func $A $C) $H
  ↪ @diag_func $A $C $H;

// Hom-functor projection: diagonal sends eta : H => K to diag(eta).
rule @fapp1_func _ _ (@diag_func_func $A $C) $H $K
  ↪ @diag_func_func_fapp1_func $A $C $H $K;

// Object projection of diagonal hom-action: eta ↦ diag_func_func_transf(eta).
rule fapp0 (@diag_func_func_fapp1_func $A $C $H $K) $eta
  ↪ @diag_func_func_transf $A $C $H $K $eta;

// Direct capped projection of the same diagonal transfor.
rule @fapp1_fapp0 _ _ (@diag_func_func $A $C) $H $K $eta
  ↪ @diag_func_func_transf $A $C $H $K $eta;

// Object and arrow action of the diagonal functor.
rule @fapp0 $A $C (@diag_func $A $C $H) $a
  ↪ @fapp0 $A $C (@fapp0 $A (Functor_cat $A $C) $H $a) $a;

// Hom-functor projection for contraction at endpoints a,a'.
rule @fapp1_func $A $C (@diag_func $A $C $H) $a $a'
  ↪ @diag_fapp1_func $A $C $H $a $a';

// Capped diagonal action: diag(H)[p] ↪ H[p][p].
rule fapp0 (@diag_fapp1_func $A $C $H $a $a') $p
  ↪ @tapp1_fapp0
      $A
      $C
      (@fapp0 $A (Functor_cat $A $C) $H $a)
      (@fapp0 $A (Functor_cat $A $C) $H $a')
      $a
      $a'
      (@fapp1_fapp0 $A (Functor_cat $A $C) $H $a $a' $p)
      $p;

// Direct capped projection of the same diagonal arrow action.
rule @fapp1_fapp0 $A $C (@diag_func $A $C $H) $a $a' $p
  ↪ @tapp1_fapp0
      $A
      $C
      (@fapp0 $A (Functor_cat $A $C) $H $a)
      (@fapp0 $A (Functor_cat $A $C) $H $a')
      $a
      $a'
      (@fapp1_fapp0 $A (Functor_cat $A $C) $H $a $a' $p)
      $p;

// Component projection for contracted transfors.
rule @tapp0_fapp0
      $A
      $C
      _
      _
      $a
      (@diag_func_func_transf $A $C $H $K $eta)
  ↪ @tapp0_fapp0
      $A
      $C
      (@fapp0 $A (Functor_cat $A $C) $H $a)
      (@fapp0 $A (Functor_cat $A $C) $K $a)
      $a
      (@tapp0_fapp0 $A (Functor_cat $A $C) $H $K $a $eta);

// 17d. Generic ordinary functor hom-action
//
// Generic full hom-action for identity and composition of ordinary functors.
// These rules let semantic aliases such as curry expose functor-level action
// instead of falling back to capped `fapp1_fapp0` computation only.
rule @fapp1_func $A $A (@id Cat_cat $A) $x $y ↪ @id Cat_cat (Hom_cat $A $x $y);

// Hom-action of a composite: (F ∘ G)_1 ↪ F_1 ∘ G_1.
rule @fapp1_func $A $C (@comp_fapp0 Cat_cat $A $B $C $F $G) $x $y
  ↪ @comp_fapp0
      Cat_cat
      (Hom_cat $A $x $y)
      (Hom_cat $B
        (@fapp0 $A $B $G $x)
        (@fapp0 $A $B $G $y))
      (Hom_cat $C
        (@fapp0 $B $C $F (@fapp0 $A $B $G $x))
        (@fapp0 $B $C $F (@fapp0 $A $B $G $y)))
      (@fapp1_func
        $B
        $C
        $F
        (@fapp0 $A $B $G $x)
        (@fapp0 $A $B $G $y))
      (@fapp1_func $A $B $G $x $y);

// Stable pullback cut elimination and arrow projections. These are placed
// after the generic identity/composition action so competing paths can use
// those global rules while Lambdapi checks local confluence.
rule @Pullback_catd $A $A $E (@id Cat_cat $A) ↪ $E;
// Pullback of the universe identity along F is the family F itself.
rule @Pullback_catd $A Cat_cat (@id Cat_cat Cat_cat) $F ↪ $F;

// Pullback accumulation: H^*(F^*E) ↪ (F ∘ H)^*E.
rule @Pullback_catd
      $A $B
      (@Pullback_catd $B $C $E $F)
      $H
  ↪ @Pullback_catd
      $A $C
      $E
      (@comp_cat_fapp0 $A $B $C $F $H);

// Hom-action of F^*E is E_1 after the hom-action of F.
rule @fapp1_func _ Cat_cat (@Pullback_catd $A $B $E $F) $a $a'
  ↪ @comp_cat_fapp0
      (Hom_cat $A $a $a')
      (Hom_cat $B
        (@fapp0 $A $B $F $a)
        (@fapp0 $A $B $F $a'))
      (Functor_cat
        (@fapp0 $B Cat_cat $E (@fapp0 $A $B $F $a))
        (@fapp0 $B Cat_cat $E (@fapp0 $A $B $F $a')))
      (@fapp1_func
        $B
        Cat_cat
        $E
        (@fapp0 $A $B $F $a)
        (@fapp0 $A $B $F $a'))
      (@fapp1_func $A $B $F $a $a');

// Capped base-arrow transport: (F^*E)[p] ↪ E[F[p]].
rule @fapp1_fapp0 _ Cat_cat (@Pullback_catd $A $B $E $F) $a $a' $p
  ↪ @fapp1_fapp0
      $B
      Cat_cat
      $E
      (@fapp0 $A $B $F $a)
      (@fapp0 $A $B $F $a')
      (@fapp1_fapp0 $A $B $F $a $a' $p);

// Structured-arrow projection of pullback totalization:
//   (p,alpha) ↦ (F[p],alpha).
//
// This rule follows the capped Pullback_catd transport owner so the source
// endpoint of alpha is already visible to subject reduction. Restricting the
// argument to the canonical Sigma-arrow pair leaves arbitrary ordinary arrows
// under the generic functor action.
rule @fapp1_fapp0
      _
      _
      (@sigma_pullback_total_func $A $K $F $D)
      (Struct_sigma $a $u)
      (Struct_sigma $b $v)
      (Struct_sigma $p $alpha)
  ↪ @sigma_arrow
      $K
      $D
      (@fapp0 $A $K $F $a)
      (@fapp0 $A $K $F $b)
      $u
      $v
      (@fapp1_fapp0 $A $K $F $a $b $p)
      $alpha;

// Semantic curry sanity checks. These live after `Product_pair_tele_func`
// computation rules, because the primary curry package is a definition through
// that telescope rather than a primitive object-action rewrite rule.

// 17e. Section pullback and internal Pi action
//
// Internalized-x prerequisite: pull a section back along a base functor.
//
// Surface/formula:
//   section_pullback_func(F,E) :
//     (Π b :^n B, E[b]) ⊢ (Π a :^n A, E[F[a]])
//   section_pullback_func(F,E)(s)[a] = s[F[a]].
symbol section_pullback_func [A B : Cat]
  (F : τ (Functor A B)) (E : τ (Catd B))
  : τ (Functor
      (@Functord_cat B (@Const_catd B Terminal_cat) E)
      (@Functord_cat A (@Const_catd A Terminal_cat) (@Pullback_catd A B E F)));

// Fixed object-level section produced by `section_pullback_func`.
//
// Surface/formula:
//   section_pullback_sec(F,E,s)[a] = s[F[a]].
symbol section_pullback_sec [A B : Cat]
  (F : τ (Functor A B)) (E : τ (Catd B))
  (s : τ (Obj (@Functord_cat B (@Const_catd B Terminal_cat) E)))
  : τ (Obj (@Functord_cat A (@Const_catd A Terminal_cat) (@Pullback_catd A B E F)));

// Object action: section_pullback_func(F,E)[s] ↪ section_pullback_sec(F,E,s).
rule @fapp0 _ _ (@section_pullback_func $A $B $F $E) $s ↪ @section_pullback_sec $A $B $F $E $s;

// Component formula: section_pullback_sec(F,E,s)[a] ↪ s[F[a]].
rule @tapp0_fapp0
      $A Cat_cat _ _ $a
      (@section_pullback_sec $A $B $F $E $s)
  ↪ @Obj_func
      (Fibre_cat (@Pullback_catd $A $B $E $F) $a)
      (@piapp0 $B $E $s (@fapp0 $A $B $F $a));

// Direct displayed component of section weakening along a Sigma projection.
// At z, it is the constant fibre functor with value s[z].
// lhs-audit: keep 1,3,4 -- the fixed direct displayed endpoints are the
// projection-pullback uncurrying discriminator and subject-reduction guard.
rule @tapp0_fapp0
      $B
      Cat_cat
      $R
      $E
      $z
      (@section_pullback_sec
        (@Sigma_cat $B $R)
        $B
        (@Sigma_proj1_func $B $R)
        $E
        $s)
  ↪ @Const_func
      (Fibre_cat $R $z)
      (Fibre_cat $E $z)
      (@piapp0 $B $E $s $z);

// Base-arrow laxity component of the same direct displayed weakening. It is
// exactly the original section action, retained at the generic
// terminal-source displayed-laxity owner, and is independent of the
// source-fibre object.
// lhs-audit: keep 1,2,3 -- the direct displayed endpoints guard the
// projection-pullback uncurrying action.
rule @fdapp1_int_cell
      $B
      $R
      $E
      (@section_pullback_sec
        (@Sigma_cat $B $R)
        $B
        (@Sigma_proj1_func $B $R)
        $E
        $s)
      $z
      $z'
      $q
      _
  ↪ @fdapp1_int_cell
      $B
      (@Const_catd $B Terminal_cat)
      $E
      $s
      $z
      $z'
      $q
      Terminal_obj;

// Internalized-x prerequisite: naturality component of Pi along a base functor.
//
// Surface/formula:
//   section_pullback_transf(F)[E] = section_pullback_func(F,E)
//   : Π b :^n B, E[b] ⊢ Π a :^n A, E[F[a]].
injective symbol section_pullback_transf [A B : Cat]
  (F : τ (Functor A B))
  : τ (Transf
      (@Pi_func B)
      (@comp_cat_fapp0
        (@Catd_cat B)
        (@Catd_cat A)
        Cat_cat
        (@Pi_func A)
        (@Pullback_catd_func A B F)));

// Family component: section_pullback_transf(F)[E] ↪ section_pullback_func(F,E).
rule @tapp0_fapp0 _ Cat_cat _ _ $E (@section_pullback_transf $A $B $F)
  ↪ @section_pullback_func $A $B $F $E;

// Internal Pi action at F and E folds to ordinary section pullback.
rule @fdapp1_int_cell _ _ _ Pi_int_funcd $B $A $F $E
  ↪ @section_pullback_func $A $B $F $E;

// Pointwise internal Pi action along G[p] folds to section pullback.
rule @fdapp1_int_cell
      $K
      _
      _
      (@Pi_pullback_funcd $K $G)
      $x
      $y
      $p
      $E
  ↪ @section_pullback_func
      (@fapp0 $K (Op_cat Cat_cat) $G $y)
      (@fapp0 $K (Op_cat Cat_cat) $G $x)
      (@fapp1_fapp0 $K (Op_cat Cat_cat) $G $x $y $p)
      $E;


// 17f. Reusable contextual curry basis

// Positive dependent curry across one Sigma context extension. The source
// and target categories are already proof-time comparable, so the semantic
// operation is an opaque identity rather than a new primitive functor.
symbol sigma_functord_curry_func [K : Cat]
  [R D : τ (Catd K)]
  : τ (Functor
      (@Pi_cat
        (@Sigma_cat K R)
        (@Sigma_proj1_pullback_catd K R D))
      (@Functord_cat K R D))
≔ @id_func
    (@Pi_cat
      (@Sigma_cat K R)
      (@Sigma_proj1_pullback_catd K R D));

opaque sigma_functord_curry_func;

injective symbol sigma_functord_curry_sec [K : Cat]
  [R D : τ (Catd K)]
  (s : τ (Obj
    (@Pi_cat
      (@Sigma_cat K R)
      (@Sigma_proj1_pullback_catd K R D))))
  : τ (Functord R D);

rule @fapp0 _ _
      (@sigma_functord_curry_func $K $R $D) $s
  ↪ @sigma_functord_curry_sec $K $R $D $s;

injective symbol sigma_functord_curry_fibre_func [K : Cat]
  [R D : τ (Catd K)]
  (s : τ (Obj
    (@Pi_cat
      (@Sigma_cat K R)
      (@Sigma_proj1_pullback_catd K R D))))
  (k : τ (Obj K))
  : τ (Functor (Fibre_cat R k) (Fibre_cat D k));

rule @tapp0_fapp0 $K Cat_cat _ _ $k
      (@sigma_functord_curry_sec $K $R $D $s)
  ↪ @sigma_functord_curry_fibre_func $K $R $D $s $k;

rule @fapp0 _ _
      (@sigma_functord_curry_fibre_func $K $R $D $s $k) $r
  ↪ @piapp0
      (@Sigma_cat $K $R)
      (@Sigma_proj1_pullback_catd $K $R $D)
      $s
      (Struct_sigma $k $r);

// The fibre functor inherits section action along the identity-base Sigma
// arrow. This remains internally typed; no pointwise naturality evidence is
// supplied by the caller.
rule @fapp1_fapp0 _ _
      (@sigma_functord_curry_fibre_func $K $R $D $s $k)
      $r $r' $alpha
  ↪ @piapp1_fapp0
      (@Sigma_cat $K $R)
      (@Sigma_proj1_pullback_catd $K $R $D)
      $s
      (Struct_sigma $k $r)
      (Struct_sigma $k $r')
      (@sigma_arrow
        $K $R $k $k
        $r $r'
        (@id $K $k)
        $alpha);

// Base-arrow laxity is the section action on the canonical total transport.
rule @fdapp1_int_cell
      $K $R $D
      (@sigma_functord_curry_sec $K $R $D $s)
      $x $y $p $r
  ↪ @piapp1_fapp0
      (@Sigma_cat $K $R)
      (@Sigma_proj1_pullback_catd $K $R $D)
      $s
      (Struct_sigma $x $r)
      (Struct_sigma
        $y
        (@fapp0
          (Fibre_cat $R $x)
          (Fibre_cat $R $y)
          (@catd_transport_func $K $R $x $y $p)
          $r))
      (@sigma_transport_arrow $K $R $x $y $p $r);

// 17g. Variance-correct mixed displayed curry
//
// This qualified package keeps the existing Unit_prof/Hom action architecture
// and adds only the missing variance-correct section transposition.

symbol mix_neg_total [K : Cat]
  (A : τ (Catd (Op_cat K)))
  : Cat
≔ Op_cat
    (@Sigma_cat
      (Op_cat K)
      (@Op_catd (Op_cat K) A));

symbol mix_neg_base_func [K : Cat]
  (A : τ (Catd (Op_cat K)))
  : τ (Functor (@mix_neg_total K A) K)
≔ @Op_func
    (@Sigma_cat
      (Op_cat K)
      (@Op_catd (Op_cat K) A))
    (Op_cat K)
    (@Sigma_proj1_func
      (Op_cat K)
      (@Op_catd (Op_cat K) A));

symbol mix_context_family [K : Cat]
  (A : τ (Catd (Op_cat K)))
  (C : τ (Catd K))
  : τ (Catd (@mix_neg_total K A))
≔ @Pullback_catd
    (@mix_neg_total K A)
    K
    C
    (@mix_neg_base_func K A);

symbol mix_context_cat [K : Cat]
  (A : τ (Catd (Op_cat K)))
  (C : τ (Catd K))
  : Cat
≔ @Sigma_cat
    (@mix_neg_total K A)
    (@mix_context_family K A C);

symbol mix_context_base_func [K : Cat]
  (A : τ (Catd (Op_cat K)))
  (C : τ (Catd K))
  : τ (Functor (@mix_context_cat K A C) K)
≔ @comp_cat_fapp0
    (@mix_context_cat K A C)
    (@mix_neg_total K A)
    K
    (@mix_neg_base_func K A)
    (@Sigma_proj1_func
      (@mix_neg_total K A)
      (@mix_context_family K A C));

symbol mix_uncurried_family [K : Cat]
  (A : τ (Catd (Op_cat K)))
  (B C : τ (Catd K))
  : τ (Catd (@mix_context_cat K A C))
≔ @Sigma_proj1_pullback_catd
    (@mix_neg_total K A)
    (@mix_context_family K A C)
    (@mix_context_family K A B);

// Canonical negative part of a mixed arrow over p:k->k'.  The A-component is
// contravariant: alpha : a -> A[p](a').  Pointwise opposite plus total
// opposite packages it as an arrow (k,a) -> (k',a') without an external
// variance witness.
symbol mix_neg_arrow [K : Cat]
  [A : τ (Catd (Op_cat K))]
  [k k' : τ (Obj K)]
  (p : τ (Hom K k k'))
  (a : τ (Obj (Fibre_cat A k)))
  (a' : τ (Obj (Fibre_cat A k')))
  (alpha : τ (Obj (Hom_cat
      (Fibre_cat A k)
      a
      (@fapp0
        (Fibre_cat A k')
        (Fibre_cat A k)
        (@catd_transport_func (Op_cat K) A k' k p)
        a'))))
  : τ (Obj (Hom_cat
      (@mix_neg_total K A)
      (Struct_sigma k a)
      (Struct_sigma k' a')))
≔ @sigma_arrow
    (Op_cat K)
    (@Op_catd (Op_cat K) A)
    k'
    k
    a'
    a
    p
    alpha;

// Reusable negative-family curry. It abstracts the opposite-Sigma base
// independently of any surrounding positive Sigma section.
constant symbol neg_sigma_functord_curry_func
  [K : Cat]
  [A : τ (Catd (Op_cat K))]
  [X Y : τ (Catd K)]
  : τ (Functor
      (@Functord_cat
        (@mix_neg_total K A)
        (@mix_context_family K A X)
        (@mix_context_family K A Y))
      (@Functord_cat K X (@Functor_catd K A Y)));

injective symbol neg_sigma_functord_curry_funcd
  [K : Cat]
  [A : τ (Catd (Op_cat K))]
  [X Y : τ (Catd K)]
  (H : τ (Functord
    (@mix_context_family K A X)
    (@mix_context_family K A Y)))
  : τ (Functord X (@Functor_catd K A Y));

rule @fapp0 _ _
      (@neg_sigma_functord_curry_func $K $A $X $Y) $H
  ↪ @neg_sigma_functord_curry_funcd $K $A $X $Y $H;

injective symbol neg_sigma_functord_curry_fibre_func
  [K : Cat]
  [A : τ (Catd (Op_cat K))]
  [X Y : τ (Catd K)]
  (H : τ (Functord
    (@mix_context_family K A X)
    (@mix_context_family K A Y)))
  (k : τ (Obj K))
  : τ (Functor
      (Fibre_cat X k)
      (Functor_cat (Fibre_cat A k) (Fibre_cat Y k)));

rule @tapp0_fapp0 $K Cat_cat _ _ $k
      (@neg_sigma_functord_curry_funcd $K $A $X $Y $H)
  ↪ @neg_sigma_functord_curry_fibre_func $K $A $X $Y $H $k;

injective symbol neg_sigma_functord_curry_at_func
  [K : Cat]
  [A : τ (Catd (Op_cat K))]
  [X Y : τ (Catd K)]
  (H : τ (Functord
    (@mix_context_family K A X)
    (@mix_context_family K A Y)))
  (k : τ (Obj K))
  (x : τ (Obj (Fibre_cat X k)))
  : τ (Functor (Fibre_cat A k) (Fibre_cat Y k));

rule @fapp0 _ _
      (@neg_sigma_functord_curry_fibre_func $K $A $X $Y $H $k) $x
  ↪ @neg_sigma_functord_curry_at_func $K $A $X $Y $H $k $x;

rule @fapp0 _ _
      (@neg_sigma_functord_curry_at_func $K $A $X $Y $H $k $x) $a
  ↪ @fapp0
      (Fibre_cat $X $k)
      (Fibre_cat $Y $k)
      (@tapp0_fapp0
        (@mix_neg_total $K $A)
        Cat_cat
        (@mix_context_family $K $A $X)
        (@mix_context_family $K $A $Y)
        (Struct_sigma $k $a)
        $H)
      $x;

// Negative-fibre action is the internally owned base laxity of H.
rule @fapp1_fapp0 _ _
      (@neg_sigma_functord_curry_at_func $K $A $X $Y $H $k $x)
      $a $a' $alpha
  ↪ @fdapp1_int_cell
      (@mix_neg_total $K $A)
      (@mix_context_family $K $A $X)
      (@mix_context_family $K $A $Y)
      $H
      (Struct_sigma $k $a)
      (Struct_sigma $k $a')
      (@mix_neg_arrow
        $K $A $k $k (@id $K $k)
        $a $a' $alpha)
      $x;

// Positive-X action remains ordinary fibre action of H at the selected a.
rule @tapp0_fapp0 _ _ _ _ $a
      (@fapp1_fapp0
        (@fapp0 $K Cat_cat $X $k)
        (Functor_cat
          (@fapp0 (Op_cat $K) Cat_cat $A $k)
          (@fapp0 $K Cat_cat $Y $k))
        (@neg_sigma_functord_curry_fibre_func $K $A $X $Y $H $k)
        $x $x' $beta)
  ↪ @fapp1_fapp0
      (Fibre_cat $X $k)
      (Fibre_cat $Y $k)
      (@tapp0_fapp0
        (@mix_neg_total $K $A)
        Cat_cat
        (@mix_context_family $K $A $X)
        (@mix_context_family $K $A $Y)
        (Struct_sigma $k $a)
        $H)
      $x $x' $beta;

// Canonical negative-total arrow over p with identity fibre component.
symbol mix_neg_base_arrow [K : Cat]
  [A : τ (Catd (Op_cat K))]
  [k k' : τ (Obj K)]
  (p : τ (Hom K k k'))
  (a' : τ (Obj (Fibre_cat A k')))
  : τ (Hom
      (@mix_neg_total K A)
      (Struct_sigma
        k
        (@fapp0
          (Fibre_cat A k')
          (Fibre_cat A k)
          (@catd_transport_func (Op_cat K) A k' k p)
          a'))
      (Struct_sigma k' a'))
≔ @mix_neg_arrow
    K A k k' p
    (@fapp0
      (Fibre_cat A k')
      (Fibre_cat A k)
      (@catd_transport_func (Op_cat K) A k' k p)
      a')
    a'
    (@id
      (Fibre_cat A k)
      (@fapp0
        (Fibre_cat A k')
        (Fibre_cat A k)
        (@catd_transport_func (Op_cat K) A k' k p)
        a'));

// Base-arrow laxity of the curried displayed functor is inherited from H.
rule @tapp0_fapp0 _ _ _ _ $a'
      (@fdapp1_int_cell
        $K
        $X
        (@Functor_catd $K $A $Y)
        (@neg_sigma_functord_curry_funcd $K $A $X $Y $H)
        $k $k' $p $x)
  ↪ @fdapp1_int_cell
      (@mix_neg_total $K $A)
      (@mix_context_family $K $A $X)
      (@mix_context_family $K $A $Y)
      $H
      (Struct_sigma
        $k
        (@fapp0
          (Fibre_cat $A $k')
          (Fibre_cat $A $k)
          (@catd_transport_func (Op_cat $K) $A $k' $k $p)
          $a'))
      (Struct_sigma $k' $a')
      (@mix_neg_base_arrow $K $A $k $k' $p $a')
      $x;

symbol mix_context_arrow [K : Cat]
  [A : τ (Catd (Op_cat K))]
  [C : τ (Catd K)]
  [k k' : τ (Obj K)]
  (p : τ (Hom K k k'))
  (a : τ (Obj (Fibre_cat A k)))
  (a' : τ (Obj (Fibre_cat A k')))
  (alpha : τ (Obj (Hom_cat
      (Fibre_cat A k)
      a
      (@fapp0
        (Fibre_cat A k')
        (Fibre_cat A k)
        (@catd_transport_func (Op_cat K) A k' k p)
        a'))))
  (c : τ (Obj (Fibre_cat C k)))
  (c' : τ (Obj (Fibre_cat C k')))
  (beta : τ (Hom
      (Fibre_cat C k')
      (@fapp0
        (Fibre_cat C k)
        (Fibre_cat C k')
        (@catd_transport_func K C k k' p)
        c)
      c'))
  : τ (Hom
      (@mix_context_cat K A C)
      (Struct_sigma (Struct_sigma k a) c)
      (Struct_sigma (Struct_sigma k' a') c'))
≔ @sigma_arrow
    (@mix_neg_total K A)
    (@mix_context_family K A C)
    (Struct_sigma k a)
    (Struct_sigma k' a')
    c
    c'
    (@mix_neg_arrow K A k k' p a a' alpha)
    beta;

// Canonical base-laxity arrow: both fibre components are identities at the
// internally transported endpoints, while p remains the shared base arrow.
symbol mix_context_base_arrow [K : Cat]
  [A : τ (Catd (Op_cat K))]
  [C : τ (Catd K)]
  [k k' : τ (Obj K)]
  (p : τ (Hom K k k'))
  (a' : τ (Obj (Fibre_cat A k')))
  (c : τ (Obj (Fibre_cat C k)))
  : τ (Obj (Hom_cat
      (@mix_context_cat K A C)
      (Struct_sigma
        (Struct_sigma
          k
          (@fapp0
            (Fibre_cat A k')
            (Fibre_cat A k)
            (@catd_transport_func (Op_cat K) A k' k p)
            a'))
        c)
      (Struct_sigma
        (Struct_sigma k' a')
        (@fapp0
          (Fibre_cat C k)
          (Fibre_cat C k')
          (@catd_transport_func K C k k' p)
          c))))
≔ @mix_context_arrow
    K A C k k' p
    (@fapp0
      (Fibre_cat A k')
      (Fibre_cat A k)
      (@catd_transport_func (Op_cat K) A k' k p)
      a')
    a'
    (@id
      (Fibre_cat A k)
      (@fapp0
        (Fibre_cat A k')
        (Fibre_cat A k)
        (@catd_transport_func (Op_cat K) A k' k p)
        a'))
    c
    (@fapp0
      (Fibre_cat C k)
      (Fibre_cat C k')
      (@catd_transport_func K C k k' p)
      c)
    (@id
      (Fibre_cat C k')
      (@fapp0
        (Fibre_cat C k)
        (Fibre_cat C k')
        (@catd_transport_func K C k k' p)
        c));

symbol mix_uncurried_cat [K : Cat]
  (A : τ (Catd (Op_cat K)))
  (B C : τ (Catd K))
  : Cat
≔ @Pi_cat
    (@mix_context_cat K A C)
    (@mix_uncurried_family K A B C);

symbol mix_curried_cat [K : Cat]
  (A : τ (Catd (Op_cat K)))
  (B C : τ (Catd K))
  : Cat
≔ @Functord_cat K C (@Functor_catd K A B);

// Qualified mixed curry from sections over ((k,a),c) to displayed functors
// c |-> (a |-> s[((k,a),c)]).  Unit_prof continues to own the ambient
// two-ended Hom action used by Functor_catd; this is only section transposition.
constant symbol mixed_curry_func [K : Cat]
  [A : τ (Catd (Op_cat K))]
  [B C : τ (Catd K)]
  : τ (Functor
      (@mix_uncurried_cat K A B C)
      (@mix_curried_cat K A B C));

injective symbol mixed_curry_funcd [K : Cat]
  [A : τ (Catd (Op_cat K))]
  [B C : τ (Catd K)]
  (s : τ (Obj (@mix_uncurried_cat K A B C)))
  : τ (Functord C (@Functor_catd K A B));

rule @fapp0 _ _
      (@mixed_curry_func $K $A $B $C) $s
  ↪ @mixed_curry_funcd $K $A $B $C $s;

injective symbol mixed_curry_fibre_func [K : Cat]
  [A : τ (Catd (Op_cat K))]
  [B C : τ (Catd K)]
  (s : τ (Obj (@mix_uncurried_cat K A B C)))
  (k : τ (Obj K))
  : τ (Functor
      (Fibre_cat C k)
      (Functor_cat (Fibre_cat A k) (Fibre_cat B k)));

rule @tapp0_fapp0
      $K Cat_cat _ _ $k
      (@mixed_curry_funcd $K $A $B $C $s)
  ↪ @mixed_curry_fibre_func $K $A $B $C $s $k;

injective symbol mixed_curry_at_func [K : Cat]
  [A : τ (Catd (Op_cat K))]
  [B C : τ (Catd K)]
  (s : τ (Obj (@mix_uncurried_cat K A B C)))
  (k : τ (Obj K))
  (c : τ (Obj (Fibre_cat C k)))
  : τ (Functor (Fibre_cat A k) (Fibre_cat B k));

rule @fapp0 _ _
      (@mixed_curry_fibre_func $K $A $B $C $s $k) $c
  ↪ @mixed_curry_at_func $K $A $B $C $s $k $c;

// Triple-point beta.
rule @fapp0 _ _
      (@mixed_curry_at_func $K $A $B $C $s $k $c) $a
  ↪ @piapp0
      (@mix_context_cat $K $A $C)
      (@mix_uncurried_family $K $A $B $C)
      $s
      (Struct_sigma (Struct_sigma $k $a) $c);

// Negative-fibre arrow action is the original section action on the canonical
// identity-base mixed arrow.  The warning inventory records its expected
// overlap with generic strict identity action rather than adding a broad
// identity collapse.
rule @fapp1_fapp0 _ _
      (@mixed_curry_at_func $K $A $B $C $s $k $c)
      $a $a' $alpha
  ↪ @piapp1_fapp0
      (@mix_context_cat $K $A $C)
      (@mix_uncurried_family $K $A $B $C)
      $s
      (Struct_sigma (Struct_sigma $k $a) $c)
      (Struct_sigma (Struct_sigma $k $a') $c)
      (@mix_context_arrow
        $K $A $C $k $k (@id $K $k)
        $a $a' $alpha
        $c $c (@id (Fibre_cat $C $k) $c));

// Positive-fibre arrow action is a transfor; this rule projects its component
// at a.  The fapp0 forms on the LHS are the measured runtime normal forms of
// the three Fibre_cat classifiers, so both projection orders actually join.
rule @tapp0_fapp0
      _ _ _ _ $a
      (@fapp1_fapp0
        (@fapp0 $K Cat_cat $C $k)
        (Functor_cat
          (@fapp0 (Op_cat $K) Cat_cat $A $k)
          (@fapp0 $K Cat_cat $B $k))
        (@mixed_curry_fibre_func $K $A $B $C $s $k)
        $c $c' $beta)
  ↪ @piapp1_fapp0
      (@mix_context_cat $K $A $C)
      (@mix_uncurried_family $K $A $B $C)
      $s
      (Struct_sigma (Struct_sigma $k $a) $c)
      (Struct_sigma (Struct_sigma $k $a) $c')
      (@mix_context_arrow
        $K $A $C $k $k (@id $K $k)
        $a $a (@id (Fibre_cat $A $k) $a)
        $c $c' $beta);

// Base-arrow laxity is a genuine transfor; its component at a' is the section
// action on the canonical two-sided transported arrow.
rule @tapp0_fapp0
      _ _ _ _ $a'
      (@fdapp1_int_cell
        $K
        $C
        (@Functor_catd $K $A $B)
        (@mixed_curry_funcd $K $A $B $C $s)
        $k $k' $p $c)
  ↪ @piapp1_fapp0
      (@mix_context_cat $K $A $C)
      (@mix_uncurried_family $K $A $B $C)
      $s
      (Struct_sigma
        (Struct_sigma
          $k
          (@fapp0
            (Fibre_cat $A $k')
            (Fibre_cat $A $k)
            (@catd_transport_func (Op_cat $K) $A $k' $k $p)
            $a'))
        $c)
      (Struct_sigma
        (Struct_sigma $k' $a')
        (@fapp0
          (Fibre_cat $C $k)
          (Fibre_cat $C $k')
          (@catd_transport_func $K $C $k $k' $p)
          $c))
      (@mix_context_base_arrow $K $A $C $k $k' $p $a' $c);

// -------------------------------------------------------------------------------------------------
// 18. Cat-valued profunctors
// -------------------------------------------------------------------------------------------------

// 18a. Fixed-endpoint profunctor category and vertical maps

/*
  A v3.2 profunctor from A to B is a Cat-valued functor on A^op × B.

  Surface/formula:
    Prof_base(A,B) = A^op × B
    Prof_cat(A,B)  = (A^op × B) ⊢ Cat
    R : Prof(A,B)  means R : A^op × B ⊢ Cat

    Unit_prof(X)[x,y] = Hom_X(x,y)
    Hom_prof_along(F,G)[a,b] = Hom_X(F[a],G[b])

  for F : A ⊢ X and G : B ⊢ X. `Unit_prof(X)` is the primitive
  uncurried hom profunctor; `Hom_prof_along(F,G)` is the readable
  transparent surface for reindexing that unit along F and G.

  For a base arrow (p,q) : (a,b) -> (a',b') in A^op × B, equivalently

    p : a' ->^A a
    q : b  ->^B b',

  the hom profunctor acts by:

    h |-> G[q] o h o F[p].

  Endpoint functor arguments are owned by `Prof_reindex`, so the public
  representable action now computes through the generic reindex/product-map
  projection ladder and the primitive `Unit_prof` action.
*/

// Profunctor base: A^op × B.
symbol Prof_base (A B : Cat) : Cat
≔ Product_cat (Op_cat A) B;

// Category of Cat-valued profunctors A -/-> B.
injective symbol Prof_cat (A B : Cat) : Cat;

// Object projection: a profunctor is a Cat-valued family on `A^op x B`.
rule Obj (Prof_cat $A $B)
  ↪ Obj (Catd_cat (Product_cat (Op_cat $A) $B));

// Vertical hom projection: profunctor maps are natural family morphisms.
rule Hom_cat (Prof_cat $A $B) $P $Q
  ↪ @Functord_cat (Product_cat (Op_cat $A) $B) $P $Q;

// Proof-time endpoint recovery only: both displayed-family base components
// are recovered explicitly.
unif_rule Prof_cat $A $B ≡ Catd_cat (Product_cat $A0 $B0)
  ↪ [ $A ≡ Op_cat $A0; $B ≡ $B0 ];

// Object/type classifier of Cat-valued profunctors.
symbol Prof (A B : Cat) : Grpd
≔ Obj (Prof_cat A B);

// Readability alias for the endpoint-base map of profunctor reindexing.
//
// Semantically:
//   Prof_reindex_base_func(F,G) = Product_map_func(Op_func(F),G).
symbol Prof_reindex_base_func [A A' B B' : Cat]
  (F : τ (Functor A' A))
  (G : τ (Functor B' B))
  : τ (Functor
      (Product_cat (Op_cat A') B')
      (Product_cat (Op_cat A) B))
≔ @Product_map_func
    (Op_cat A')
    (Op_cat A)
    B'
    B
    (@Op_func A' A F)
    G;

// Vertical maps between profunctors with fixed endpoints.
//
// This is intentionally a transparent alias for the existing hom-category;
// identities and composition remain owned by `id_funcd` and
// `comp_catd_fapp0`.
symbol ProfMap
  [A B : Cat]
  (P Q : τ (Prof A B))
  : Grpd
≔ Obj (Hom_cat (Prof_cat A B) P Q);

// 18b. Opposite profunctors and fixed-endpoint duality

/*
  Object-level opposite profunctor.

  For R : Prof(A,B), the dual has base:

    Prof_base(Op_cat B,Op_cat A) = B × Op_cat A.

  The current higher-category opposite satisfies
  Hom_{Op X}(b,a) = Hom_X(a,b) without an extra opposite on the hom-category.
  Therefore profunctor duality is pullback along product symmetry only.
  Applying `Op_catd` pointwise would incorrectly add a second fibre opposite.
*/
injective symbol Op_prof [A B : Cat]
  (R : τ (Prof A B))
  : τ (Prof (Op_cat B) (Op_cat A));

// Fibre projection: duality evaluates R after swapping the product base.
rule @fapp0 _ Cat_cat (@Op_prof $A $B $R) $ba
  ↪ @fapp0
      (Product_cat (Op_cat $A) $B)
      Cat_cat
      $R
      (@fapp0
        (Product_cat $B (Op_cat $A))
        (Product_cat (Op_cat $A) $B)
        (@Product_swap_func $B (Op_cat $A))
        $ba);

// Full base-arrow action: first apply product swap, then the original action.
rule @fapp1_func _ Cat_cat (@Op_prof $A $B $R) $ba $ba'
  ↪ @comp_cat_fapp0
      (Hom_cat (Product_cat $B (Op_cat $A)) $ba $ba')
      (Hom_cat
        (Product_cat (Op_cat $A) $B)
        (@fapp0
          (Product_cat $B (Op_cat $A))
          (Product_cat (Op_cat $A) $B)
          (@Product_swap_func $B (Op_cat $A))
          $ba)
        (@fapp0
          (Product_cat $B (Op_cat $A))
          (Product_cat (Op_cat $A) $B)
          (@Product_swap_func $B (Op_cat $A))
          $ba'))
      (Functor_cat
        (@fapp0
          (Product_cat (Op_cat $A) $B)
          Cat_cat
          $R
          (@fapp0
            (Product_cat $B (Op_cat $A))
            (Product_cat (Op_cat $A) $B)
            (@Product_swap_func $B (Op_cat $A))
            $ba))
        (@fapp0
          (Product_cat (Op_cat $A) $B)
          Cat_cat
          $R
          (@fapp0
            (Product_cat $B (Op_cat $A))
            (Product_cat (Op_cat $A) $B)
            (@Product_swap_func $B (Op_cat $A))
            $ba')))
      (@fapp1_func
        (Product_cat (Op_cat $A) $B)
        Cat_cat
        $R
        (@fapp0
          (Product_cat $B (Op_cat $A))
          (Product_cat (Op_cat $A) $B)
          (@Product_swap_func $B (Op_cat $A))
          $ba)
        (@fapp0
          (Product_cat $B (Op_cat $A))
          (Product_cat (Op_cat $A) $B)
          (@Product_swap_func $B (Op_cat $A))
          $ba'))
      (@fapp1_func
        (Product_cat $B (Op_cat $A))
        (Product_cat (Op_cat $A) $B)
        (@Product_swap_func $B (Op_cat $A))
        $ba
        $ba');

// Capped base-arrow action of profunctor duality.
rule @fapp1_fapp0 _ Cat_cat (@Op_prof $A $B $R) $ba $ba' $h
  ↪ @fapp1_fapp0
      (Product_cat (Op_cat $A) $B)
      Cat_cat
      $R
      (@fapp0
        (Product_cat $B (Op_cat $A))
        (Product_cat (Op_cat $A) $B)
        (@Product_swap_func $B (Op_cat $A))
        $ba)
      (@fapp0
        (Product_cat $B (Op_cat $A))
        (Product_cat (Op_cat $A) $B)
        (@Product_swap_func $B (Op_cat $A))
        $ba')
      (@fapp1_fapp0
        (Product_cat $B (Op_cat $A))
        (Product_cat (Op_cat $A) $B)
        (@Product_swap_func $B (Op_cat $A))
        $ba
        $ba'
        $h);

// Object-level involution: dualizing a profunctor twice returns it.
rule @Op_prof
      _
      _
      (@Op_prof $A $B $R)
  ↪ $R;

/*
  Fixed-endpoint opposite profunctor functor.

  This is the fixed vertical action of object-level profunctor duality.
  Identity and composition are inherited from the generic functor calculus.
*/
injective symbol Op_prof_func [A B : Cat]
  : τ (Functor
      (@Prof_cat A B)
      (@Prof_cat (Op_cat B) (Op_cat A)));

// Object action of the fixed-endpoint duality functor.
rule @fapp0 _ _ (@Op_prof_func $A $B) $R
  ↪ @Op_prof $A $B $R;

// Proof-time semantic view: object duality is pullback along product swap.
unif_rule
  @Op_prof $A $B $R
  ≡ @Pullback_catd
      (Product_cat $B (Op_cat $A))
      (Product_cat (Op_cat $A) $B)
      $R
      (@Product_swap_func $B (Op_cat $A))
  ↪ [ tt ≡ tt ];

// Proof-time semantic view of the whole fixed-endpoint duality functor.
unif_rule
  @Op_prof_func $A $B
  ≡ @Pullback_catd_func
      (Product_cat $B (Op_cat $A))
      (Product_cat (Op_cat $A) $B)
      (@Product_swap_func $B (Op_cat $A))
  ↪ [ tt ≡ tt ];

// Vertical action of profunctor duality, inherited from `Op_prof_func`.
symbol Op_prof_map
  [A B : Cat]
  [P Q : τ (Prof A B)]
  (r : τ (ProfMap P Q))
  : τ (@ProfMap
      (Op_cat B)
      (Op_cat A)
      (@Op_prof A B P)
      (@Op_prof A B Q))
≔ @fapp1_fapp0
    (@Prof_cat A B)
    (@Prof_cat (Op_cat B) (Op_cat A))
    (@Op_prof_func A B)
    P Q r;

// 18c. Endpoint reindexing and product-base action

/*
  Profunctor reindexing.

  Surface/formula:
    Prof_reindex(R,F,G)[a',b'] = R[F[a'],G[b']]

  where:
    R : Prof(A,B)
    F : A' ⊢ A
    G : B' ⊢ B.

  Semantically this is pullback along:

    Product_map_func(Op_func(F),G) : A'^op × B' ⊢ A^op × B.

  Unlike the readability aliases above, `Prof_reindex` is a stable,
  non-injective head. A focused probe showed that the representable
  accumulation law cannot be attached to a symbol defined with `≔`.
  Its object and arrow projections below route through the generic
  Product_map_func(Op_func(F),G) base map directly.
*/
symbol Prof_reindex [A A' B B' : Cat]
  (R : τ (Prof A B))
  (F : τ (Functor A' A))
  (G : τ (Functor B' B))
  : τ (Prof A' B');

// Reindexing object-level profunctor opposite is owned by the semantic
// `Op_prof` head, not by the unfolded pullback/product-swap presentation.
rule @Prof_reindex
      _ _
      _ _
      (@Op_prof $A $B $R)
      (@Op_func $B' $B $G)
      (@Op_func $A' $A $F)
  ↪ @Op_prof
      $A'
      $B'
      (@Prof_reindex $A $A' $B $B' $R $F $G);

// Object/fibre projection of profunctor reindexing.
rule @fapp0
      _
      Cat_cat
      (@Prof_reindex $A $A' $B $B' $R $F $G)
      $ab
  ↪ @fapp0
      (Product_cat (Op_cat $A) $B)
      Cat_cat
      $R
      (@fapp0
        (Product_cat (Op_cat $A') $B')
        (Product_cat (Op_cat $A) $B)
        (@Product_map_func
          (Op_cat $A')
          (Op_cat $A)
          $B'
          $B
          (@Op_func $A' $A $F)
          $G)
        $ab);

// Full base-arrow action of reindexing. The named rung keeps the functorial
// action available before capping at one product arrow.
symbol Prof_reindex_fapp1_func [A A' B B' : Cat]
  (R : τ (Catd (Product_cat (Op_cat A) B)))
  (F : τ (Functor A' A))
  (G : τ (Functor B' B))
  [ab ab' : τ (Obj (Product_cat (Op_cat A') B'))]
  : τ (Functor
      (Hom_cat (Product_cat (Op_cat A') B') ab ab')
      (Functor_cat
        (@fapp0
          (Product_cat (Op_cat A') B')
          Cat_cat
          (@Prof_reindex A A' B B' R F G)
          ab)
        (@fapp0
          (Product_cat (Op_cat A') B')
          Cat_cat
          (@Prof_reindex A A' B B' R F G)
          ab')));

// Hom-action projection of reindexing at product-base endpoints ab,ab'.
rule @fapp1_func
      _
      Cat_cat
      (@Prof_reindex $A $A' $B $B' $R $F $G)
      $ab
      $ab'
  ↪ @Prof_reindex_fapp1_func
      $A $A' $B $B' $R $F $G $ab $ab';

// Applying the full action maps the base arrow through Op_func(F) × G, then
// applies the original profunctor action.
rule fapp0
      (@Prof_reindex_fapp1_func
        $A $A' $B $B' $R $F $G $ab $ab')
      $pq
  ↪ @fapp1_fapp0
      (Product_cat (Op_cat $A) $B)
      Cat_cat
      $R
      (@fapp0
        (Product_cat (Op_cat $A') $B')
        (Product_cat (Op_cat $A) $B)
        (@Product_map_func
          (Op_cat $A')
          (Op_cat $A)
          $B'
          $B
          (@Op_func $A' $A $F)
          $G)
        $ab)
      (@fapp0
        (Product_cat (Op_cat $A') $B')
        (Product_cat (Op_cat $A) $B)
        (@Product_map_func
          (Op_cat $A')
          (Op_cat $A)
          $B'
          $B
          (@Op_func $A' $A $F)
          $G)
        $ab')
      (@fapp1_fapp0
        (Product_cat (Op_cat $A') $B')
        (Product_cat (Op_cat $A) $B)
        (@Product_map_func
          (Op_cat $A')
          (Op_cat $A)
          $B'
          $B
          (@Op_func $A' $A $F)
          $G)
        $ab
        $ab'
        $pq);

// Direct capped action joins the full-action projection above.
rule @fapp1_fapp0
      _
      Cat_cat
      (@Prof_reindex $A $A' $B $B' $R $F $G)
      $ab
      $ab'
      $pq
  ↪ @fapp1_fapp0
      (Product_cat (Op_cat $A) $B)
      Cat_cat
      $R
      (@fapp0
        (Product_cat (Op_cat $A') $B')
        (Product_cat (Op_cat $A) $B)
        (@Product_map_func
          (Op_cat $A')
          (Op_cat $A)
          $B'
          $B
          (@Op_func $A' $A $F)
          $G)
        $ab)
      (@fapp0
        (Product_cat (Op_cat $A') $B')
        (Product_cat (Op_cat $A) $B)
        (@Product_map_func
          (Op_cat $A')
          (Op_cat $A)
          $B'
          $B
          (@Op_func $A' $A $F)
          $G)
        $ab')
      (@fapp1_fapp0
        (Product_cat (Op_cat $A') $B')
        (Product_cat (Op_cat $A) $B)
        (@Product_map_func
          (Op_cat $A')
          (Op_cat $A)
          $B'
          $B
          (@Op_func $A' $A $F)
          $G)
        $ab
        $ab'
        $pq);

// 18d. Unit hom profunctor and readable representables

// Identity/unit hom profunctor, the uncurried/product form of hom_int(id_X).
injective symbol Unit_prof (X : Cat)
  : τ (Prof X X);

// Direct fibre computation, formulated for an arbitrary product object.
rule @fapp0
      _
      Cat_cat
      (@Unit_prof $X)
      $xy
  ↪ Hom_cat
      $X
      (sigma_Fst $xy)
      (sigma_Snd $xy);

// Full base-arrow action of the unit hom profunctor at constructed product
// endpoints. The public normal form is the general Hom_cat endpoint-action
// owner; the product-composition presentation folds to this owner separately.
// lhs-audit: keep 4 -- constructed pair endpoint is decomposed by the rule.
rule @fapp1_func
      _
      Cat_cat
      (@Unit_prof $X)
      (Struct_sigma $x $y)
      (Struct_sigma $x' $y')
  ↪ @Hom_tele_func $X $x $x' $y $y';

// Capped base-arrow action, joined with the full-action projection above.
rule @fapp1_fapp0
      _
      Cat_cat
      (@Unit_prof $X)
      $xy
      $xy'
      $pq
  ↪ @Hom_func
      $X
      (sigma_Fst $xy)
      (sigma_Fst $xy')
      (sigma_Snd $xy)
      (sigma_Snd $xy')
      (sigma_Fst $pq)
      (sigma_Snd $pq);

// Binary representable hom profunctor as endpoint reindexing of Unit_prof.
//
// Surface/formula:
//   Hom_prof_along(F,G)[a,b] = Hom_X(F[a],G[b]).
symbol Hom_prof_along [A B X : Cat]
  (F : τ (Functor A X))
  (G : τ (Functor B X))
  : τ (Prof A B)
≔ @Prof_reindex X A X B (@Unit_prof X) F G;

// Right-representable hom profunctor, as the identity-left specialization.
symbol Hom_prof [B X : Cat]
  (G : τ (Functor B X))
  : τ (Prof X B)
≔ @Hom_prof_along X B X (@id_func X) G;

// Standard equipment names for the two representables induced by a functor.
// They are transparent views of the Unit_prof/Prof_reindex normal form.
symbol Companion_prof [A B : Cat]
  (F : τ (Functor A B))
  : τ (Prof A B)
≔ @Hom_prof_along A B B F (@id_func B);

// Conjoint of F: the right-representable `Hom_B(F[-],-)` presentation.
symbol Conjoint_prof [A B : Cat]
  (F : τ (Functor A B))
  : τ (Prof B A)
≔ @Hom_prof A B F;

// Ordinary representability of a profunctor by a conjoint.
symbol IsRepresentedBy_iso
  [B J : Cat]
  (P : τ (Prof B J))
  (L : τ (Functor J B))
  : Grpd
≔ IsoEvidence
    (Prof_cat B J)
    P
    (@Conjoint_prof J B L);

// A chosen representing functor together with ordinary isomorphism evidence.
symbol Representation_iso
  [B J : Cat]
  (P : τ (Prof B J))
  : Grpd
≔ `Σ_ L : τ (Functor J B),
    @IsRepresentedBy_iso B J P L;

// 18e. Computational comparison as the profunctor-facing DefIso view

/*
  Computational comparisons between profunctors.

  `ProfComparison(P,Q)` is the transparent profunctor-facing view of
  `DefIso(Prof_cat(A,B),P,Q)`. Push/pull are postcomposition by the selected
  forward/inverse maps. Their cancellation is owned by the generic `DefIso`
  and stable hom-action calculus; there is no parallel profunctor-specific
  beta/eta theory. `IsoEvidence` is the ordinary propositional view.
*/
// Transparent comparison classifier: `ProfComparison(P,Q) = DefIso(P,Q)`.
symbol ProfComparison
  [A B : Cat]
  (P Q : τ (Prof A B))
  : Grpd
≔ @DefIso (@Prof_cat A B) P Q;

// Push an incoming vertical map forward by postcomposition with `defiso_to`.
symbol prof_comparison_push
  [A B : Cat]
  [P Q : τ (Prof A B)]
  (i : τ (ProfComparison P Q))
  [R : τ (Prof A B)]
  (r : τ (ProfMap R P))
  : τ (ProfMap R Q)
≔ @hom_postcomp_fapp0
    (Prof_cat A B)
    (Prof_cat A B)
    (@id_func (Prof_cat A B))
    R P Q
    (@defiso_to (@Prof_cat A B) P Q i)
    r;

// Pull an incoming vertical map back by postcomposition with `defiso_from`.
symbol prof_comparison_pull
  [A B : Cat]
  [P Q : τ (Prof A B)]
  (i : τ (ProfComparison P Q))
  [R : τ (Prof A B)]
  (s : τ (ProfMap R Q))
  : τ (ProfMap R P)
≔ @hom_postcomp_fapp0
    (Prof_cat A B)
    (Prof_cat A B)
    (@id_func (Prof_cat A B))
    R Q P
    (@defiso_from (@Prof_cat A B) P Q i)
    s;

// Selected forward and inverse arrows are identity applications.
symbol prof_comparison_to
  [A B : Cat]
  [P Q : τ (Prof A B)]
  (i : τ (ProfComparison P Q))
  : τ (ProfMap P Q)
≔ @defiso_to (@Prof_cat A B) P Q i;

// Selected inverse vertical map of a computational comparison.
symbol prof_comparison_from
  [A B : Cat]
  [P Q : τ (Prof A B)]
  (i : τ (ProfComparison P Q))
  : τ (ProfMap Q P)
≔ @defiso_from (@Prof_cat A B) P Q i;

// Forget a computational comparison to ordinary isomorphism evidence.
symbol prof_comparison_evidence
  [A B : Cat]
  [P Q : τ (Prof A B)]
  (i : τ (ProfComparison P Q))
  : τ (IsoEvidence (Prof_cat A B) P Q)
≔ @defiso_iso_evidence (@Prof_cat A B) P Q i;

// Incoming-map naturality and selected-arrow agreement are inherited from
// the generic hom-action and DefIso owners. `ProfComparison` keeps only a
// compatibility surface while downstream code migrates to `DefIso` directly.

// Reflexive profunctor comparison, inherited from `defiso_refl`.
symbol prof_comparison_refl
  [A B : Cat]
  (P : τ (Prof A B))
  : τ (ProfComparison P P)
≔ @defiso_refl (@Prof_cat A B) P;

// Symmetry of profunctor comparison, inherited from `defiso_sym`.
symbol prof_comparison_sym
  [A B : Cat]
  [P Q : τ (Prof A B)]
  (i : τ (ProfComparison P Q))
  : τ (ProfComparison Q P)
≔ @defiso_sym (@Prof_cat A B) P Q i;

// Vertical composition of comparisons, inherited from `defiso_comp`.
symbol prof_comparison_comp
  [A B : Cat]
  [P Q R : τ (Prof A B)]
  (j : τ (ProfComparison Q R))
  (i : τ (ProfComparison P Q))
  : τ (ProfComparison P R)
≔ @defiso_comp (@Prof_cat A B) P Q R j i;

// Functorial image of a comparison, inherited from `defiso_fmap`.
symbol prof_comparison_fmap
  [A B A' B' : Cat]
  (F : τ (Functor (Prof_cat A B) (Prof_cat A' B')))
  [P Q : τ (Prof A B)]
  (i : τ (ProfComparison P Q))
  : τ (ProfComparison (fapp0 F P) (fapp0 F Q))
≔ @defiso_fmap
    (@Prof_cat A B)
    (@Prof_cat A' B')
    F P Q i;

// Reindexing along identity endpoint functors is neutral. This rule is added
// here because tensor reindexing below exposes identity reindexing at the
// unchanged middle endpoint.
rule @Prof_reindex
      $A $A $B $B
      $R
      (@id Cat_cat $A)
      (@id Cat_cat $B)
  ↪ $R;

// Nested reindexing accumulates both endpoint functors.
rule @Prof_reindex
      $A' $A''
      $B' $B''
      (@Prof_reindex $A $A' $B $B' $R $F $G)
      $F'
      $G'
  ↪ @Prof_reindex
      $A $A''
      $B $B''
      $R
      (@comp_cat_fapp0 $A'' $A' $A $F $F')
      (@comp_cat_fapp0 $B'' $B' $B $G $G');

// Reindexing a constant profunctor remains constant.
rule @Prof_reindex
      $A $A'
      $B $B'
      (@Const_catd _ $C)
      $F
      $G
  ↪ @Const_catd (Product_cat (Op_cat $A') $B') $C;

// 18f. Shaped profunctor cells and endpoint-changing application

/*
  Shaped profunctor cells.

  A cell from R' : Prof(A',B') to R : Prof(A,B), over endpoint functors
  F : A' -> A and G : B' -> B, is a natural family morphism:

    R' -> Prof_reindex(R,F,G).

  The common-shape specialization uses Unit_prof(I) as source. Its objects are
  shaped elements of R over F : I -> A and G : I -> B. These remain transparent
  aliases: `Functord_cat` and `Prof_reindex` are the semantic owners, while the
  representable fold above supplies the useful normal form.
*/
symbol Prof_transf_cat [A A' B B' : Cat]
  (R' : τ (Prof A' B'))
  (F : τ (Functor A' A))
  (R : τ (Prof A B))
  (G : τ (Functor B' B))
  : Cat
≔ @Functord_cat
    (Product_cat (Op_cat A') B')
    R'
    (@Prof_reindex A A' B B' R F G);

// Shaped-cell category: Prof_hom_cat(F,R,G) = Cell(Unit_I,R;F,G).
symbol Prof_hom_cat [I A B : Cat]
  (F : τ (Functor I A))
  (R : τ (Prof A B))
  (G : τ (Functor I B))
  : Cat
≔ @Prof_transf_cat
    A I B I
    (@Unit_prof I)
    F
    R
    G;

// Objects of the shaped-cell category: Prof_hom(F,R,G) = Obj Prof_hom_cat(F,R,G).
symbol Prof_hom [I A B : Cat]
  (F : τ (Functor I A))
  (R : τ (Prof A B))
  (G : τ (Functor I B))
  : Grpd
≔ Obj (@Prof_hom_cat I A B F R G);

/*
  Narrow shaped application of an internally natural profunctor cell.

  This is deliberately smaller than the retired general equipment-composition
  facade: it applies one cell to one shaped element and owns no
  identity, associativity, or generic composition rewrite rules.
*/
symbol Prof_cell_apply
  [I A' B' A B : Cat]
  [R' : τ (Prof A' B')]
  [R : τ (Prof A B)]
  [F : τ (Functor A' A)]
  [G : τ (Functor B' B)]
  [a : τ (Functor I A')]
  [b : τ (Functor I B')]
  (c : τ (Obj (@Prof_transf_cat A A' B B' R' F R G)))
  (r : τ (@Prof_hom I A' B' a R' b))
  : τ (@Prof_hom
      I A B
      (@comp_cat_fapp0 I A' A F a)
      R
      (@comp_cat_fapp0 I B' B G b));

// 18g. Internalized reindexing and equipment-style cell composition

/*
  Internalized profunctor reindexing.

  Semantically this is pullback along Product_map_func(Op_func(F),G), but the
  stable functor and arrow heads are required because the object projection
  must remain the stable `Prof_reindex` normal form.
*/
symbol Prof_reindex_func [A A' B B' : Cat]
  (F : τ (Functor A' A))
  (G : τ (Functor B' B))
  : τ (Functor (Prof_cat A B) (Prof_cat A' B'));

// Object action of internal reindexing: Prof_reindex_func(F,G)[R] ↪ R(F-,G-).
rule @fapp0
      _
      _
      (@Prof_reindex_func $A $A' $B $B' $F $G)
      $R
  ↪ @Prof_reindex $A $A' $B $B' $R $F $G;

// Vertical-map action of profunctor reindexing.
symbol Prof_reindex_transf [A A' B B' : Cat]
  [R S : τ (Prof A B)]
  (r : τ (ProfMap R S))
  (F : τ (Functor A' A))
  (G : τ (Functor B' B))
  : τ (ProfMap
      (@Prof_reindex A A' B B' R F G)
      (@Prof_reindex A A' B B' S F G));

// Capped hom-action: Prof_reindex_func(F,G)[r] ↪ Prof_reindex_transf(r,F,G).
rule @fapp1_fapp0
      _
      _
      (@Prof_reindex_func $A $A' $B $B' $F $G)
      $R
      $S
      $r
  ↪ @Prof_reindex_transf $A $A' $B $B' $R $S $r $F $G;

// Identity endpoint reindexing leaves a vertical profunctor map unchanged.
rule @Prof_reindex_transf
      $A $A $B $B
      $R $S
      $r
      (@id Cat_cat $A)
      (@id Cat_cat $B)
  ↪ $r;

// Probe: stable arrow action of profunctor reindexing should not hide
// ordinary functoriality under the fold-oriented hom-action normal form.
rule @Prof_reindex_transf
      $A $A2 $B $B2
      $R $R
      (@id (@Prof_cat $A $B) $R)
      $F $G
  ↪ @id
      (@Prof_cat $A2 $B2)
      (@Prof_reindex $A $A2 $B $B2 $R $F $G);

// lhs-audit: keep 1 -- Prof_cat is the target-category discriminator for reindexing composition.
rule @comp_fapp0
      (@Prof_cat $A2 $B2)
      _ _ _
      (@Prof_reindex_transf $A $A2 $B $B2 $S $T $s $F $G)
      (@Prof_reindex_transf $A $A2 $B $B2 $R $S $r $F $G)
  ↪ @Prof_reindex_transf
      $A $A2 $B $B2
      $R $T
      (@comp_fapp0
        (@Prof_cat $A $B)
        $R $S $T
        $s $r)
      $F $G;

// Reindexed DefIso cancellation under represented postcomposition.
rule @hom_postcomp_fapp0
      (@Prof_cat $A2 $B2)
      (@Prof_cat $A2 $B2)
      (@id Cat_cat (@Prof_cat $A2 $B2))
      $R _ _
      (@Prof_reindex_transf
        $A $A2 $B $B2
        $y $x
        (@defiso_from
          (@Prof_cat $A $B)
          $x $y $i)
        $F $G)
      (@hom_postcomp_fapp0
        (@Prof_cat $A2 $B2)
        (@Prof_cat $A2 $B2)
        (@id Cat_cat (@Prof_cat $A2 $B2))
        $R _ _
        (@Prof_reindex_transf
          $A $A2 $B $B2
          $x $y
          (@defiso_to
            (@Prof_cat $A $B)
            $x $y $i)
          $F $G)
        $r)
  ↪ $r
with @hom_postcomp_fapp0
      (@Prof_cat $A2 $B2)
      (@Prof_cat $A2 $B2)
      (@id Cat_cat (@Prof_cat $A2 $B2))
      $R _ _
      (@Prof_reindex_transf
        $A $A2 $B $B2
        $x $y
        (@defiso_to
          (@Prof_cat $A $B)
          $x $y $i)
        $F $G)
      (@hom_postcomp_fapp0
        (@Prof_cat $A2 $B2)
        (@Prof_cat $A2 $B2)
        (@id Cat_cat (@Prof_cat $A2 $B2))
        $R _ _
        (@Prof_reindex_transf
          $A $A2 $B $B2
          $y $x
          (@defiso_from
            (@Prof_cat $A $B)
            $x $y $i)
          $F $G)
        $s)
  ↪ $s;

// Readable shaped identity element for the unit profunctor.
symbol Prof_id_hom (B : Cat)
  : τ (@Prof_hom
      B B B
      (@id_func B)
      (@Unit_prof B)
      (@id_func B))
≔ @id_funcd
    (Product_cat (Op_cat B) B)
    (@Unit_prof B);

// Core runtime computation uses narrow fixed owners such as `Prof_cell_apply`,
// fixed co-Yoneda transformations, `Prof_tensor_map`, and generic family
// composition directly.

/*
  Shaped representable unit element induced by a functor's hom action.

  This is the core owner used by fixed co-Yoneda beta.
*/
symbol Prof_func_hom [A B : Cat]
  (F : τ (Functor A B))
  : τ (@Prof_hom A B B F (@Unit_prof B) F);

// Identity functor induces the canonical shaped identity of Unit_prof(A).
rule @Prof_func_hom $A $A (@id Cat_cat $A)
  ↪ @Prof_id_hom $A;

// Component of a functor-induced shaped unit is the ordinary hom-action.
// lhs-audit: keep 1,3,4 -- the product/opposite base gives sigma_Fst/Snd
// their profunctor endpoint types; the normalized representable families pin
// the actual `Prof_func_hom` transfor shape and avoid unrelated Cat-valued
// projection overlaps.
rule @tapp0_fapp0
      (Product_cat (Op_cat $A) $A)
      Cat_cat
      (@Unit_prof $A)
      (@Prof_reindex $B $A $B $A (@Unit_prof $B) $F $F)
      $ab
      (@Prof_func_hom $A $B $F)
  ↪ @fapp1_func
      $A
      $B
      $F
      (sigma_Fst $ab)
      (sigma_Snd $ab);

// Capped product-base action of `Prof_func_hom` is the uncurried projection
// of the existing internal ordinary hom-action, not a separate naturality law.
// lhs-audit: keep 1,3,4 -- the product/opposite base gives sigma_Fst/Snd
// their profunctor endpoint types; the normalized representable families pin
// the actual `Prof_func_hom` transfor shape and avoid unrelated Cat-valued
// projection overlaps.
rule @tapp1_fapp0
      (Product_cat (Op_cat $A) $A)
      Cat_cat
      (@Unit_prof $A)
      (@Prof_reindex $B $A $B $A (@Unit_prof $B) $F $F)
      $ab
      $ab'
      (@Prof_func_hom $A $B $F)
      $pq
  ↪ @tapp1_fapp0
      $A
      Cat_cat
      (@hom_ $A $A (@id_func $A) (sigma_Fst $ab))
      (@hom_ $B $A $F (@fapp0 $A $B $F (sigma_Fst $ab')))
      (sigma_Snd $ab)
      (sigma_Snd $ab')
      (@tapp1_fapp0
        (Op_cat $A)
        (@Catd_cat $A)
        (@hom_int $A $A (@id_func $A))
        (@comp_cat_fapp0
          (Op_cat $A)
          (Op_cat $B)
          (@Catd_cat $A)
          (@hom_int $B $A $F)
          (@Op_func $A $B $F))
        (sigma_Fst $ab)
        (sigma_Fst $ab')
        (@fapp1_int_transf $A $B $F)
        (sigma_Fst $pq))
      (sigma_Snd $pq);

// 18h. Tensor, shaped introduction, and fixed-endpoint co-Yoneda maps

/*
  Primitive tensor/composition of Cat-valued profunctors.

  Semantically this is the coend-like composite:

    R : Prof(A,B), S : Prof(B,X) |- Prof_tensor(R,S) : Prof(A,X).

  The current kernel has no general coend/coinserter quotient, so the tensor
  itself is intentionally opaque. Reindexing distributes across only the two
  exposed endpoints; the shared middle category B remains fixed.
*/
symbol Prof_tensor [A B X : Cat]
  (R : τ (Prof A B))
  (S : τ (Prof B X))
  : τ (Prof A X);

// Tensor reindexing acts only at its two exposed endpoints.
rule @Prof_reindex
      $A $A'
      $X $X'
      (@Prof_tensor $A $B $X $R $S)
      $F
      $G
  ↪ @Prof_tensor
      $A' $B $X'
      (@Prof_reindex
        $A $A' $B $B
        $R
        $F
        (@id_func $B))
      (@Prof_reindex
        $B $B $X $X'
        $S
        (@id_func $B)
        $G);

/*
  Fixed-endpoint tensor map action.

  This is the narrow fixed-endpoint vertical action. Endpoint-changing tensor
  cells should eventually be derived from this owner plus profunctor
  reindexing, rather than defining this owner through the endpoint-changing
  primitive.
*/
symbol Prof_tensor_map
  [A B X : Cat]
  [P P' : τ (Prof A B)]
  [Q Q' : τ (Prof B X)]
  (r : τ (ProfMap P P'))
  (s : τ (ProfMap Q Q'))
  : τ (ProfMap
      (@Prof_tensor A B X P Q)
      (@Prof_tensor A B X P' Q'));

// Bifunctor package for fixed-endpoint profunctor tensor.
symbol Prof_tensor_func [A B X : Cat]
  : τ (Functor
      (Product_cat (@Prof_cat A B) (@Prof_cat B X))
      (@Prof_cat A X));

// Object action: Prof_tensor_func[(P,Q)] ↪ P tensor Q.
rule @fapp0 _ _ (@Prof_tensor_func $A $B $X) $PQ
  ↪ @Prof_tensor
      $A $B $X
      (sigma_Fst $PQ)
      (sigma_Snd $PQ);

// Capped arrow action: (r,s) ↦ Prof_tensor_map(r,s).
rule @fapp1_fapp0 _ _ (@Prof_tensor_func $A $B $X) $PQ $PQ' $rs
  ↪ @Prof_tensor_map
      $A $B $X
      (sigma_Fst $PQ)
      (sigma_Fst $PQ')
      (sigma_Snd $PQ)
      (sigma_Snd $PQ')
      (sigma_Fst $rs)
      (sigma_Snd $rs);

// Compose shaped elements through a common middle probe M.
constant symbol Prof_tensor_hom_hom
  [I A B X : Cat]
  [R : τ (Prof A B)]
  [S : τ (Prof B X)]
  [F : τ (Functor I A)]
  [G : τ (Functor I X)]
  (M : τ (Functor I B))
  (r : τ (@Prof_hom I A B F R M))
  (s : τ (@Prof_hom I B X M S G))
  : τ (@Prof_hom I A X F (@Prof_tensor A B X R S) G);

/*
  Internal fixed-endpoint co-Yoneda naturality owners.

  The unit tensor functors expose the fixed-endpoint action of
  `Prof_tensor_map`. The co-Yoneda maps below are diagonal components of
  natural transformations; their naturality is represented by generic
  `tapp1_fapp0`, not by a separate commuting-square rewrite rule.
*/
symbol Prof_tensor_right_unit_pair_func [A B : Cat]
  : τ (Functor
      (@Prof_cat A B)
      (Product_cat (@Prof_cat A B) (@Prof_cat B B)))
≔ Struct_sigma
    (@id_func (@Prof_cat A B))
    (@Const_func (@Prof_cat A B) (@Prof_cat B B) (@Unit_prof B));

// Right-unit tensor endofunctor: P ↦ P tensor Unit_prof(B).
symbol Prof_tensor_right_unit_func [A B : Cat]
  : τ (Functor (Prof_cat A B) (Prof_cat A B))
≔ @comp_cat_fapp0
    (@Prof_cat A B)
    (Product_cat (@Prof_cat A B) (@Prof_cat B B))
    (@Prof_cat A B)
    (@Prof_tensor_func A B B)
    (@Prof_tensor_right_unit_pair_func A B);

// Pairing for the left-unit tensor endofunctor: P ↦ (Unit_prof(A),P).
symbol Prof_tensor_left_unit_pair_func [A B : Cat]
  : τ (Functor
      (@Prof_cat A B)
      (Product_cat (@Prof_cat A A) (@Prof_cat A B)))
≔ Struct_sigma
    (@Const_func (@Prof_cat A B) (@Prof_cat A A) (@Unit_prof A))
    (@id_func (@Prof_cat A B));

// Left-unit tensor endofunctor: P ↦ Unit_prof(A) tensor P.
symbol Prof_tensor_left_unit_func [A B : Cat]
  : τ (Functor (Prof_cat A B) (Prof_cat A B))
≔ @comp_cat_fapp0
    (@Prof_cat A B)
    (Product_cat (@Prof_cat A A) (@Prof_cat A B))
    (@Prof_cat A B)
    (@Prof_tensor_func A A B)
    (@Prof_tensor_left_unit_pair_func A B);

// Covariant co-Yoneda natural transformation: (- tensor Unit_B) => id.
symbol Prof_coyoneda_cov_transf [A B : Cat]
  : τ (Transf
      (@Prof_tensor_right_unit_func A B)
      (@id_func (@Prof_cat A B)));

// Contravariant co-Yoneda natural transformation: (Unit_A tensor -) => id.
symbol Prof_coyoneda_con_transf [A B : Cat]
  : τ (Transf
      (@Prof_tensor_left_unit_func A B)
      (@id_func (@Prof_cat A B)));

// Fixed-endpoint one-way co-Yoneda maps.
symbol Prof_coyoneda_cov_map [A B : Cat]
  (P : τ (Prof A B))
  : τ (ProfMap
      (@Prof_tensor A B B P (@Unit_prof B))
      P);

// Left-unit co-Yoneda component: Unit_A tensor P -> P.
symbol Prof_coyoneda_con_map [A B : Cat]
  (P : τ (Prof A B))
  : τ (ProfMap
      (@Prof_tensor A A B (@Unit_prof A) P)
      P);

// Component projection of the covariant co-Yoneda transformation at P.
rule @tapp0_fapp0
      _ _
      _ _
      $P
      (@Prof_coyoneda_cov_transf $A $B)
  ↪ @Prof_coyoneda_cov_map $A $B $P;

// Component projection of the contravariant co-Yoneda transformation at P.
rule @tapp0_fapp0
      _ _
      _ _
      $P
      (@Prof_coyoneda_con_transf $A $B)
  ↪ @Prof_coyoneda_con_map $A $B $P;

// Fixed right-unit co-Yoneda beta on tensor-introduced shaped elements.
rule @Prof_cell_apply
      $I $A $B $A $B
      (@Prof_tensor $A $B $B $P
        (@Unit_prof $B))
      $P
      (@id Cat_cat $A)
      (@id Cat_cat $B)
      $F
      $M
      (@Prof_coyoneda_cov_map $A $B $P)
      (@Prof_tensor_hom_hom
        $I $A $B $B
        $P
        (@Unit_prof $B)
        $F
        $M
        $M
        $p
        (@Prof_func_hom $I $B $M))
  ↪ $p;

// Fixed right-unit co-Yoneda naturality fusion under shaped application.
rule @Prof_cell_apply
      $I $A $B $A $B
      (@Prof_tensor $A $B $B $P
        (@Unit_prof $B))
      $P'
      (@id Cat_cat $A)
      (@id Cat_cat $B)
      $F
      $M
      (@tapp1_fapp0
        _ _
        _ _
        $P $P'
        (@Prof_coyoneda_cov_transf $A $B)
        $pp)
      (@Prof_tensor_hom_hom
        $I $A $B $B
        $P
        (@Unit_prof $B)
        $F
        $M
        $M
        $p
        (@Prof_func_hom $I $B $M))
  ↪ @Prof_cell_apply
      $I $A $B $A $B
      $P $P'
      (@id_func $A)
      (@id_func $B)
      $F $M
      $pp $p;

// Fixed left-unit co-Yoneda beta on tensor-introduced shaped elements.
rule @Prof_cell_apply
      $I $A $B $A $B
      (@Prof_tensor $A $A $B
        (@Unit_prof $A)
        $P)
      $P
      (@id Cat_cat $A)
      (@id Cat_cat $B)
      $F
      $G
      (@Prof_coyoneda_con_map $A $B $P)
      (@Prof_tensor_hom_hom
        $I $A $A $B
        (@Unit_prof $A)
        $P
        $F
        $G
        $F
        (@Prof_func_hom $I $A $F)
        $p)
  ↪ $p;

// Fixed left-unit co-Yoneda naturality fusion under shaped application.
rule @Prof_cell_apply
      $I $A $B $A $B
      (@Prof_tensor $A $A $B
        (@Unit_prof $A)
        $P)
      $P'
      (@id Cat_cat $A)
      (@id Cat_cat $B)
      $F
      $G
      (@tapp1_fapp0
        _ _
        _ _
        $P $P'
        (@Prof_coyoneda_con_transf $A $B)
        $pp)
      (@Prof_tensor_hom_hom
        $I $A $A $B
        (@Unit_prof $A)
        $P
        $F
        $G
        $F
        (@Prof_func_hom $I $A $F)
        $p)
  ↪ @Prof_cell_apply
      $I $A $B $A $B
      $P $P'
      (@id_func $A)
      (@id_func $B)
      $F $G
      $pp $p;

// 18i. Covariant/contravariant implication and vertical closed cores

/*
  Covariant profunctor implication.

  For O : Prof(A,X) and Q : Prof(B,X):

    Prof_imply_cov(O,Q) : Prof(A,B)

  is the symbolic right adjoint to tensoring on the right by Q. The current
  kernel has no end semantics for this object, so the implication itself is
  opaque and its computational content is exposed through reindexing and the
  eval/lambda calculus below.
*/
symbol Prof_imply_cov [A B X : Cat]
  (O : τ (Prof A X))
  (Q : τ (Prof B X))
  : τ (Prof A B);

// Reindexing the implication result acts on the left endpoints of both inputs.
rule @Prof_reindex
      $A $A'
      $B $B'
      (@Prof_imply_cov $A $B $X $O $Q)
      $F
      $M
  ↪ @Prof_imply_cov
      $A' $B' $X
      (@Prof_reindex
        $A $A' $X $X
        $O
        $F
        (@id_func $X))
      (@Prof_reindex
        $B $B' $X $X
        $Q
        $M
        (@id_func $X));

/*
  Mixed-variance covariant implication.

    Prof_imply_cov_func2 :
      Prof(A,X) x Prof(B,X)^op -> Prof(A,B).

  Product identity projections compute for arbitrary product objects, so the
  direct product-domain presentation inherits the generic strict-functor
  identity law without requiring a visible Struct_sigma constructor.
*/
symbol Prof_imply_cov_func2 [A B X : Cat]
  : τ (Functor
      (Product_cat
        (Prof_cat A X)
        (Op_cat (Prof_cat B X)))
      (Prof_cat A B));

// Object action: (O,Q) ↦ Prof_imply_cov(O,Q), contravariant in Q.
rule @fapp0
      _ _
      (@Prof_imply_cov_func2 $A $B $X)
      $oq
  ↪ @Prof_imply_cov
      $A $B $X
      (sigma_Fst $oq)
      (sigma_Snd $oq);

// Insert a varying O beside the fixed contravariant weight Q.
symbol Prof_imply_cov_fixed_weight_func [A B X : Cat]
  (Q : τ (Prof B X))
  : τ (Functor
      (Prof_cat A X)
      (Product_cat
        (Prof_cat A X)
        (Op_cat (Prof_cat B X))))
≔ Struct_sigma
    (@id_func (Prof_cat A X))
    (@Const_func
      (Prof_cat A X)
      (Op_cat (Prof_cat B X))
      Q);

/*
  Fixed-weight implication is the semantic specialization of the mixed
  functor along O |-> (O,Q). The semantic definition is kept opaque so its
  generic fapp1 identity/composition cuts remain visible before the product
  pipeline unfolds.
*/
symbol Prof_imply_cov_func [A B X : Cat]
  (Q : τ (Prof B X))
  : τ (Functor
      (Prof_cat A X)
      (Prof_cat A B))
≔ @comp_cat_fapp0
    (Prof_cat A X)
    (Product_cat
      (Prof_cat A X)
      (Op_cat (Prof_cat B X)))
    (Prof_cat A B)
    (@Prof_imply_cov_func2 A B X)
    (@Prof_imply_cov_fixed_weight_func A B X Q);

opaque Prof_imply_cov_func;

// Fixed-weight object projection: Prof_imply_cov_func(Q)[O] ↪ O ⇒ Q.
rule fapp0
      (@Prof_imply_cov_func $A $B $X $Q)
      $O
  ↪ @Prof_imply_cov $A $B $X $O $Q;

/*
  Vertical covariant closed core.

  Evaluation and lambda abstraction are primitive only for maps between
  profunctors with fixed endpoints:

    ProfMap(P, O ⇒ Q)  <->  ProfMap(P tensor Q, O).

  Endpoint-changing equipment views are intentionally absent. They are
  historical compatibility wrappers around this fixed-endpoint core and should
  be reintroduced only as derived APIs when a concrete consumer needs them.
*/
symbol Prof_eval_cov_map
  [A B X : Cat]
  [P : τ (Prof A B)]
  [Q : τ (Prof B X)]
  [O : τ (Prof A X)]
  (t : τ (ProfMap P (@Prof_imply_cov A B X O Q)))
  : τ (ProfMap (@Prof_tensor A B X P Q) O);

// Covariant currying: ProfMap(P tensor Q,O) -> ProfMap(P,O ⇒ Q).
symbol Prof_lambda_cov_map
  [A B X : Cat]
  [P : τ (Prof A B)]
  [Q : τ (Prof B X)]
  [O : τ (Prof A X)]
  (t : τ (ProfMap (@Prof_tensor A B X P Q) O))
  : τ (ProfMap P (@Prof_imply_cov A B X O Q));

// Covariant beta/eta: lambda(eval(t)) ↪ t and eval(lambda(t)) ↪ t.
rule @Prof_lambda_cov_map
      $A $B $X $P $Q $O
      (@Prof_eval_cov_map $A $B $X $P $Q $O $t)
  ↪ $t
with @Prof_eval_cov_map
      $A $B $X $P $Q $O
      (@Prof_lambda_cov_map $A $B $X $P $Q $O $t)
  ↪ $t;

/*
  Contravariant profunctor implication.

  For P : Prof(A,B) and O : Prof(A,X):

    Prof_imply_con(P,O) : Prof(B,X)

  is the symbolic right adjoint to tensoring on the left by P. As for the
  covariant implication, the object remains opaque and its computational
  content is exposed through reindexing and the eval/lambda calculus.
*/
symbol Prof_imply_con [A B X : Cat]
  (P : τ (Prof A B))
  (O : τ (Prof A X))
  : τ (Prof B X);

// Reindexing the implication result acts on the right endpoints of both inputs.
rule @Prof_reindex
      $B $B'
      $X $X'
      (@Prof_imply_con $A $B $X $P $O)
      $M
      $G
  ↪ @Prof_imply_con
      $A $B' $X'
      (@Prof_reindex
        $A $A $B $B'
        $P
        (@id_func $A)
        $M)
      (@Prof_reindex
        $A $A $X $X'
        $O
        (@id_func $A)
        $G);

/*
  Vertical contravariant closed core:

    ProfMap(Q, P ⇒ O)  <->  ProfMap(P tensor Q, O).
*/
symbol Prof_eval_con_map
  [A B X : Cat]
  [P : τ (Prof A B)]
  [Q : τ (Prof B X)]
  [O : τ (Prof A X)]
  (t : τ (ProfMap Q (@Prof_imply_con A B X P O)))
  : τ (ProfMap (@Prof_tensor A B X P Q) O);

// Contravariant currying: ProfMap(P tensor Q,O) -> ProfMap(Q,P ⇒ O).
symbol Prof_lambda_con_map
  [A B X : Cat]
  [P : τ (Prof A B)]
  [Q : τ (Prof B X)]
  [O : τ (Prof A X)]
  (t : τ (ProfMap (@Prof_tensor A B X P Q) O))
  : τ (ProfMap Q (@Prof_imply_con A B X P O));

// Contravariant beta/eta: lambda(eval(t)) ↪ t and eval(lambda(t)) ↪ t.
rule @Prof_lambda_con_map
      $A $B $X $P $Q $O
      (@Prof_eval_con_map $A $B $X $P $Q $O $t)
  ↪ $t
with @Prof_eval_con_map
      $A $B $X $P $Q $O
      (@Prof_lambda_con_map $A $B $X $P $Q $O $t)
  ↪ $t;

// 18j. Weighted representability and adjunction-mate preservation

// Ordinary weighted-limit representability, kept separate from the stronger
// computational comparison interface below.
symbol WeightedCone_prof
  [B J J' : Cat]
  (F : τ (Functor J B))
  (W : τ (Prof J' J))
  : τ (Prof B J')
≔ @Prof_imply_cov
    B J' J
    (@Hom_prof J B F)
    W;

// Ordinary weighted-limit property: WeightedCone(F,W) is represented by L.
symbol IsWeightedLimit_cov_iso
  [B J J' : Cat]
  (F : τ (Functor J B))
  (W : τ (Prof J' J))
  (L : τ (Functor J' B))
  : Grpd
≔ @IsRepresentedBy_iso
    B J'
    (@WeightedCone_prof B J J' F W)
    L;

/*
  Computational weighted-limit representability.

  One ambient comparison internalizes the probe. Reindexing it along
  M : I -> B supplies inverse operations on every incoming profunctor map.
  Selected universal/cone maps are obtained directly by applying these
  operations to identities; beta/eta itself remains on the dedicated
  comparison eliminators, not on separate selected-map wrappers.
*/
symbol IsWeightedLimit_cov_comp
  [B J J' : Cat]
  (F : τ (Functor J B))
  (W : τ (Prof J' J))
  (L : τ (Functor J' B))
  : Grpd
≔ @ProfComparison
    B J'
    (@WeightedCone_prof B J J' F W)
    (@Hom_prof J' B L);

// Forward universal operation after reindexing the limit comparison along M.
symbol weighted_limit_cov_push
  [B J J' : Cat]
  [F : τ (Functor J B)]
  [W : τ (Prof J' J)]
  [L : τ (Functor J' B)]
  (isl : τ (@IsWeightedLimit_cov_comp B J J' F W L))
  [I : Cat]
  (M : τ (Functor I B))
  [R : τ (Prof I J')]
  (r : τ (ProfMap
      R
      (@Prof_imply_cov
        I J' J
        (@Hom_prof_along I J B M F)
        W)))
  : τ (ProfMap R (@Hom_prof_along I J' B M L))
≔ @prof_comparison_push
    I J'
    _
    _
    (@prof_comparison_fmap
      B J' I J'
      (@Prof_reindex_func B I J' J' M (@id_func J'))
      _
      _
      isl)
    R
    r;

// Inverse universal operation after reindexing the limit comparison along M.
symbol weighted_limit_cov_pull
  [B J J' : Cat]
  [F : τ (Functor J B)]
  [W : τ (Prof J' J)]
  [L : τ (Functor J' B)]
  (isl : τ (@IsWeightedLimit_cov_comp B J J' F W L))
  [I : Cat]
  (M : τ (Functor I B))
  [R : τ (Prof I J')]
  (s : τ (ProfMap R (@Hom_prof_along I J' B M L)))
  : τ (ProfMap
      R
      (@Prof_imply_cov
        I J' J
        (@Hom_prof_along I J B M F)
        W))
≔ @prof_comparison_pull
    I J'
    _
    _
    (@prof_comparison_fmap
      B J' I J'
      (@Prof_reindex_func B I J' J' M (@id_func J'))
      _
      _
      isl)
    R
    s;

/*
  Computational adjunction/profunctor mate.

  For adj : Adjunction(Ladj,Radj), M : I -> A, and F : K -> B, the mate comparison
  expresses the representable hom isomorphism

    Hom_B(left(M),F) <-> Hom_A(M,right(F)).

  The strict owner is the ambient ProfComparison certificate below. Selected
  mate maps are obtained by applying `prof_comparison_push/pull` or
  `defiso_to/from` at the use site; they are not independent runtime owners.
*/
injective symbol Adjunction_hom_prof_comparison
  [A B : Cat]
  [Ladj : τ (Functor A B)]
  [Radj : τ (Functor B A)]
  (adj : τ (@Adjunction A B Ladj Radj))
  : τ (ProfComparison
      (@Hom_prof_along
        A B B
        Ladj
        (@id_func B))
      (@Hom_prof_along
        A B A
        (@id_func A)
        Radj));

// Reindexed adjunction mate: Hom_B(LM,F) ≃ Hom_A(M,RF).
symbol Adjunction_hom_prof_comparison_along
  [A B : Cat]
  [Ladj : τ (Functor A B)]
  [Radj : τ (Functor B A)]
  (adj : τ (@Adjunction A B Ladj Radj))
  [I K : Cat]
  (M : τ (Functor I A))
  (F : τ (Functor K B))
  : τ (ProfComparison
      (@Hom_prof_along
        I K B
        (@comp_cat_fapp0
          I A B
          Ladj
          M)
        F)
      (@Hom_prof_along
        I K A
        M
        (@comp_cat_fapp0
          K B A
          Radj
          F)))
≔ @prof_comparison_fmap
    A B I K
    (@Prof_reindex_func A I B K M F)
    _
    _
    (@Adjunction_hom_prof_comparison A B Ladj Radj adj);

/*
  Computational right-adjoint preservation.

  This parallel API composes three certified comparisons:

    1. the inverse adjunction mate through fixed-weight implication;
    2. the given weighted-limit comparison reindexed along the left adjoint;
    3. the adjunction mate at the candidate limit.

  Its beta/eta laws are inherited from `prof_comparison_push/pull`; no
  theorem-specific fold or cancellation rule is added to ordinary equipment
  composition.
*/
symbol right_adjoint_weighted_limit_comp_step1
  [B J J' A : Cat]
  [Ladj : τ (Functor A B)]
  [Radj : τ (Functor B A)]
  [W : τ (Prof J' J)]
  [F : τ (Functor J B)]
  (adj : τ (@Adjunction A B Ladj Radj))
  : τ (ProfComparison
      (@Prof_imply_cov
        A J' J
        (@Hom_prof
          J A
          (@comp_cat_fapp0
            J B A
            Radj
            F))
        W)
      (@Prof_imply_cov
        A J' J
        (@Hom_prof_along
          A J B
          Ladj
          F)
        W))
≔ @prof_comparison_fmap
    A J A J'
    (@Prof_imply_cov_func A J' J W)
    _
    _
    (@prof_comparison_sym
      A J
      _
      _
      (@Adjunction_hom_prof_comparison_along
        A B Ladj Radj adj
        A J
        (@id_func A)
        F));

// Preservation step 2: reindex the supplied weighted-limit comparison along L.
symbol right_adjoint_weighted_limit_comp_step2
  [B J J' A : Cat]
  [Ladj : τ (Functor A B)]
  [Radj : τ (Functor B A)]
  [W : τ (Prof J' J)]
  [F : τ (Functor J B)]
  [L : τ (Functor J' B)]
  (isl : τ (@IsWeightedLimit_cov_comp B J J' F W L))
  (adj : τ (@Adjunction A B Ladj Radj))
  : τ (ProfComparison
      (@Prof_imply_cov
        A J' J
        (@Hom_prof_along
          A J B
          Ladj
          F)
        W)
      (@Hom_prof_along
        A J' B
        Ladj
        L))
≔ @prof_comparison_fmap
    B J' A J'
    (@Prof_reindex_func
      B A J' J'
      Ladj
      (@id_func J'))
    _
    _
    isl;

// Preservation step 3: apply the adjunction mate to the candidate limit L.
symbol right_adjoint_weighted_limit_comp_step3
  [B J J' A : Cat]
  [Ladj : τ (Functor A B)]
  [Radj : τ (Functor B A)]
  [L : τ (Functor J' B)]
  (adj : τ (@Adjunction A B Ladj Radj))
  : τ (ProfComparison
      (@Hom_prof_along
        A J' B
        Ladj
        L)
      (@Hom_prof
        J' A
        (@comp_cat_fapp0
          J' B A
          Radj
          L)))
≔ @Adjunction_hom_prof_comparison_along
    A B Ladj Radj adj
    A J'
    (@id_func A)
    L;

// Composite certificate that a right adjoint preserves the weighted limit.
symbol right_adjoint_preserves_weighted_limit_cov_comp
  [B J J' A : Cat]
  [Ladj : τ (Functor A B)]
  [Radj : τ (Functor B A)]
  [W : τ (Prof J' J)]
  [F : τ (Functor J B)]
  [L : τ (Functor J' B)]
  (isl : τ (@IsWeightedLimit_cov_comp B J J' F W L))
  (adj : τ (@Adjunction A B Ladj Radj))
  : τ (@IsWeightedLimit_cov_comp
      A J J'
      (@comp_cat_fapp0
        J B A
        Radj
        F)
      W
      (@comp_cat_fapp0
        J' B A
        Radj
        L))
≔ @prof_comparison_comp
    A J'
    _ _ _
    (@right_adjoint_weighted_limit_comp_step3
      B J J' A Ladj Radj L adj)
    (@prof_comparison_comp
      A J'
      _ _ _
      (@right_adjoint_weighted_limit_comp_step2
        B J J' A Ladj Radj W F L isl adj)
      (@right_adjoint_weighted_limit_comp_step1
        B J J' A Ladj Radj W F adj));

/*
  Contravariant weighted colimits by duality.

  For F : J -> B, W : Prof(J,J'), and L : J' -> B, the colimit witness is
  definitionally the covariant weighted-limit witness in the opposite category:

    IsWeightedLimit_cov_comp(Op F, Op_prof W, Op L).

  This keeps one universal-property owner. Direct colimit-oriented projection
  names remain deferred until a downstream formula requires them.
*/
symbol WeightedColimit_con [B J J' : Cat]
  (F : τ (Functor J B))
  (W : τ (Prof J J'))
  (L : τ (Functor J' B))
  : Grpd
≔ @IsWeightedLimit_cov_comp
    (Op_cat B)
    (Op_cat J)
    (Op_cat J')
    (@Op_func J B F)
    (@Op_prof J J' W)
    (@Op_func J' B L);

// The two conversions are identity wrappers after opposite involution and
// double product-swap pullback cancellation.
symbol Op_weighted_limit_cov
  [B J J' : Cat]
  [F : τ (Functor J B)]
  [W : τ (Prof J' J)]
  [L : τ (Functor J' B)]
  (isl : τ (@IsWeightedLimit_cov_comp B J J' F W L))
  : τ (@WeightedColimit_con
      (Op_cat B)
      (Op_cat J)
      (Op_cat J')
      (@Op_func J B F)
      (@Op_prof J' J W)
      (@Op_func J' B L))
≔ isl;

// Convert a weighted colimit witness to the opposite weighted-limit witness.
symbol Op_weighted_colimit_con
  [B J J' : Cat]
  [F : τ (Functor J B)]
  [W : τ (Prof J J')]
  [L : τ (Functor J' B)]
  (isc : τ (@WeightedColimit_con B J J' F W L))
  : τ (@IsWeightedLimit_cov_comp
      (Op_cat B)
      (Op_cat J)
      (Op_cat J')
      (@Op_func J B F)
      (@Op_prof J J' W)
      (@Op_func J' B L))
≔ isc;

/*
  Left adjoints preserve weighted colimits.

  Applying right-adjoint preservation to Op_adjunction(adj) makes its right
  adjoint Op(left(adj)), so the result is definitionally the desired colimit
  witness after Op_func distributes over composition.
*/
symbol left_adjoint_preserves_weighted_colimit_con
  [A J J' B : Cat]
  [Ladj : τ (Functor A B)]
  [Radj : τ (Functor B A)]
  [F : τ (Functor J A)]
  [W : τ (Prof J J')]
  [L : τ (Functor J' A)]
  (isc : τ (@WeightedColimit_con A J J' F W L))
  (adj : τ (@Adjunction A B Ladj Radj))
  : τ (@WeightedColimit_con
      B J J'
      (@comp_cat_fapp0 J A B Ladj F)
      W
      (@comp_cat_fapp0 J' A B Ladj L))
≔ @right_adjoint_preserves_weighted_limit_cov_comp
    (Op_cat A)
    (Op_cat J)
    (Op_cat J')
    (Op_cat B)
    (@Op_func B A Radj)
    (@Op_func A B Ladj)
    (@Op_prof J J' W)
    (@Op_func J A F)
    (@Op_func J' A L)
    isc
    (@Op_adjunction A B Ladj Radj adj);

// 18k. Directed-inductive join and internally natural cross arrows

/*
  Directed-inductive join category.

  This is a primitive nondependent recursor stress test, not a claim that the
  kernel already has a generic higher-inductive or collage construction.

  The old draft quantified externally over shaped cross arrows and added a
  separate naturality equation. Here that data is one internal equipment cell:

    Terminal_prof(A,B) -> Hom_prof_along(first,second).

  Thus naturality in both endpoints is owned by `Prof_transf_cat`.
*/

// Constant terminal Cat-valued profunctor.
symbol Terminal_prof (A B : Cat)
  : τ (Prof A B)
≔ @Const_catd (Product_cat (Op_cat A) B) Terminal_cat;

// Unique shaped element of the terminal profunctor.
constant symbol Prof_terminal_hom [I A B : Cat]
  (F : τ (Functor I A))
  (G : τ (Functor I B))
  : τ (@Prof_hom I A B F (@Terminal_prof A B) G);

// Terminal-source specialization of narrow cell application.
symbol Prof_cell_eval
  [I A' B' A B : Cat]
  [R : τ (Prof A B)]
  [F : τ (Functor A' A)]
  [G : τ (Functor B' B)]
  [a : τ (Functor I A')]
  [b : τ (Functor I B')]
  (c : τ (Obj
      (@Prof_transf_cat A A' B B'
        (@Terminal_prof A' B') F R G)))
  : τ (@Prof_hom
      I A B
      (@comp_cat_fapp0 I A' A F a)
      R
      (@comp_cat_fapp0 I B' B G b))
≔ @Prof_cell_apply
    I A' B' A B
    (@Terminal_prof A' B')
    R
    F G a b
    c
    (@Prof_terminal_hom I A' B' a b);

// Primitive join and its two category introductions.
injective symbol Join_cat (A B : Cat) : Cat;

// Left join introduction: inl : A ⊢ A ⋆ B.
constant symbol join_fst_func (A B : Cat)
  : τ (Functor A (@Join_cat A B));

// Right join introduction: inr : B ⊢ A ⋆ B.
constant symbol join_snd_func (A B : Cat)
  : τ (Functor B (@Join_cat A B));

// Internally natural family of all directed cross arrows from A to B.
constant symbol join_cross_transf (A B : Cat)
  : τ (Obj
      (@Prof_transf_cat
        (@Join_cat A B) A
        (@Join_cat A B) B
        (@Terminal_prof A B)
        (@join_fst_func A B)
        (@Unit_prof (@Join_cat A B))
        (@join_snd_func A B)));

// Shaped cross arrow derived from the internally natural cross cell.
symbol join_cross_hom [A B I : Cat]
  (a : τ (Functor I A))
  (b : τ (Functor I B))
  : τ (@Prof_hom
      I
      (@Join_cat A B)
      (@Join_cat A B)
      (@comp_cat_fapp0
        I A (@Join_cat A B)
        (@join_fst_func A B)
        a)
      (@Unit_prof (@Join_cat A B))
      (@comp_cat_fapp0
        I B (@Join_cat A B)
        (@join_snd_func A B)
        b))
≔ @Prof_cell_eval
    I A B
    (@Join_cat A B)
    (@Join_cat A B)
    (@Unit_prof (@Join_cat A B))
    (@join_fst_func A B)
    (@join_snd_func A B)
    a b
    (@join_cross_transf A B);

/*
  Nondependent join recursor.

  `cross` is a single natural equipment cell, rather than a family of
  Lambdapi-quantified shaped elements plus a separate coherence proof.
*/
symbol join_elim_func [A B E : Cat]
  (first : τ (Functor A E))
  (second : τ (Functor B E))
  (cross : τ (Obj
      (@Prof_transf_cat
        E A E B
        (@Terminal_prof A B)
        first
        (@Unit_prof E)
        second)))
  : τ (Functor (@Join_cat A B) E);

// Primitive join-recursion beta for the internally natural cross cell.
symbol join_elim_cross_transf [A B E : Cat]
  (first : τ (Functor A E))
  (second : τ (Functor B E))
  (cross : τ (Obj
      (@Prof_transf_cat
        E A E B
        (@Terminal_prof A B)
        first
        (@Unit_prof E)
        second)))
  : τ (Obj
      (@Prof_transf_cat
        E A E B
        (@Terminal_prof A B)
        first
        (@Unit_prof E)
        second));

// Join recursor beta on the natural cross-cell datum.
rule @join_elim_cross_transf $A $B $E $first $second $cross
  ↪ $cross;

// Join recursor betas: elim ∘ inl ↪ first and elim ∘ inr ↪ second.
rule @comp_fapp0
      Cat_cat
      $A
      _
      $E
      (@join_elim_func $A $B $E $first $second $cross)
      (@join_fst_func $A $B)
  ↪ $first
with @comp_fapp0
      Cat_cat
      $B
      _
      $E
      (@join_elim_func $A $B $E $first $second $cross)
      (@join_snd_func $A $B)
  ↪ $second;

// -------------------------------------------------------------------------------------------------
// 18z. Late cross-section normalization bridges
// -------------------------------------------------------------------------------------------------

// These cuts intentionally live at the end of the profunctor section, after the
// product, pullback, profunctor, implication, adjunction, duality, weighted
// limit, and join systems they join. They are executable rules, so they must
// remain before the section-19 applications, but they are not part of those
// applications.

// There is deliberately no whole-constructor
// `Product_map_func(id,id) -> id_func(Product_cat ...)` rule: for an arbitrary
// opaque product object that would require the rejected broad product eta law.

// Runtime accumulation of Cat-valued pullback through outer composition.
rule @comp_fapp0
      Cat_cat
      $A
      $B
      Cat_cat
      (@Pullback_catd $B $C $E $F)
      $H
  ↪ @Pullback_catd
      $A
      $C
      $E
      (@comp_fapp0 Cat_cat $A $B $C $F $H);

// lhs-audit: keep 2,3,4 -- product source/middle/target categories guard componentwise product-map composition.
rule @comp_fapp0
      Cat_cat
      (Product_cat $A0 $B0)
      (Product_cat $A1 $B1)
      (Product_cat $A2 $B2)
      (@Product_map_func $A1 $A2 $B1 $B2 $F12 $G12)
      (@Product_map_func $A0 $A1 $B0 $B1 $F01 $G01)
  ↪ @Product_map_func
      $A0 $A2 $B0 $B2
      (@comp_fapp0 Cat_cat $A0 $A1 $A2 $F12 $F01)
      (@comp_fapp0 Cat_cat $B0 $B1 $B2 $G12 $G01);

/*
  Product-map identity comparisons.

  Rewriting Product_map_func(id,id) to either id_func or the projection pair
  creates competing object and hom-action normal forms. At proof/elaboration
  time, however, both comparisons are useful and coherent. The stable
  Product_map_func head acts as the rigid intermediary because Lambdapi's
  unifier does not chain a direct id_func-versus-Struct_sigma eta rule.
*/
unif_rule
  @Product_map_func
    $A $A $B $B
    (@id Cat_cat $A)
    (@id Cat_cat $B)
  ≡ @Struct_sigma
      (Obj (Functor_cat (Product_cat $A $B) $A))
      (λ _ : τ (Obj (Functor_cat (Product_cat $A $B) $A)),
        Obj (Functor_cat (Product_cat $A $B) $B))
      (@Product_projL_func $A $B)
      (@Product_projR_func $A $B)
  ↪ [ tt ≡ tt ];

unif_rule
  @id Cat_cat (Product_cat $A $B)
  ≡ @Product_map_func
      $A $A $B $B
      (@id Cat_cat $A)
      (@id Cat_cat $B)
  ↪ [ tt ≡ tt ];

/*
  Generic product-map pullback as profunctor reindexing.

  Here F is an arbitrary functor A -> A'. Pulling a Cat-valued family on
  A' x B' back along Product_map_func(F,G) is the same object as reindexing
  the corresponding profunctor from Op(A') to B' along Op_func(F) and G.
  The object-level and functor-level folds share that normal form.
*/
// lhs-audit: keep 1,2 -- product source/target guard the product-map base
rule @Pullback_catd
      (Product_cat $A $B)
      (Product_cat $A' $B')
      $R
      (@Product_map_func $A $A' $B $B' $F $G)
  ↪ @Prof_reindex
      (Op_cat $A')
      (Op_cat $A)
      $B'
      $B
      $R
      (@Op_func $A $A' $F)
      $G;

// Functor-level product-map pullback folds to profunctor reindexing.
rule @Pullback_catd_func
      _
      _
      (@Product_map_func $A $A' $B $B' $F $G)
  ↪ @Prof_reindex_func
      (Op_cat $A')
      (Op_cat $A)
      $B'
      $B
      (@Op_func $A $A' $F)
      $G;


// -------------------------------------------------------------------------------------------------
// 19. Applications: PathOut, path induction, and transitivity
// -------------------------------------------------------------------------------------------------

// 19a. Outgoing-path categories and fixed-source path induction

// Fixed-x layer: outgoing-path category at a fixed source object.
//
// Surface/formula:
//   PathOut_Z(x) = Σ y :^n Z, Hom_Z(x,y)
//   object notation: (y,p) with p : Hom_Z(x,y).
symbol PathOut_cat [Z : Cat] (x : τ (Obj Z)) : Cat
≔ @Sigma_cat Z (@Rep_catd Z x);

// Internalized-x layer: PathOut as a contravariant functor of the source.
//
// Surface/formula:
//   PathOut_cat_func(Z) : Z^op ⊢ Cat
//   PathOut_cat_func(Z)[x] = PathOut_Z(x)
//   PathOut_cat_func(Z)[p : x ->^Z y] : PathOut_Z(y) ⊢ PathOut_Z(x).
symbol PathOut_cat_func [Z : Cat]
  : τ (Functor (Op_cat Z) Cat_cat)
≔ @comp_cat_fapp0
     (Op_cat Z)
     (@Catd_cat Z)
     Cat_cat
     (@Sigma_func Z)
     (@Rep_catd_func Z);

// Internalized-x layer: readable name for PathOut's action on a base arrow.
//
// Surface/formula:
//   PathOut_transport_func(p) = PathOut_cat_func(Z)[p]
//   : PathOut_Z(y) ⊢ PathOut_Z(x)
//   and PathOut_transport_func(p)[(y,id_y)] = (y,p).
symbol PathOut_transport_func [Z : Cat] [x y : τ (Obj Z)]
  (p : τ (Hom Z x y))
  : τ (Functor (@PathOut_cat Z y) (@PathOut_cat Z x))
≔ @fapp1_fapp0
    (Op_cat Z)
    Cat_cat
    (@PathOut_cat_func Z)
    y
    x
    p;

// 19b. PathOut motives and fixed-source path induction
//
// Internalized-x layer: family of motive categories over source objects.
//
// Surface/formula:
//   PathOutMotives_Z[x] = Catd(PathOut_Z(x))
//   i.e. a fibre object E is a motive E : PathOut_Z(x) ⊢ Cat.
symbol PathOutMotives_catd [Z : Cat]
  : τ (Catd Z)
≔ @Pullback_catd
     Z
     (Op_cat Cat_cat)
     Catd_cat_func
     (@Op_func (Op_cat Z) Cat_cat (@PathOut_cat_func Z));

// Internalized-x target layer: Pi over the moving PathOut category.
//
// Surface/formula:
//   PathOutPi_Z : x :^n Z ; Catd(PathOut_Z(x)) ⊢ Cat
//   PathOutPi_Z[x][E] = Π q :^n PathOut_Z(x), E[q].
//
// This is deliberately the semantic pullback of `Pi_int_funcd` along
// `Op_func(PathOut_cat_func Z)`, then folded to `Pi_pullback_funcd`.
symbol PathOutPi_funcd [Z : Cat]
  : τ (Functord (@PathOutMotives_catd Z) (@Const_catd Z Cat_cat))
≔ @fapp1_fapp0
    (@Catd_cat (Op_cat Cat_cat))
    (@Catd_cat Z)
    (@Pullback_catd_func
      Z
      (Op_cat Cat_cat)
      (@Op_func (Op_cat Z) Cat_cat (@PathOut_cat_func Z)))
    Catd_cat_func
    (@Const_catd (Op_cat Cat_cat) Cat_cat)
    Pi_int_funcd;

// Internalized-x target layer: total target family for path induction.
//
// Surface/formula:
//   PathIndTgt_Z[(x,E)] = Π q :^n PathOut_Z(x), E[q]
//   over Σ x :^n Z, Catd(PathOut_Z(x)).
symbol PathIndTgt_catd [Z : Cat]
  : τ (Catd (@Sigma_cat Z (@PathOutMotives_catd Z)))
≔ @Sigma_catd_functord_catd
    Z
    (@PathOutMotives_catd Z)
    (@PathOutPi_funcd Z);

// Fixed-x notation: object `(y,p)` of PathOut_Z(x).
//
// Surface/formula:
//   pathout_obj(x;y,p) = (y,p).
symbol pathout_obj [Z : Cat] (x y : τ (Obj Z))
  (p : τ (Hom Z x y))
  : τ (Obj (@PathOut_cat Z x))
≔ Struct_sigma y p;

// Fixed-x notation: distinguished reflexive outgoing path.
//
// Surface/formula:
//   reflout_x = (x,id_x) : PathOut_Z(x).
symbol pathout_refl_obj [Z : Cat] (x : τ (Obj Z))
  : τ (Obj (@PathOut_cat Z x))
≔ @pathout_obj Z x x (@id Z x);

// Fixed-x source layer: evaluation at the reflexive outgoing path.
//
// Surface/formula:
//   pathout_refl_eval_func(Z,x)[E] = E[(x,id_x)].
//
// The base-arrow helper below records the concrete map along p; the full
// coherence package remains abstract.
symbol pathout_refl_eval_func [Z : Cat] (x : τ (Obj Z))
  : τ (Functor (@Catd_cat (@PathOut_cat Z x)) Cat_cat)
≔ @fapp0_func
     (@PathOut_cat Z x)
     Cat_cat
     (@pathout_refl_obj Z x);

// Internalized-x source layer: displayed package of fixed-source reflexive
// evaluation.
//
// Surface/formula:
//   PathOutReflEval_Z : x :^n Z ; Catd(PathOut_Z(x)) ⊢ Cat
//   PathOutReflEval_Z[x][E] = E[(x,id_x)].
constant symbol PathOutReflEval_funcd [Z : Cat]
  : τ (Functord (@PathOutMotives_catd Z) (@Const_catd Z Cat_cat));

// Source component: PathOutReflEval_Z[x] ↪ evaluation at (x,id_x).
rule @tapp0_fapp0
      _
      Cat_cat
      _
      _
      $x
      (@PathOutReflEval_funcd $Z)
  ↪ @pathout_refl_eval_func $Z $x;

// Reflexive-to-path arrow in the outgoing-path category.
//
// Surface/formula:
//   rho_{x,y,p} : (x,id_x) ->^PathOut_Z(x) (y,p).
//
// This is the canonical Sigma transport arrow for Rep_Z(x). Its endpoint
// reduces by Rep_Z(x)[p](id_x) = p.
symbol pathout_refl_arrow [Z : Cat] (x y : τ (Obj Z))
  (p : τ (Hom Z x y))
  : τ (Hom
      (@PathOut_cat Z x)
      (@pathout_refl_obj Z x)
      (@pathout_obj Z x y p))
≔ @sigma_transport_arrow
    Z
    (@Rep_catd Z x)
    x
    y
    p
    (@id Z x);

// Fixed-x source layer: motive transport along `rho_{x,y,p}`.
//
// Surface/formula:
//   E[rho_{x,y,p}] : E[(x,id_x)] ⊢ E[(y,p)].
symbol pathout_refl_eval_base_func [Z : Cat] [x y : τ (Obj Z)]
  (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x)))
  : τ (Functor
      (Fibre_cat E (@pathout_refl_obj Z x))
      (Fibre_cat E (@pathout_obj Z x y p)))
≔ @fapp1_fapp0
    (@PathOut_cat Z x)
    Cat_cat
    E
    (@pathout_refl_obj Z x)
    (@pathout_obj Z x y p)
    (@pathout_refl_arrow Z x y p);

// Internalized-x source/target base layer: transport a motive along a moving
// source arrow.
//
// Surface/formula:
//   p_*E = PathOutMotives_Z[p](E)
//        = Pullback_catd(E, PathOut_transport_func(p))
//   so p_*E : PathOut_Z(y) ⊢ Cat.
symbol pathout_motive_transport_obj [Z : Cat] [x y : τ (Obj Z)]
  (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x)))
  : τ (Catd (@PathOut_cat Z y))
≔ @fapp0
    (@Catd_cat (@PathOut_cat Z x))
    (@Catd_cat (@PathOut_cat Z y))
    (@fapp1_fapp0
      Z
      Cat_cat
      (@PathOutMotives_catd Z)
      x
      y
      p)
    E;

// Internalized-x source/target base layer: canonical total arrow in
// Σ x :^n Z, Catd(PathOut_Z(x)).
//
// Surface/formula:
//   (x,E) ->^Σ (y,p_*E), lying over p : x ->^Z y.
symbol pathout_motive_transport_arrow [Z : Cat]
  [x y : τ (Obj Z)]
  (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x)))
  : τ (Hom
      (@Sigma_cat Z (@PathOutMotives_catd Z))
      (Struct_sigma x E)
      (Struct_sigma y (@pathout_motive_transport_obj Z x y p E)))
≔ @sigma_transport_arrow
    Z
    (@PathOutMotives_catd Z)
    x
    y
    p
    E;

// Final desired fixed-x theorem/object: path induction section.
//
// Surface/formula:
//   path_ind_sec(x,E,u) : Π q :^n PathOut_Z(x), E[q]
//   with u : E[(x,id_x)].
symbol path_ind_sec [Z : Cat] (x : τ (Obj Z))
  (E : τ (Catd (@PathOut_cat Z x)))
  (u : τ (Obj (Fibre_cat E (@pathout_refl_obj Z x))))
  : τ (Obj (Pi_cat E));

// Fixed-x packaging layer: section collecting all `rho_{x,y,p}`, derived as
// path induction on the representable motive at the reflexive outgoing path.
//
// Surface/formula:
//   pathout_refl_arrow_sec(x) :
//     Π q :^n PathOut_Z(x), Hom_{PathOut_Z(x)}((x,id_x),q)
//   pathout_refl_arrow_sec(x)[(y,p)] = rho_{x,y,p}.
symbol pathout_refl_arrow_sec [Z : Cat] (x : τ (Obj Z))
  : τ (Obj (Pi_cat
      (@Rep_catd
        (@PathOut_cat Z x)
        (@pathout_refl_obj Z x))))
≔ @path_ind_sec
    Z
    x
    (@Rep_catd
      (@PathOut_cat Z x)
      (@pathout_refl_obj Z x))
    (@id (@PathOut_cat Z x) (@pathout_refl_obj Z x));

// Fixed-x internal layer: source family of path induction at fixed x.
//
// Surface/formula:
//   PathInd_src(Z,x)[E] = E[(x,id_x)].
symbol PathInd_src_catd [Z : Cat] (x : τ (Obj Z))
  : τ (Catd (@Catd_cat (@PathOut_cat Z x)))
≔ @pathout_refl_eval_func Z x;

// Fixed-x internal layer: target family of path induction at fixed x.
//
// Surface/formula:
//   PathInd_tgt(Z,x)[E] = Π q :^n PathOut_Z(x), E[q].
symbol PathInd_tgt_catd [Z : Cat] (x : τ (Obj Z))
  : τ (Catd (@Catd_cat (@PathOut_cat Z x)))
≔ @Pi_func (@PathOut_cat Z x);

// Fixed-x internal layer: component functor of the fixed-source eliminator.
//
// Surface/formula:
//   path_ind_func_fapp0(Z,x,E) : E[(x,id_x)] ⊢ Π q, E[q]
//   path_ind_func_fapp0(Z,x,E)[u] = path_ind_sec(Z,x,E,u).
symbol path_ind_func_fapp0 [Z : Cat] (x : τ (Obj Z))
  (E : τ (Catd (@PathOut_cat Z x)))
  : τ (Functor
      (Fibre_cat E (@pathout_refl_obj Z x))
      (Pi_cat E));

// Object action: the eliminator sends u to the section path_ind_sec(x,E,u).
rule @fapp0 _ _ (@path_ind_func_fapp0 $Z $x $E) $u
  ↪ @path_ind_sec $Z $x $E $u;

// Final desired fixed-x theorem packaged as a displayed functor.
//
// Surface/formula:
//   PathInd_func(Z,x) :
//     E :^n Catd(PathOut_Z(x)) ; E[(x,id_x)] ⊢ Π q, E[q].
constant symbol PathInd_func [Z : Cat] (x : τ (Obj Z))
  : τ (Functord
      (@PathInd_src_catd Z x)
      (@PathInd_tgt_catd Z x));

// Motive component: PathInd_func(Z,x)[E] ↪ path_ind_func_fapp0(Z,x,E).
rule @tapp0_fapp0
      _
      Cat_cat
      _
      _
      $E
      (@PathInd_func $Z $x)
  ↪ @path_ind_func_fapp0 $Z $x $E;

// Primary synthetic/telescope path-induction theorem over the varying source
// object.
//
// Surface/formula:
//   PathInd_transfd(Z) :
//     x :^n Z ; PathOutReflEval_Z[x] => PathOutPi_Z[x]
//   PathInd_transfd(Z)[x] = PathInd_func(Z,x).
//
// Status/architecture note:
//   This `Transfd` is the primary internalized-x theorem. Its type already
//   internalizes naturality in the source object x; we should not re-express
//   that naturality as an external hand-written square for the core milestone.
//   What downstream regressions inspect are the induced source/target
//   transports along p : x ->^Z y:
//
//     source: E[rho_{x,y,p}]
//     target: section_pullback(PathOut_transport(p),E)
//
//   The target transport computes through the component-level displayed laxity
//   cell for `PathOutPi_funcd`; this is shared by the telescope theorem and its
//   derived Sigma-total presentation.
//
// The component projection rule is installed later, after the generic
// displayed-transfor head `tdapp0_fapp0` is declared.
constant symbol PathInd_transfd [Z : Cat]
  : τ (@Transfd
      Z
      (@PathOutMotives_catd Z)
      (@Const_catd Z Cat_cat)
      (@PathOutReflEval_funcd Z)
      (@PathOutPi_funcd Z));

// 19c. Sigma-total presentation of path induction
//
// Internalized-x source layer: total source family over moving `(x,E)`.
//
// Surface/formula:
//   PathIndSrc_Z[(x,E)] = E[(x,id_x)]
//   over Σ x :^n Z, Catd(PathOut_Z(x)).
symbol PathIndSrc_catd [Z : Cat]
  : τ (Catd (@Sigma_cat Z (@PathOutMotives_catd Z)))
≔ @Sigma_catd_functord_catd
    Z
    (@PathOutMotives_catd Z)
    (@PathOutReflEval_funcd Z);

// Internalized-x source layer: source transport along the canonical total
// transported-motive arrow.
//
// Surface/formula:
//   PathIndSrc_transport(p,E) = E[rho_{x,y,p}]
//   : E[(x,id_x)] ⊢ (p_*E)[(y,id_y)] = E[(y,p)].
symbol PathIndSrc_transport_func [Z : Cat] [x y : τ (Obj Z)]
  (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x)))
  : τ (Functor
      (Fibre_cat (@PathIndSrc_catd Z) (Struct_sigma x E))
      (Fibre_cat
        (@PathIndSrc_catd Z)
        (Struct_sigma y (@pathout_motive_transport_obj Z x y p E))))
≔ @pathout_refl_eval_base_func Z x y p E;

// Uncurried Sigma-total presentation of path induction, derived from the
// primary telescope theorem by generic Sigma-total uncurrying.
//
// Surface/formula:
//   PathInd_funcd(Z) :
//     x,E :^n Σ x :^n Z, Catd(PathOut_Z(x)) ;
//       E[(x,id_x)] ⊢ Π q :^n PathOut_Z(x), E[q]
//   PathInd_funcd(Z)[(x,E)][u] = path_ind_sec(Z,x,E,u).
//
// This is a derived presentation, not the primitive theorem. It is used to
// inspect the Sigma-style formulation at canonical/cartesian total arrows
// coming from transport of `(x,E)`. Arbitrary non-cartesian Sigma-arrow
// naturality is intentionally outside the current milestone.
symbol PathInd_funcd [Z : Cat]
  : τ (Functord
      (@PathIndSrc_catd Z)
      (@PathIndTgt_catd Z))
≔ @Sigma_transfd_funcd
    Z
    (@PathOutMotives_catd Z)
    (@PathOutReflEval_funcd Z)
    (@PathOutPi_funcd Z)
    (@PathInd_transfd Z);

/*
  Mathematical computation statements for fixed-x path induction.

  These describe the source/target fibres and the component of the packaged
  fixed-source eliminator. The Sigma-total component statements live with the
  generic uncurrying projection, after `tdapp0_fapp0` is available.
*/

// 19d. Transitivity benchmark
//
// Transitivity benchmark layer: target family for composition out of a fixed
// source x.
//
// Surface/formula:
//   CompTarget_Z(x)[y] = Rep_Z(y) ⊢ Rep_Z(x)
//                      = Functord_cat(Rep_Z(y),Rep_Z(x)).
//
// This is a semantic `hom_con` alias, not a primitive stable family head. The
// transitivity benchmark checks that path induction on the corresponding
// motive computes to post/precomposition in representables.
injective symbol CompTarget_catd [Z : Cat] (x : τ (Obj Z))
  : τ (Catd Z)
≔ @hom_con
    (@Catd_cat Z)
    (@Rep_catd Z x)
    (Op_cat Z)
    (@Rep_catd_func Z);

// Transitivity benchmark layer: readable alias for the capped hom-action of
// `CompTarget_catd`.
//
// Surface/formula:
//   CompTarget_Z(x)[p : a ->^Z b]
//     : (Rep_Z(a) ⊢ Rep_Z(x)) ⊢ (Rep_Z(b) ⊢ Rep_Z(x)).
//
// Its endpoint type uses canonical `Functord_cat` forms rather than reducible
// `Fibre_cat` wrappers, but its body still goes through `CompTarget_catd`
// itself.
symbol CompTarget_fapp1_func [Z : Cat] [x a b : τ (Obj Z)]
  (p : τ (Hom Z a b))
  : τ (Functor
      (@Functord_cat Z (@Rep_catd Z a) (@Rep_catd Z x))
      (@Functord_cat Z (@Rep_catd Z b) (@Rep_catd Z x)))
≔ @fapp1_fapp0
    Z
    Cat_cat
    (@CompTarget_catd Z x)
    a
    b
    p;

// Transitivity benchmark layer: composition motive over PathOut_Z(x).
//
// Surface/formula:
//   CompMotive_Z(x)[(y,p)] = Rep_Z(y) ⊢ Rep_Z(x).
//
// This is the pullback of `CompTarget_Z(x)` along the Sigma projection
// PathOut_Z(x) ⊢ Z.
symbol CompMotive_catd [Z : Cat] (x : τ (Obj Z))
  : τ (Catd (@PathOut_cat Z x))
≔ @Sigma_proj1_pullback_catd
     Z
     (@Rep_catd Z x)
     (@CompTarget_catd Z x);

// Component projection for the primary synthetic/telescope path-induction theorem.
rule @tdapp0_fapp0 $Z _ _ _ _ $x (@PathInd_transfd $Z)
  ↪ @PathInd_func $Z $x;

// LHS indexing guard: unlike ordinary inferred source/family slots, both
// compounds below are required here. Dropping the source makes rule checking
// exceed the bounded check; dropping the family also does so, and retaining
// only the family fails subject reduction. Keep this explicit pair unless a
// focused probe establishes a replacement decision-tree shape.
// lhs-audit: keep 1,3 -- measured subject-reduction and performance guard
rule @tapp0_fapp0
      (@Sigma_cat $Z (@hom_ $Z $Z (@id Cat_cat $Z) $x))
      Cat_cat
      (@Const_catd (@Sigma_cat $Z (@hom_ $Z $Z (@id Cat_cat $Z) $x)) Terminal_cat)
      $E
      (Struct_sigma $y $p)
      (@path_ind_sec $Z $x $E $u)
  ↪ @Obj_func
      (Fibre_cat $E (Struct_sigma $y $p))
      (@fapp0
        (Hom_cat (@PathOut_cat $Z $x)
          (@pathout_refl_obj $Z $x)
          (Struct_sigma $y $p))
        (Fibre_cat $E (Struct_sigma $y $p))
        (@fib_cov_tapp0_func
          (@PathOut_cat $Z $x)
          $E
          (@pathout_refl_obj $Z $x)
          (Struct_sigma $y $p)
          $u)
        (@pathout_refl_arrow $Z $x $y $p));

// Sigma-pullback motive computation: path induction folds to fibre covariance.
rule @path_ind_sec $Z $x
      (@Sigma_proj1_pullback_catd $Z (@hom_ $Z $Z (@id Cat_cat $Z) $x) $D)
      $u
  ↪ @fib_cov_transf $Z $D $x $u;

/*
  Proof-time reflexive component join for structured path-category induction.

  The section-level `path_ind_sec` fold can expose `fib_cov_transf` before the
  component projection fires. The two rigid heads below identify the
  reflexive terminal-source component only after the residual constraints
  verify the exact PathOut/Sigma-pullback presentation. This is a proof-time
  comparison, not a runtime reduction or a general constant-component law.
*/
unif_rule
  @tapp0_fapp0
      $K
      Cat_cat
      $F
      $G
      $k
      (@fib_cov_transf (Path_cat $A) $D $x $u)
  ≡ @Const_func
      Terminal_cat
      (@fapp0 (Path_cat $A) Cat_cat $D $x)
      $u
  ↪ [
      $K ≡ @PathOut_cat (Path_cat $A) $x;
      $F ≡ @Const_catd (@PathOut_cat (Path_cat $A) $x) Terminal_cat;
      $G ≡ @Sigma_proj1_pullback_catd
        (Path_cat $A)
        (@Rep_catd (Path_cat $A) $x)
        $D;
      $k ≡ @pathout_obj (Path_cat $A) $x $x (@eq_refl $A $x)
    ];

/*
  Literal path-category comparison between structured action and primitive J.

  `path_cat_structured_transport` is the existing directed-family action;
  `path_cat_ind_eqr_transport` is primitive right-J with a function-valued
  motive. The agreement proofs use `ind_eqr`, the functor-identity comparison
  above, and the reflexive component join. No second eliminator, opaque
  decoder, or implicit term coercion is introduced.
*/

// Structured transport applies the displayed functor action along p.
symbol path_cat_structured_transport
  [A : Grpd]
  (D : τ (Catd (Path_cat A)))
  [x y : τ A]
  (u : τ (Obj (Fibre_cat D x)))
  (p : τ (@= A x y))
  : τ (Obj (Fibre_cat D y))
≔ @fapp0
    (Hom_cat (Path_cat A) x y)
    (Fibre_cat D y)
    (@fib_cov_tapp0_func (Path_cat A) D x y u)
    p;

// Primitive right-J transport uses a function-valued motive to move u.
symbol path_cat_ind_eqr_transport
  [A : Grpd]
  (D : τ (Catd (Path_cat A)))
  [x y : τ A]
  (u : τ (Obj (Fibre_cat D x)))
  (p : τ (@= A x y))
  : τ (Obj (Fibre_cat D y))
≔ (@ind_eqr
      A
      y
      (λ z : τ A, λ _ : τ (@= A z y),
        @Function_grpd (Obj (Fibre_cat D z)) (Obj (Fibre_cat D y)))
      (λ v : τ (Obj (Fibre_cat D y)), v)
      x
      p)
    u;

// Functorial structured transport agrees propositionally with primitive J.
symbol path_cat_structured_transport_agrees_ind_eqr
  [A : Grpd]
  (D : τ (Catd (Path_cat A)))
  [x y : τ A]
  (u : τ (Obj (Fibre_cat D x)))
  (p : τ (@= A x y))
  : τ (@=
      (Obj (Fibre_cat D y))
      (@path_cat_structured_transport A D x y u p)
      (@path_cat_ind_eqr_transport A D x y u p))
≔ (@ind_eqr
      A
      y
      (λ z : τ A, λ q : τ (@= A z y),
        @Pi_grpd
          (Obj (Fibre_cat D z))
          (λ v : τ (Obj (Fibre_cat D z)),
            @=
              (Obj (Fibre_cat D y))
              (@path_cat_structured_transport A D z y v q)
              (@path_cat_ind_eqr_transport A D z y v q)))
      (λ v : τ (Obj (Fibre_cat D y)),
        @eq_ap
          (Hom Cat_cat (Fibre_cat D y) (Fibre_cat D y))
          (Obj (Fibre_cat D y))
          (λ H : τ (Hom Cat_cat (Fibre_cat D y) (Fibre_cat D y)),
            @fapp0 (Fibre_cat D y) (Fibre_cat D y) H v)
          (@fapp1_fapp0
            (Path_cat A)
            Cat_cat
            D
            y y
            (@eq_refl A y))
          (@id Cat_cat (Fibre_cat D y))
          (@eq_refl
            (Hom Cat_cat (Fibre_cat D y) (Fibre_cat D y))
            (@fapp1_fapp0
              (Path_cat A)
              Cat_cat
              D
              y y
              (@eq_refl A y))))
      x
      p)
    u;

// Evaluate the existing structured path-induction section at (y,p).
symbol path_cat_path_ind_app
  [A : Grpd]
  (D : τ (Catd (Path_cat A)))
  [x y : τ A]
  (u : τ (Obj (Fibre_cat D x)))
  (p : τ (@= A x y))
  : τ (Obj (Fibre_cat D y))
≔ @piapp0
    (@PathOut_cat (Path_cat A) x)
    (@Sigma_proj1_pullback_catd
      (Path_cat A)
      (@Rep_catd (Path_cat A) x)
      D)
    (@path_ind_sec
      (Path_cat A)
      x
      (@Sigma_proj1_pullback_catd
        (Path_cat A)
        (@Rep_catd (Path_cat A) x)
        D)
      u)
    (@pathout_obj (Path_cat A) x y p);

// Existing structured path induction agrees with the displayed action.
symbol path_cat_path_ind_app_agrees_structured
  [A : Grpd]
  (D : τ (Catd (Path_cat A)))
  [x y : τ A]
  (u : τ (Obj (Fibre_cat D x)))
  (p : τ (@= A x y))
  : τ (@=
      (Obj (Fibre_cat D y))
      (@path_cat_path_ind_app A D x y u p)
      (@path_cat_structured_transport A D x y u p))
≔ (@ind_eqr
      A
      y
      (λ z : τ A, λ q : τ (@= A z y),
        @Pi_grpd
          (Obj (Fibre_cat D z))
          (λ v : τ (Obj (Fibre_cat D z)),
            @=
              (Obj (Fibre_cat D y))
              (@path_cat_path_ind_app A D z y v q)
              (@path_cat_structured_transport A D z y v q)))
      (λ v : τ (Obj (Fibre_cat D y)),
        @eq_trans
          (Obj (Fibre_cat D y))
          (@path_cat_path_ind_app A D y y v (@eq_refl A y))
          v
          (@path_cat_structured_transport A D y y v (@eq_refl A y))
          (@eq_ap
            (Hom Cat_cat Terminal_cat (Fibre_cat D y))
            (Obj (Fibre_cat D y))
            (λ H : τ (Hom Cat_cat Terminal_cat (Fibre_cat D y)),
              @fapp0 Terminal_cat (Fibre_cat D y) H Terminal_obj)
            (@tapp0_fapp0
              (@PathOut_cat (Path_cat A) y)
              Cat_cat
              (@Const_catd (@PathOut_cat (Path_cat A) y) Terminal_cat)
              (@Sigma_proj1_pullback_catd
                (Path_cat A)
                (@Rep_catd (Path_cat A) y)
                D)
              (@pathout_obj (Path_cat A) y y (@eq_refl A y))
              (@fib_cov_transf (Path_cat A) D y v))
            (@Obj_func (Fibre_cat D y) v)
            (@eq_refl
              (Hom Cat_cat Terminal_cat (Fibre_cat D y))
              (@tapp0_fapp0
                (@PathOut_cat (Path_cat A) y)
                Cat_cat
                (@Const_catd (@PathOut_cat (Path_cat A) y) Terminal_cat)
                (@Sigma_proj1_pullback_catd
                  (Path_cat A)
                  (@Rep_catd (Path_cat A) y)
                  D)
                (@pathout_obj (Path_cat A) y y (@eq_refl A y))
                (@fib_cov_transf (Path_cat A) D y v))))
          (@eq_sym
            (Obj (Fibre_cat D y))
            (@path_cat_structured_transport A D y y v (@eq_refl A y))
            v
            (@path_cat_structured_transport_agrees_ind_eqr
              A D y y v (@eq_refl A y))))
      x
      p)
    u;

// Existing structured path induction agrees with primitive right-J transport.
symbol path_cat_path_ind_app_agrees_ind_eqr
  [A : Grpd]
  (D : τ (Catd (Path_cat A)))
  [x y : τ A]
  (u : τ (Obj (Fibre_cat D x)))
  (p : τ (@= A x y))
  : τ (@=
      (Obj (Fibre_cat D y))
      (@path_cat_path_ind_app A D x y u p)
      (@path_cat_ind_eqr_transport A D x y u p))
≔ @eq_trans
    (Obj (Fibre_cat D y))
    (@path_cat_path_ind_app A D x y u p)
    (@path_cat_structured_transport A D x y u p)
    (@path_cat_ind_eqr_transport A D x y u p)
    (@path_cat_path_ind_app_agrees_structured A D x y u p)
    (@path_cat_structured_transport_agrees_ind_eqr A D x y u p);

// Mathematical computation statement: fixed-x path induction on a
// Sigma-projection pullback motive reduces to covariant fibre transport.

// Final desired transitivity benchmark theorem/object.
//
// Surface/formula:
//   path_comp_sec(x) :
//     p :^n Rep_Z(x)[y] ; Rep_Z(y) ⊢ Rep_Z(x)
//   path_comp_sec(x)[p][z][q] = q ∘ p.
//
// This is the reduced normal form of fixed-x path induction on the composition
// motive.
symbol path_comp_sec [Z : Cat] (x : τ (Obj Z))
  : τ (Obj (@Functord_cat Z (@Rep_catd Z x) (@CompTarget_catd Z x)))
≔ @fib_cov_transf
    Z
    (@CompTarget_catd Z x)
    x
    (@id_funcd Z (@Rep_catd Z x));

// Transitivity benchmark layer: representable action of a path by
// precomposition.
//
// Surface/formula:
//   path_comp_func(p) : Rep_Z(y) ⊢ Rep_Z(x)
//   path_comp_func(p)[z][q] = q ∘ p.
symbol path_comp_func [Z : Cat] [x y : τ (Obj Z)]
  (p : τ (Hom Z x y))
  : τ (Functord (@Rep_catd Z y) (@Rep_catd Z x))
≔ @fapp1_fapp0
    (Op_cat Z)
    (@Catd_cat Z)
    (@Rep_catd_func Z)
    y
    x
    p;

/*
  Mathematical computation statements for the fixed-x transitivity benchmark.

  These are not merely regression probes: they state that fixed-x path
  induction on the composition motive computes to representable
  precomposition, and then to ordinary categorical composition.
*/

// The semantic `hom_con` presentation of `CompTarget_catd` computes without a
// CompTarget-specific identity shortcut.

// 19e. Path-induction target transport aliases
//
// Internalized-x target layer: target-side path-out transport. The transported
// motive remains canonically `PathOutMotives[p](E)`; this helper exposes its
// pullback presentation so Pi sections move by the generic section-pullback
// map.
//
// Surface/formula:
//   pathout_pi_transport(p,E)
//     : Π q :^n PathOut_Z(x), E[q]
//       ⊢ Π q :^n PathOut_Z(y), E[PathOut_transport(p)[q]].
symbol pathout_pi_transport_func [Z : Cat] [x y : τ (Obj Z)]
  (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x)))
  : τ (Functor
      (@Pi_cat (@PathOut_cat Z x) E)
      (@Pi_cat (@PathOut_cat Z y) (@pathout_motive_transport_obj Z x y p E)))
≔ @section_pullback_func
    (@PathOut_cat Z y)
    (@PathOut_cat Z x)
    (@PathOut_transport_func Z x y p)
    E;

// Internalized-x target layer: target transport along the canonical total
// transported-motive arrow.
//
// Surface/formula:
//   PathIndTgt_transport(p,E) = pathout_pi_transport(p,E).
symbol PathIndTgt_transport_func [Z : Cat] [x y : τ (Obj Z)]
  (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x)))
  : τ (Functor
      (Fibre_cat (@PathIndTgt_catd Z) (Struct_sigma x E))
      (Fibre_cat
        (@PathIndTgt_catd Z)
        (Struct_sigma y (@pathout_motive_transport_obj Z x y p E))))
≔ @pathout_pi_transport_func Z x y p E;

/*
  Mathematical computation statements for target transport and the
  source transport over the canonical transported-motive arrow live in the
  checks module.
*/


// 19f. Nested telescope stress examples

/*
  Mixed-variance family constructors.

  Surface/formula:
    Functor_catd(M,N)[k] = M[k^-] ⊢_[k] N[k]
    Hom_catd(E,X,Y)[k] = X[k^-] ->_[k]^E Y[k]
    Transf_catd(M,N,FF,GG)[k] = FF[k^-] =>_[k] GG[k]
    Hom_catd(const Cat, X, Y) = Functor_catd(Op_func(X),Y).
*/

// Nested telescope stress example.
//
// Surface/formula:
//   k |-> (z :^n Z ; E[k^-;z] ⊢ D[k;z])
//   = Hom_{Catd(Z)}(E[k^-],D[k]).
symbol Nested_telescope_catd [K Z : Cat]
  (E : τ (Obj (Pi_cat (@Op_catd K (@Const_catd K (@Catd_cat Z))))))
  (D : τ (Obj (Pi_cat (@Const_catd K (@Catd_cat Z)))))
  : τ (Catd K)
≔ @Hom_catd
    K
    (@Const_catd K (@Catd_cat Z))
    E
    D;

// Full nested telescope category:
//   k :^n K ; C[k] ⊢ (z :^n Z ; E[k^-;z] ⊢ D[k;z]).
symbol Nested_telescope_cat [K Z : Cat]
  (C : τ (Catd K))
  (E : τ (Obj (Pi_cat (@Op_catd K (@Const_catd K (@Catd_cat Z))))))
  (D : τ (Obj (Pi_cat (@Const_catd K (@Catd_cat Z)))))
  : Cat
≔ @Functord_cat K C (@Nested_telescope_catd K Z E D);

// Nested transformation telescope stress example.
//
// Surface/formula:
//   k |-> (z :^n Z ; FF[k^-;z] => GG[k;z])
//   = Hom_{Functord(E,D)}(FF[k^-],GG[k]).
symbol Nested_transfd_telescope_catd [K Z : Cat]
  (E D : τ (Catd Z))
  (FF : τ (Obj (Pi_cat (@Op_catd K (@Const_catd K (@Functord_cat Z E D))))))
  (GG : τ (Obj (Pi_cat (@Const_catd K (@Functord_cat Z E D)))))
  : τ (Catd K)
≔ @Hom_catd
    K
    (@Const_catd K (@Functord_cat Z E D))
    FF
    GG;

// Full nested transformation telescope category:
//   k :^n K ; C[k] ⊢ (z :^n Z ; FF[k^-;z] => GG[k;z]).
symbol Nested_transfd_telescope_cat [K Z : Cat]
  (C : τ (Catd K))
  (E D : τ (Catd Z))
  (FF : τ (Obj (Pi_cat (@Op_catd K (@Const_catd K (@Functord_cat Z E D))))))
  (GG : τ (Obj (Pi_cat (@Const_catd K (@Functord_cat Z E D)))))
  : Cat
≔ @Functord_cat K C (@Nested_transfd_telescope_catd K Z E D FF GG);

// 19g. Eckmann-Hilton first computation slice

/*
  This is the conservative first slice of the Eckmann-Hilton application.
  It introduces reviewer-facing names for the 2-endomorphism category of an
  identity 1-cell and its vertical composition, plus the identity
  postcomposition computations that already hold by reflexivity.

  No horizontal-composition facade or rewrite rule is introduced here.
*/

// 2-endomorphisms of the identity 1-cell at x.
//
// Surface/formula:
//   EH_2End(B,x) = Hom_{Hom_B(x,x)}(id_x,id_x).
symbol EH_2End
  [B : Cat]
  (x : τ (Obj B))
  : Cat
≔ Hom_cat (Hom_cat B x x) (@id B x) (@id B x);

// Vertical composition of 2-endomorphisms.
//
// Surface/formula:
//   EH_vcomp(beta,alpha) = beta · alpha.
symbol EH_vcomp
  [B : Cat]
  (x : τ (Obj B))
  (beta alpha : τ (Obj (@EH_2End B x)))
  : τ (Obj (@EH_2End B x))
≔ @comp_fapp0
    (Hom_cat B x x)
    (@id B x)
    (@id B x)
    (@id B x)
    beta
    alpha;

// Postcomposition by the identity 1-cell computes to the identity functor on
// the endomorphism hom-category.
symbol EH_identity_postcomp
  [B : Cat]
  (x : τ (Obj B))
  : τ (
      @hom_postcomp_func B B (@id_func B) x x x (@id B x)
      =
      @id_func (Hom_cat B x x))
≔ eq_refl (@id_func (Hom_cat B x x));

// Consequently, whiskering a 2-endomorphism by the identity 1-cell computes
// back to the original 2-cell.
symbol EH_identity_whisker
  [B : Cat]
  (x : τ (Obj B))
  (alpha : τ (Obj (@EH_2End B x)))
  : τ (
      @fapp1_fapp0
        (Hom_cat B x x)
        (Hom_cat B x x)
        (@hom_postcomp_func B B (@id_func B) x x x (@id B x))
        (@id B x)
        (@id B x)
        alpha
      =
      alpha)
≔ eq_refl alpha;

// Alias computation for the displayed vertical-composition name.
symbol EH_vcomp_alias
  [B : Cat]
  (x : τ (Obj B))
  (beta alpha : τ (Obj (@EH_2End B x)))
  : τ (
      @EH_vcomp B x beta alpha
      =
      @comp_fapp0
        (Hom_cat B x x)
        (@id B x)
        (@id B x)
        (@id B x)
        beta
        alpha)
≔ eq_refl
    (@comp_fapp0
      (Hom_cat B x x)
      (@id B x)
      (@id B x)
      (@id B x)
      beta
      alpha);

// Horizontal unit 2-cell for the identity 1-cell.
symbol EH_one
  [B : Cat]
  (x : τ (Obj B))
  : τ (Obj (@EH_2End B x))
≔ @id (Hom_cat B x x) (@id B x);

// Pre-configured horizontal composition of two 2-endomorphisms, expressed as
// represented postcomposition action. This is the computational surface used
// by the Eckmann-Hilton proof rather than a separate primitive hcomp.
symbol EH_hcomp
  [B : Cat]
  (x : τ (Obj B))
  (beta alpha : τ (Obj (@EH_2End B x)))
  : τ (Obj (@EH_2End B x))
≔ @tapp1_fapp0
    (Hom_cat B x x)
    (Hom_cat B x x)
    (@hom_postcomp_func B B (@id_func B) x x x (@id B x))
    (@hom_postcomp_func B B (@id_func B) x x x (@id B x))
    (@id B x)
    (@id B x)
    (@hom_postcomp_tele_fapp1_fapp0
      B B (@id_func B) x x x (@id B x) (@id B x) beta)
    alpha;

// Left horizontal unit: 1 * alpha = alpha.
symbol EH_hcomp_left_unit
  [B : Cat]
  (x : τ (Obj B))
  (alpha : τ (Obj (@EH_2End B x)))
  : τ (
      @EH_hcomp B x (@EH_one B x) alpha
      =
      alpha)
≔ eq_refl alpha;

// Right horizontal unit: beta * 1 = beta.
symbol EH_hcomp_right_unit
  [B : Cat]
  (x : τ (Obj B))
  (beta : τ (Obj (@EH_2End B x)))
  : τ (
      @EH_hcomp B x beta (@EH_one B x)
      =
      beta)
≔ eq_refl beta;

// First shared-middle equality for the Eckmann-Hilton chain:
//   beta · alpha = beta * alpha.
symbol EH_vcomp_to_shared_middle
  [B : Cat]
  (x : τ (Obj B))
  (alpha beta : τ (Obj (@EH_2End B x)))
  : τ (
      @EH_vcomp B x beta alpha
      =
      @EH_hcomp B x beta alpha)
≔ @hom_postcomp_representable_interchange_eq
    B
    x
    x
    x
    (@id B x)
    (@id B x)
    (@id B x)
    (@EH_one B x)
    beta
    (@id B x)
    (@id B x)
    (@id B x)
    alpha
    (@EH_one B x);

// Second shared-middle equality:
//   alpha · beta = beta * alpha.
symbol EH_swapped_vcomp_to_shared_middle
  [B : Cat]
  (x : τ (Obj B))
  (alpha beta : τ (Obj (@EH_2End B x)))
  : τ (
      @EH_vcomp B x alpha beta
      =
      @EH_hcomp B x beta alpha)
≔ @hom_postcomp_representable_interchange_eq
    B
    x
    x
    x
    (@id B x)
    (@id B x)
    (@id B x)
    beta
    (@EH_one B x)
    (@id B x)
    (@id B x)
    (@id B x)
    (@EH_one B x)
    alpha;

// Eckmann-Hilton commutativity for 2-endomorphisms of an identity 1-cell.
symbol EH_comm
  [B : Cat]
  (x : τ (Obj B))
  (alpha beta : τ (Obj (@EH_2End B x)))
  : τ (
      @EH_vcomp B x beta alpha
      =
      @EH_vcomp B x alpha beta)
≔ @eq_trans
    (Hom (Hom_cat B x x) (@id B x) (@id B x))
    (@EH_vcomp B x beta alpha)
    (@EH_hcomp B x beta alpha)
    (@EH_vcomp B x alpha beta)
    (@EH_vcomp_to_shared_middle B x alpha beta)
    (eq_sym (@EH_swapped_vcomp_to_shared_middle B x alpha beta));

// -------------------------------------------------------------------------------------------------
// 20. Equality-local category skeleton and restricted Core inclusion
// -------------------------------------------------------------------------------------------------

/*
  Recursive equality-local skeleton.

  Sk⁼(0,A) is the path core of A.  Each successor retains the objects and
  current directed hom dimension of A, then recursively replaces all higher
  cells by equality action.  This is not a universal IsNCat truncation: no
  sethood of the retained hom objects is asserted.
*/

// Sk⁼(n,A): retain n directed dimensions and replace higher cells by paths.
injective symbol EqSkeleton_cat
  (n : CatDim)
  (A : Cat)
  : Cat;

// The zero skeleton is the existing path core.
rule EqSkeleton_cat cat_zero $A
  ↪ Core_cat $A;

// Every skeleton retains the objects of its source category.
rule Obj (EqSkeleton_cat _ $A)
  ↪ Obj $A;

// A successor skeleton recurses through the source hom-category.
rule Hom_cat (EqSkeleton_cat (cat_succ $n) $A) $x $y
  ↪ EqSkeleton_cat $n (Hom_cat $A $x $y);

// Successor identities are inherited from the source category.
rule @id (EqSkeleton_cat (cat_succ _) $A) $x
  ↪ @id $A $x;

/*
  Successor composition is genuinely inherited computation.  This rule
  intentionally retains that runtime contract even though the open category
  projection overlaps generic composition/naturality families; those warning
  locations are diagnostic evidence, not a reason to weaken the operation to
  proof-time equality.
*/
rule
  @comp_fapp0
    (EqSkeleton_cat (cat_succ _) $A)
    $w $x $y $g $f
  ↪ @comp_fapp0 $A $w $x $y $g $f;

// Simultaneous action of Sk⁼ on a fixed ordinary functor.
injective symbol eq_skeleton_map_func
  (n : CatDim)
  [A B : Cat]
  (F : τ (Functor A B))
  : τ (Functor
      (EqSkeleton_cat n A)
      (EqSkeleton_cat n B));

// At zero this is the existing internal path-map action.
rule @eq_skeleton_map_func cat_zero $A $B $F
  ↪ @path_map_func
      (Obj $A)
      (Obj $B)
      (@functor_object_function $A $B $F);

// Object action agrees with the underlying functor at every dimension.
rule @fapp0
      _ _
      (@eq_skeleton_map_func _ $A $B $F)
      $x
  ↪ @fapp0 $A $B $F $x;

// Successor hom action is the recursively skeletonized hom functor.
rule @fapp1_func
      _ _
      (@eq_skeleton_map_func (cat_succ $n) $A $B $F)
      $x $y
  ↪ @eq_skeleton_map_func
      $n
      (Hom_cat $A $x $y)
      (Hom_cat $B
        (@fapp0 $A $B $F $x)
        (@fapp0 $A $B $F $y))
      (@fapp1_func $A $B $F $x $y);

// Capped successor action evaluates the recursively skeletonized hom action.
rule
  @fapp1_fapp0
    _ _
    (@eq_skeleton_map_func (cat_succ $n) $A $B $F)
    $x $y $f
  ↪ @fapp0
      (EqSkeleton_cat $n (Hom_cat $A $x $y))
      (EqSkeleton_cat $n
        (Hom_cat $B
          (@fapp0 $A $B $F $x)
          (@fapp0 $A $B $F $y)))
      (@eq_skeleton_map_func
        $n
        (Hom_cat $A $x $y)
        (Hom_cat $B
          (@fapp0 $A $B $F $x)
          (@fapp0 $A $B $F $y))
        (@fapp1_func $A $B $F $x $y))
      $f;

// The simultaneous action preserves identity at the whole-functor level.
rule @eq_skeleton_map_func $n $A $A (@id Cat_cat $A)
  ↪ @id Cat_cat (EqSkeleton_cat $n $A);

// The simultaneous action preserves composition at the whole-functor level.
rule @comp_fapp0
      Cat_cat
      _ _ _
      (@eq_skeleton_map_func $n $B $C $G)
      (@eq_skeleton_map_func $n $A $B $F)
  ↪ @eq_skeleton_map_func
      $n $A $C
      (@comp_fapp0 Cat_cat $A $B $C $G $F);

// Recursive canonical inclusion Sk⁼(n,A) -> A.
injective symbol eq_skeleton_incl_func
  (n : CatDim)
  (A : Cat)
  : τ (Functor (EqSkeleton_cat n A) A);

// At zero this is the existing Core inclusion.
rule eq_skeleton_incl_func cat_zero $A
  ↪ Core_incl_func $A;

// Every inclusion fixes objects.
rule @fapp0
      _ _
      (eq_skeleton_incl_func _ _)
      $x
  ↪ $x;

// Successor hom action is the recursive inclusion.
rule @fapp1_func
      _ _
      (eq_skeleton_incl_func (cat_succ $n) $A)
      $x $y
  ↪ eq_skeleton_incl_func $n (Hom_cat $A $x $y);

// Capped successor inclusion evaluates the recursive hom inclusion.
rule
  @fapp1_fapp0
    _ $A
    (eq_skeleton_incl_func (cat_succ $n) $A)
    $x $y $f
  ↪ @fapp0
      (EqSkeleton_cat $n (Hom_cat $A $x $y))
      (Hom_cat $A $x $y)
      (eq_skeleton_incl_func $n (Hom_cat $A $x $y))
      $f;

/*
  Equality-local category of categories.

  Cat₁⁼ retains categories and ordinary functors, while its higher cells
  are paths between functors.  It is deliberately weaker than a universal
  one-category truncation.
*/
symbol Cat1Eq_cat : Cat
≔ EqSkeleton_cat (cat_succ cat_zero) Cat_cat;

// Evaluate a functor at objects, packaged as a function between classifiers.
symbol functor_object_map_function
  [C D : Cat]
  : τ (@Function_grpd
      (Functor C D)
      (@Function_grpd (Obj C) (Obj D)))
≔ λ F : τ (Functor C D),
    @functor_object_function C D F;

/*
  Hom action of Core₁.  Equality of functors first maps to equality of their
  object functions; the existing iterable Path_cat_func action then supplies
  every remaining equality and higher-equality action.
*/
symbol core1_hom_func
  [C D : Cat]
  : τ (Functor
      (Path_cat (Functor C D))
      (Functor_cat (Core_cat C) (Core_cat D)))
≔ @comp_cat_fapp0
    (Path_cat (Functor C D))
    (Path_cat (@Function_grpd (Obj C) (Obj D)))
    (Functor_cat (Core_cat C) (Core_cat D))
    (@fapp1_func
      Grpd_cat Cat_cat Path_cat_func
      (Obj C) (Obj D))
    (@path_map_func
      (Functor C D)
      (@Function_grpd (Obj C) (Obj D))
      (@functor_object_map_function C D));

// Core₁ : Cat₁⁼ -> Cat, with complete full and capped first-hom projections.
injective symbol Core1_func
  : τ (Functor Cat1Eq_cat Cat_cat);

rule @fapp0 _ _ Core1_func $C
  ↪ Core_cat $C;

rule @fapp1_func _ _ Core1_func $C $D
  ↪ @core1_hom_func $C $D;

/*
  This capped beta is intended runtime computation.  It may erase an outer
  generic identity/composition pattern before that pattern fires; warning
  reports for those competing paths are retained and classified rather than
  weakening this required projection to proof-time equality.
*/
rule @fapp1_fapp0
      _ _ Core1_func $C $D $F
  ↪ @fapp0
      (Path_cat (Functor $C $D))
      (Functor_cat (Core_cat $C) (Core_cat $D))
      (@core1_hom_func $C $D)
      $F;

// J is the recursive canonical inclusion Cat₁⁼ -> Cat.
symbol Cat1Eq_incl_func
  : τ (Functor Cat1Eq_cat Cat_cat)
≔ eq_skeleton_incl_func (cat_succ cat_zero) Cat_cat;

/*
  The first off-diagonal projection of CoreInclTransf is the common diagonal
  functor Core(C) -> D.  It is Core₁'s hom action followed by CoreIncl(D).
*/
symbol core_incl_diagonal_func
  [C D : Cat]
  : τ (Functor
      (Path_cat (Functor C D))
      (Functor_cat (Core_cat C) D))
≔ @comp_cat_fapp0
    (Path_cat (Functor C D))
    (Functor_cat (Core_cat C) (Core_cat D))
    (Functor_cat (Core_cat C) D)
    (@comp_cat_cov_func
      (Core_cat C) (Core_cat D) D
      (Core_incl_func D))
    (@core1_hom_func C D);

// Restricted Core inclusion, internalized over equality-local Cat₁⁼.
injective symbol CoreInclTransf
  : τ (Transf Core1_func Cat1Eq_incl_func);

// Object component: CoreInclTransf[C] = CoreIncl(C).
rule @tapp0_fapp0
      _ _ _ _ $C CoreInclTransf
  ↪ Core_incl_func $C;

// Complete first-hom action: equality paths of functors act on the diagonal.
rule @tapp1_func
      _ _ _ _ $C $D CoreInclTransf
  ↪ @core_incl_diagonal_func $C $D;

// Capped first-hom projection at an ordinary functor F.
rule @tapp1_fapp0
      _ _ _ _ $C $D CoreInclTransf $F
  ↪ @fapp0
      (Path_cat (Functor $C $D))
      (Functor_cat (Core_cat $C) $D)
      (@core_incl_diagonal_func $C $D)
      $F;

// Capped diagonal selected by CoreInclTransf at the ordinary functor F.
symbol core_incl_transf_diagonal_fapp0
  [C D : Cat]
  (F : τ (Functor C D))
  : τ (Functor (Core_cat C) D)
≔ @tapp1_fapp0
    Cat1Eq_cat Cat_cat
    Core1_func Cat1Eq_incl_func
    C D CoreInclTransf F;

/*
  Explicit naturality square associated to CoreInclTransf at F.  Its
  projections are inherited from the common diagonal; the two boundary
  functors deliberately remain distinct runtime presentations.
*/
injective symbol core_incl_transf_kappa
  [C D : Cat]
  (F : τ (Functor C D))
  : τ (Transf
      (@comp_cat_fapp0
        (Core_cat C) C D
        (@fapp1_fapp0
          Cat1Eq_cat Cat_cat Cat1Eq_incl_func C D F)
        (@tapp0_fapp0
          Cat1Eq_cat Cat_cat
          Core1_func Cat1Eq_incl_func
          C CoreInclTransf))
      (@comp_cat_fapp0
        (Core_cat C) (Core_cat D) D
        (@tapp0_fapp0
          Cat1Eq_cat Cat_cat
          Core1_func Cat1Eq_incl_func
          D CoreInclTransf)
        (@fapp1_fapp0
          Cat1Eq_cat Cat_cat Core1_func C D F)));

// Point component of the explicit square is identity on the common diagonal.
rule @tapp0_fapp0
      _ $D _ _ $x
      (@core_incl_transf_kappa $C $D $F)
  ↪ @id
      $D
      (@fapp0
        (Core_cat $C) $D
        (@core_incl_transf_diagonal_fapp0 $C $D $F)
        $x);

// Full off-diagonal action is inherited from the common diagonal functor.
rule @tapp1_func
      _ $D _ _ $x $y
      (@core_incl_transf_kappa $C $D $F)
  ↪ @fapp1_func
      (Core_cat $C) $D
      (@core_incl_transf_diagonal_fapp0 $C $D $F)
      $x $y;

// Capped off-diagonal action is the common diagonal's arrow action.
rule @tapp1_fapp0
      _ $D _ _ $x $y
      (@core_incl_transf_kappa $C $D $F)
      $p
  ↪ @fapp1_fapp0
      (Core_cat $C) $D
      (@core_incl_transf_diagonal_fapp0 $C $D $F)
      $x $y $p;

// Readable semantic PathLift object selected by its internal functor.
symbol path_lift_fapp0
  [A : Grpd]
  [C : Cat]
  (p : τ (@Function_grpd A (Obj C)))
  : τ (Functor (Path_cat A) C)
≔ @fapp0
    (Path_cat (@Function_grpd A (Obj C)))
    (Functor_cat (Path_cat A) C)
    (@path_lift_func A C)
    p;

// Precomposition by PathMap(p), used to whisker the explicit kappa square.
symbol core_incl_transf_kappa_whisker_func
  [A : Grpd]
  [C D : Cat]
  (p : τ (@Function_grpd A (Obj C)))
  : τ (Functor
      (Functor_cat (Core_cat C) D)
      (Functor_cat (Path_cat A) D))
≔ @comp_cat_con_func
    (Path_cat A) (Core_cat C) D
    (@path_map_func A (Obj C) p);

// Raw source obtained by generic precomposition of kappa's source.
symbol core_incl_transf_kappa_left_raw_source
  [A : Grpd]
  [C D : Cat]
  (F : τ (Functor C D))
  (p : τ (@Function_grpd A (Obj C)))
  : τ (Functor (Path_cat A) D)
≔ @fapp0
    (Functor_cat (Core_cat C) D)
    (Functor_cat (Path_cat A) D)
    (@core_incl_transf_kappa_whisker_func A C D p)
    (@comp_cat_fapp0
      (Core_cat C) C D
      (@fapp1_fapp0
        Cat1Eq_cat Cat_cat Cat1Eq_incl_func C D F)
      (@tapp0_fapp0
        Cat1Eq_cat Cat_cat
        Core1_func Cat1Eq_incl_func
        C CoreInclTransf));

// Raw target obtained by generic precomposition of kappa's target.
symbol core_incl_transf_kappa_left_raw_target
  [A : Grpd]
  [C D : Cat]
  (F : τ (Functor C D))
  (p : τ (@Function_grpd A (Obj C)))
  : τ (Functor (Path_cat A) D)
≔ @fapp0
    (Functor_cat (Core_cat C) D)
    (Functor_cat (Path_cat A) D)
    (@core_incl_transf_kappa_whisker_func A C D p)
    (@comp_cat_fapp0
      (Core_cat C) (Core_cat D) D
      (@tapp0_fapp0
        Cat1Eq_cat Cat_cat
        Core1_func Cat1Eq_incl_func
        D CoreInclTransf)
      (@fapp1_fapp0
        Cat1Eq_cat Cat_cat Core1_func C D F));

// Generic functor hom-action performs the actual whiskering of kappa.
symbol core_incl_transf_kappa_left_raw
  [A : Grpd]
  [C D : Cat]
  (F : τ (Functor C D))
  (p : τ (@Function_grpd A (Obj C)))
  : τ (Transf
      (@core_incl_transf_kappa_left_raw_source A C D F p)
      (@core_incl_transf_kappa_left_raw_target A C D F p))
≔ @fapp1_fapp0
    (Functor_cat (Core_cat C) D)
    (Functor_cat (Path_cat A) D)
    (@core_incl_transf_kappa_whisker_func A C D p)
    (@comp_cat_fapp0
      (Core_cat C) C D
      (@fapp1_fapp0
        Cat1Eq_cat Cat_cat Cat1Eq_incl_func C D F)
      (@tapp0_fapp0
        Cat1Eq_cat Cat_cat
        Core1_func Cat1Eq_incl_func
        C CoreInclTransf))
    (@comp_cat_fapp0
      (Core_cat C) (Core_cat D) D
      (@tapp0_fapp0
        Cat1Eq_cat Cat_cat
        Core1_func Cat1Eq_incl_func
        D CoreInclTransf)
      (@fapp1_fapp0
        Cat1Eq_cat Cat_cat Core1_func C D F))
    (@core_incl_transf_kappa C D F);

// Proof-time raw-composition reading of the semantic PathLift object.
symbol path_lift_fapp0_raw_path
  [A : Grpd]
  [C : Cat]
  (p : τ (@Function_grpd A (Obj C)))
  : τ (@=
      (Functor (Path_cat A) C)
      (@comp_cat_fapp0
        (Path_cat A) (Path_cat (Obj C)) C
        (Core_incl_func C)
        (@path_map_func A (Obj C) p))
      (@path_lift_fapp0 A C p))
≔ @eq_refl
    (Functor (Path_cat A) C)
    (@comp_cat_fapp0
      (Path_cat A) (Path_cat (Obj C)) C
      (Core_incl_func C)
      (@path_map_func A (Obj C) p));

// Associativity aligns the raw source with F ∘ PathLift(p).
symbol core_incl_transf_kappa_left_source_path
  [A : Grpd]
  [C D : Cat]
  (F : τ (Functor C D))
  (p : τ (@Function_grpd A (Obj C)))
  : τ (@=
      (Functor (Path_cat A) D)
      (@core_incl_transf_kappa_left_raw_source A C D F p)
      (@comp_cat_fapp0
        (Path_cat A) C D
        F (@path_lift_fapp0 A C p)))
≔ @eq_trans
    (Functor (Path_cat A) D)
    (@core_incl_transf_kappa_left_raw_source A C D F p)
    (@comp_cat_fapp0
      (Path_cat A) C D F
      (@comp_cat_fapp0
        (Path_cat A) (Path_cat (Obj C)) C
        (Core_incl_func C)
        (@path_map_func A (Obj C) p)))
    (@comp_cat_fapp0
      (Path_cat A) C D
      F (@path_lift_fapp0 A C p))
    (@eq_sym
      (Functor (Path_cat A) D)
      (@comp_cat_fapp0
        (Path_cat A) C D F
        (@comp_cat_fapp0
          (Path_cat A) (Path_cat (Obj C)) C
          (Core_incl_func C)
          (@path_map_func A (Obj C) p)))
      (@core_incl_transf_kappa_left_raw_source A C D F p)
      (@comp_assoc
        Cat_cat
        (Path_cat A) (Path_cat (Obj C)) C D
        F
        (Core_incl_func C)
        (@path_map_func A (Obj C) p)))
    (@eq_ap
      (Functor (Path_cat A) C)
      (Functor (Path_cat A) D)
      (λ G : τ (Functor (Path_cat A) C),
        @comp_cat_fapp0 (Path_cat A) C D F G)
      (@comp_cat_fapp0
        (Path_cat A) (Path_cat (Obj C)) C
        (Core_incl_func C)
        (@path_map_func A (Obj C) p))
      (@path_lift_fapp0 A C p)
      (@path_lift_fapp0_raw_path A C p));

// Associativity plus PathMap functoriality aligns the raw target.
symbol core_incl_transf_kappa_left_target_path
  [A : Grpd]
  [C D : Cat]
  (F : τ (Functor C D))
  (p : τ (@Function_grpd A (Obj C)))
  : τ (@=
      (Functor (Path_cat A) D)
      (@core_incl_transf_kappa_left_raw_target A C D F p)
      (@path_lift_fapp0
        A D
        (@comp_fapp0
          Grpd_cat
          A (Obj C) (Obj D)
          (@functor_object_function C D F)
          p)))
≔ @eq_trans
    (Functor (Path_cat A) D)
    (@core_incl_transf_kappa_left_raw_target A C D F p)
    (@comp_cat_fapp0
      (Path_cat A) (Core_cat D) D
      (Core_incl_func D)
      (@comp_cat_fapp0
        (Path_cat A) (Core_cat C) (Core_cat D)
        (@path_map_func
          (Obj C) (Obj D)
          (@functor_object_function C D F))
        (@path_map_func A (Obj C) p)))
    (@path_lift_fapp0
      A D
      (@comp_fapp0
        Grpd_cat
        A (Obj C) (Obj D)
        (@functor_object_function C D F)
        p))
    (@eq_sym
      (Functor (Path_cat A) D)
      (@comp_cat_fapp0
        (Path_cat A) (Core_cat D) D
        (Core_incl_func D)
        (@comp_cat_fapp0
          (Path_cat A) (Core_cat C) (Core_cat D)
          (@path_map_func
            (Obj C) (Obj D)
            (@functor_object_function C D F))
          (@path_map_func A (Obj C) p)))
      (@core_incl_transf_kappa_left_raw_target A C D F p)
      (@comp_assoc
        Cat_cat
        (Path_cat A) (Core_cat C) (Core_cat D) D
        (Core_incl_func D)
        (@path_map_func
          (Obj C) (Obj D)
          (@functor_object_function C D F))
        (@path_map_func A (Obj C) p)))
    (@eq_refl
      (Functor (Path_cat A) D)
      (@comp_cat_fapp0
        (Path_cat A) (Core_cat D) D
        (Core_incl_func D)
        (@comp_cat_fapp0
          (Path_cat A) (Core_cat C) (Core_cat D)
          (@path_map_func
            (Obj C) (Obj D)
            (@functor_object_function C D F))
          (@path_map_func A (Obj C) p))));

// Directed source adjustment from the readable endpoint to the raw whisker.
symbol core_incl_transf_kappa_left_source_adjust
  [A : Grpd]
  [C D : Cat]
  (F : τ (Functor C D))
  (p : τ (@Function_grpd A (Obj C)))
  : τ (Transf
      (@comp_cat_fapp0
        (Path_cat A) C D
        F (@path_lift_fapp0 A C p))
      (@core_incl_transf_kappa_left_raw_source A C D F p))
≔ @path_to_hom
    (Functor_cat (Path_cat A) D)
    (@comp_cat_fapp0
      (Path_cat A) C D
      F (@path_lift_fapp0 A C p))
    (@core_incl_transf_kappa_left_raw_source A C D F p)
    (@eq_sym
      (Functor (Path_cat A) D)
      (@core_incl_transf_kappa_left_raw_source A C D F p)
      (@comp_cat_fapp0
        (Path_cat A) C D
        F (@path_lift_fapp0 A C p))
      (@core_incl_transf_kappa_left_source_path A C D F p));

// Directed target adjustment from the raw whisker to the readable endpoint.
symbol core_incl_transf_kappa_left_target_adjust
  [A : Grpd]
  [C D : Cat]
  (F : τ (Functor C D))
  (p : τ (@Function_grpd A (Obj C)))
  : τ (Transf
      (@core_incl_transf_kappa_left_raw_target A C D F p)
      (@path_lift_fapp0
        A D
        (@comp_fapp0
          Grpd_cat
          A (Obj C) (Obj D)
          (@functor_object_function C D F)
          p)))
≔ @path_to_hom
    (Functor_cat (Path_cat A) D)
    (@core_incl_transf_kappa_left_raw_target A C D F p)
    (@path_lift_fapp0
      A D
      (@comp_fapp0
        Grpd_cat
        A (Obj C) (Obj D)
        (@functor_object_function C D F)
        p))
    (@core_incl_transf_kappa_left_target_path A C D F p);

/*
  Genuine left endpoint comparison obtained by generic precomposition of the
  explicit CoreInclTransf kappa.  Associativity and readable PathLift endpoint
  changes are represented by narrow equality-induced directed adjustments;
  no Core-specific whole-functor rewrite or new unification rule is used.
*/
symbol core_incl_transf_kappa_left
  [A : Grpd]
  [C D : Cat]
  (F : τ (Functor C D))
  (p : τ (@Function_grpd A (Obj C)))
  : τ (Transf
      (@comp_cat_fapp0
        (Path_cat A) C D
        F (@path_lift_fapp0 A C p))
      (@path_lift_fapp0
        A D
        (@comp_fapp0
          Grpd_cat
          A (Obj C) (Obj D)
          (@functor_object_function C D F)
          p)))
≔ @comp_fapp0
    (Functor_cat (Path_cat A) D)
    (@comp_cat_fapp0
      (Path_cat A) C D
      F (@path_lift_fapp0 A C p))
    (@core_incl_transf_kappa_left_raw_target A C D F p)
    (@path_lift_fapp0
      A D
      (@comp_fapp0
        Grpd_cat
        A (Obj C) (Obj D)
        (@functor_object_function C D F)
        p))
    (@core_incl_transf_kappa_left_target_adjust A C D F p)
    (@comp_fapp0
      (Functor_cat (Path_cat A) D)
      (@comp_cat_fapp0
        (Path_cat A) C D
        F (@path_lift_fapp0 A C p))
      (@core_incl_transf_kappa_left_raw_source A C D F p)
      (@core_incl_transf_kappa_left_raw_target A C D F p)
      (@core_incl_transf_kappa_left_raw A C D F p)
      (@core_incl_transf_kappa_left_source_adjust A C D F p));

// Right PathLift comparison; current PathInt functoriality makes it identity.
symbol path_lift_kappa_right
  [A B : Grpd]
  [C : Cat]
  (p : τ (@Function_grpd B (Obj C)))
  (s : τ (@Function_grpd A B))
  : τ (Transf
      (@path_lift_fapp0
        A C
        (@comp_fapp0 Grpd_cat A B (Obj C) p s))
      (@comp_cat_fapp0
        (Path_cat A) (Path_cat B) C
        (@path_lift_fapp0 B C p)
        (@path_map_func A B s)))
≔ @id
    (Functor_cat (Path_cat A) C)
    (@path_lift_fapp0
      A C
      (@comp_fapp0 Grpd_cat A B (Obj C) p s));

/*
  Non-strict structured spiral.  The right comparison is definitionally the
  identity, so the selected term is the minimal PathLift(h) o kappa_left.
*/
symbol path_lift_non_strict_spiral
  [A : Grpd]
  [C : Cat]
  (S : τ (Functor C C))
  (p : τ (@Function_grpd A (Obj C)))
  (s : τ (@Function_grpd A A))
  (h : τ (@=
      (@Function_grpd A (Obj C))
      (@comp_fapp0
        Grpd_cat
        A (Obj C) (Obj C)
        (@functor_object_function C C S)
        p)
      (@comp_fapp0 Grpd_cat A A (Obj C) p s)))
  : τ (Transf
      (@comp_cat_fapp0
        (Path_cat A) C C
        S (@path_lift_fapp0 A C p))
      (@comp_cat_fapp0
        (Path_cat A) (Path_cat A) C
        (@path_lift_fapp0 A C p)
        (@path_map_func A A s)))
≔ @comp_fapp0
    (Functor_cat (Path_cat A) C)
    (@comp_cat_fapp0
      (Path_cat A) C C
      S (@path_lift_fapp0 A C p))
    (@path_lift_fapp0
      A C
      (@comp_fapp0
        Grpd_cat
        A (Obj C) (Obj C)
        (@functor_object_function C C S)
        p))
    (@comp_cat_fapp0
      (Path_cat A) (Path_cat A) C
      (@path_lift_fapp0 A C p)
      (@path_map_func A A s))
    (@fapp1_fapp0
      (Path_cat (@Function_grpd A (Obj C)))
      (Functor_cat (Path_cat A) C)
      (@path_lift_func A C)
      (@comp_fapp0
        Grpd_cat
        A (Obj C) (Obj C)
        (@functor_object_function C C S)
        p)
      (@comp_fapp0 Grpd_cat A A (Obj C) p s)
      h)
    (@core_incl_transf_kappa_left A C C S p);
