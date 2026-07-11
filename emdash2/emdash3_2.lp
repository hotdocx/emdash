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
      5f. Product closure for omega-equivalence
      5g. Product-pair telescope declaration
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

  Grouped architecture map:
    - Kernel foundations: 0-3.
    - Ordinary category calculus: 4-7.
    - Directed-family and displayed calculus: 8-17.
    - Profunctor, equipment, and DefIso migration machinery: 18.
    - Applications: 19.

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
rule ind_eqr _ $u (eq_refl _) ↪ $u;

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

// Object-level unit and natural numbers used by examples/probes, not by the
// categorical core itself.
inductive unit : TYPE ≔ | tt : unit;

// Groupoid classifier whose decoded type is the one-element type `unit`.
constant symbol Unit_grpd : Grpd;

// Decoding beta for the unit classifier.
rule τ Unit_grpd ↪ unit;

inductive nat : TYPE ≔
| zero : nat
| succ : nat → nat;

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
rule sigma_Fst (Struct_sigma $1 $2) ↪ $1;

// Second projection of an encoded dependent pair.
injective symbol sigma_Snd [a P] (s : @τΣ_ a P) : τ (P (sigma_Fst s));

// Second-projection beta: `snd(x,u) = u`.
rule sigma_Snd (Struct_sigma $1 $2) ↪ $2;

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

// Product equality uses the corresponding Sigma path view.
rule @= (Product_grpd $A $B) $p $q
  ↪ @SigmaPathView $A (λ _ : τ $A, $B) $p $q;

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

// Path-category composition is equality transitivity.
rule @comp_fapp0 (Path_cat $A) $x $y $z $q $p ↪ eq_trans $p $q;

// The path category is self-opposite at this groupoidal staging level.
rule Op_cat (Path_cat $A) ↪ Path_cat $A;

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
    q ∘ p = eq_trans(p,q)
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

/*
  Core inclusion and path-to-arrow.

  `Core_incl_func(C) : Core_cat(C) ⊢ C` owns the computational map from
  non-directed object paths to directed arrows. Composition is deliberately
  not restated here: the generic `fapp1_fapp0` functoriality rule folds
  path_to_hom(q) ∘ path_to_hom(p) to path_to_hom(eq_trans(p,q)).

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

// Category of categories.
constant symbol Cat_cat : Cat;

// Object classifier of the category universe.
injective symbol Cat_grpd  : Grpd ≔ Obj Cat_cat;

// Universe-object decoding: `Obj(Cat_cat)` decodes to the meta-type `Cat`.
rule τ (Obj Cat_cat)  ↪ Cat;

// Directed-universe beta: a hom in `Cat_cat` is an ordinary functor category.
rule Hom_cat Cat_cat $X $Y ↪ Functor_cat $X $Y;

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

// Stable displayed identity. The ordinary identity at a displayed-functor
// category folds here when that category is still visible; terminal-source
// section cases can use this head directly after Functord_cat contracts to
// Pi_cat.
constant symbol id_transfd [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  : τ (@Transfd K E D FF FF);

// Displayed identity projection at a visible `Functord_cat` head.
rule @id (@Functord_cat $K $E $D) $FF
  ↪ @id_transfd $K $E $D $FF;

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

// Selected global decoder from ordinary isomorphism evidence to object equality.
symbol iso_evidence_path
  [C : Cat]
  [x y : τ (Obj C)]
  (i : τ (IsoEvidence C x y))
  : τ (x = y);

// Decoder beta on reflexive ordinary isomorphism evidence.
rule @iso_evidence_path $C $x $x (@iso_evidence_refl $C $x)
  ↪ eq_refl $x;

// Specified-inverse 1-categorical univalence presentation.
symbol CatIsoUnivalenceByDecoder
  (C : Cat)
  : Grpd
≔ @Pi_grpd (Obj C)
    (λ x : τ (Obj C),
      @Pi_grpd (Obj C)
        (λ y : τ (Obj C),
          @EquivByInverse
            (@= (Obj C) x y)
            (IsoEvidence C x y)
            (λ p : τ (@= (Obj C) x y), @idtoiso_cat C x y p)
            (λ i : τ (IsoEvidence C x y), @iso_evidence_path C x y i)));

// Global operational staging assumption: every active category is
// 1-categorically univalent, i.e. ordinary isomorphism evidence determines an
// object path. This does not replace final omega-categorical univalence.
symbol cat_iso_univalence
  (C : Cat)
  : τ (CatIsoUnivalence C);

// Global decoder-oriented 1-categorical univalence capability.
symbol cat_iso_univalence_by_decoder
  (C : Cat)
  : τ (CatIsoUnivalenceByDecoder C);

/*
  Omega-categorical equivalence is recursive through hom-categories. The
  classifier and destructors are primitive operational heads; no unrestricted
  introduction record or general corecursor is installed. Reflexivity is the
  first canonical generator and owns the only initial destructor computation.
*/

constant symbol OmegaEquiv
  (C : Cat)
  (x y : τ (Obj C))
  : Grpd;

// Forward arrow of an omega-equivalence.
symbol omega_equiv_to
  [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y))
  : τ (Hom C x y);

// Selected left-inverse arrow of an omega-equivalence.
symbol omega_equiv_left_inv
  [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y))
  : τ (Hom C y x);

// Selected right-inverse arrow of an omega-equivalence.
symbol omega_equiv_right_inv
  [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y))
  : τ (Hom C y x);

// Higher equivalence witnessing `left_inv o to ~ id_x`.
symbol omega_equiv_left_cell
  [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y))
  : τ (OmegaEquiv
      (Hom_cat C x x)
      (@comp_fapp0 C x y x
        (omega_equiv_left_inv e)
        (omega_equiv_to e))
      (@id C x));

// Higher equivalence witnessing `to o right_inv ~ id_y`.
symbol omega_equiv_right_cell
  [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y))
  : τ (OmegaEquiv
      (Hom_cat C y y)
      (@comp_fapp0 C y x y
        (omega_equiv_to e)
        (omega_equiv_right_inv e))
      (@id C y));

// Reflexive omega-equivalence generator.
injective symbol omega_equiv_refl
  [C : Cat]
  (x : τ (Obj C))
  : τ (OmegaEquiv C x x);

// Reflexive omega-equivalence projects to identity arrows in all arrow slots.
rule omega_equiv_to (omega_equiv_refl $x) ↪ @id _ $x
with omega_equiv_left_inv (omega_equiv_refl $x) ↪ @id _ $x
with omega_equiv_right_inv (omega_equiv_refl $x) ↪ @id _ $x;

// Higher inverse cells of reflexive equivalence are recursively reflexive.
rule omega_equiv_left_cell (omega_equiv_refl $x)
  ↪ omega_equiv_refl (@id _ $x)
with omega_equiv_right_cell (omega_equiv_refl $x)
  ↪ omega_equiv_refl (@id _ $x);

/*
  Constructor-specific omega-equivalence skeleton.

  `Path_cat(A)` already has paths as arrows, so the safe first computation is
  extraction through existing destructors rather than collapsing the whole
  classifier `OmegaEquiv(Path_cat A,x,y)` to `x = y`.

  `omega_equiv_op` records that omega-equivalence is stable under opposite
  categories. Its destructors compute by routing through the existing
  `Hom_cat(Op_cat C,y,x) -> Hom_cat(C,x,y)` rule; no separate rewrite headed
  by the transparent `Hom` alias is needed.
*/
symbol path_cat_omega_path
  [A : Grpd]
  [x y : τ A]
  (e : τ (OmegaEquiv (Path_cat A) x y))
  : τ (x = y)
≔ omega_equiv_to e;

// Extract the underlying equality path from path-category isomorphism evidence.
symbol path_cat_iso_path
  [A : Grpd]
  [x y : τ A]
  (i : τ (IsoEvidence (Path_cat A) x y))
  : τ (x = y)
≔ iso_evidence_to i;

// Opposite closure reverses the endpoints of an omega-equivalence.
injective symbol omega_equiv_op
  [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y))
  : τ (OmegaEquiv (Op_cat C) y x);

// Opposite of reflexive omega-equivalence is reflexive.
rule @omega_equiv_op $C $x $x (@omega_equiv_refl $C $x)
  ↪ @omega_equiv_refl (Op_cat $C) $x;

// Opposite swaps the selected inverse directions while preserving the arrow view.
rule @omega_equiv_to
      (Op_cat $C)
      $y
      $x
      (@omega_equiv_op $C $x $y $e)
  ↪ @omega_equiv_to $C $x $y $e
with @omega_equiv_left_inv
      (Op_cat $C)
      $y
      $x
      (@omega_equiv_op $C $x $y $e)
  ↪ @omega_equiv_right_inv $C $x $y $e
with @omega_equiv_right_inv
      (Op_cat $C)
      $y
      $x
      (@omega_equiv_op $C $x $y $e)
  ↪ @omega_equiv_left_inv $C $x $y $e;

// Opposite exchanges the two higher inverse cells.
rule @omega_equiv_left_cell
      (Op_cat $C)
      $y
      $x
      (@omega_equiv_op $C $x $y $e)
  ↪ @omega_equiv_right_cell $C $x $y $e
with @omega_equiv_right_cell
      (Op_cat $C)
      $y
      $x
      (@omega_equiv_op $C $x $y $e)
  ↪ @omega_equiv_left_cell $C $x $y $e;

// Convert object equality to recursive omega-equivalence.
symbol idtoequiv_cat
  [C : Cat]
  [x y : τ (Obj C)]
  (p : τ (x = y))
  : τ (OmegaEquiv C x y);

// Reflexive object equality maps to reflexive omega-equivalence.
rule @idtoequiv_cat $C $x $x (eq_refl $x)
  ↪ @omega_equiv_refl $C $x;

// Selected decoder from omega-equivalence to object equality.
symbol omega_equiv_path
  [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y))
  : τ (x = y);

// Decoder beta on reflexive omega-equivalence.
rule @omega_equiv_path $C $x $x (@omega_equiv_refl $C $x)
  ↪ eq_refl $x;

// Omega-categorical univalence capability for `idtoequiv_cat`.
symbol CatUnivalence
  (C : Cat)
  : Grpd
≔ @Pi_grpd (Obj C)
    (λ x : τ (Obj C),
      @Pi_grpd (Obj C)
        (λ y : τ (Obj C),
          @IsEquivMap
            (@= (Obj C) x y)
            (OmegaEquiv C x y)
            (λ p : τ (@= (Obj C) x y), @idtoequiv_cat C x y p)));

// Specified-inverse omega-categorical univalence presentation.
symbol CatUnivalenceByDecoder
  (C : Cat)
  : Grpd
≔ @Pi_grpd (Obj C)
    (λ x : τ (Obj C),
      @Pi_grpd (Obj C)
        (λ y : τ (Obj C),
          @EquivByInverse
            (@= (Obj C) x y)
            (OmegaEquiv C x y)
            (λ p : τ (@= (Obj C) x y), @idtoequiv_cat C x y p)
            (λ e : τ (OmegaEquiv C x y), @omega_equiv_path C x y e)));

// Decode omega-equivalence to object equality using a univalence capability.
symbol equivtoid_cat
  [C : Cat]
  (U : τ (CatUnivalence C))
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y))
  : τ (x = y)
≔ @type_equiv_from
    (@= (Obj C) x y)
    (OmegaEquiv C x y)
    (@Struct_sigma
      (Function_grpd (@= (Obj C) x y) (OmegaEquiv C x y))
      (λ f : τ (Function_grpd (@= (Obj C) x y) (OmegaEquiv C x y)),
        @IsEquivMap (@= (Obj C) x y) (OmegaEquiv C x y) f)
      (λ p : τ (@= (Obj C) x y), @idtoequiv_cat C x y p)
      (U x y))
    e;

// Global operational assumption: the active `Cat` classifier contains
// univalent categories. In particular, since `Cat_cat : Cat`, this includes
// the universe category interface; constructor-specific computation can still
// remain stuck until installed case by case.
symbol cat_univalence
  (C : Cat)
  : τ (CatUnivalence C);

// Global decoder-oriented omega-categorical univalence capability.
symbol cat_univalence_by_decoder
  (C : Cat)
  : τ (CatUnivalenceByDecoder C);

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
rule @hom_postcomp_fapp0
      $D $D (@id Cat_cat $D)
      (@fapp0 $C $D $F $x)
      (@fapp0 $C $D $F $y)
      (@fapp0 $C $D $F $x)
      (@fapp1_fapp0 $C $D $F $y $x (@defiso_from $C $x $y $i))
      (@fapp1_fapp0 $C $D $F $x $y (@defiso_to $C $x $y $i))
  ↪ @id $D (@fapp0 $C $D $F $x)
with @hom_postcomp_fapp0
      $D $D (@id Cat_cat $D)
      (@fapp0 $C $D $F $y)
      (@fapp0 $C $D $F $x)
      (@fapp0 $C $D $F $y)
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

// Product objects are encoded pairs (x,u) with x : Obj(A), u : Obj(B).
rule Obj (Product_cat $A $B)
  ↪ @Σ_ (Obj $A) (λ _ : τ (Obj $A), Obj $B);

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
  arrows and the path decoder.
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

// Product closure preserves reflexive ordinary isomorphism evidence.
rule @iso_evidence_product
      $A
      $B
      $x
      $x
      $y
      $y
      (@iso_evidence_refl $A $x)
      (@iso_evidence_refl $B $y)
  ↪ @iso_evidence_refl
      (Product_cat $A $B)
      (Struct_sigma $x $y);

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

// Decoder of product isomorphism evidence builds the product/Sigma path view.
rule @iso_evidence_path
      (Product_cat $A $B)
      (Struct_sigma $x0 $y0)
      (Struct_sigma $x1 $y1)
      (@iso_evidence_product $A $B $x0 $x1 $y0 $y1 $iA $iB)
  ↪ @Struct_sigma
      (@= (Obj $A) $x0 $x1)
      (λ p : τ (@= (Obj $A) $x0 $x1),
        @PathOver
          (Obj $A)
          (λ _ : τ (Obj $A), Obj $B)
          $x0
          $x1
          p
          $y0
          $y1)
      (@iso_evidence_path $A $x0 $x1 $iA)
      (@const_pathover
        (Obj $A)
        (Obj $B)
        $x0
        $x1
        $y0
        $y1
        (@iso_evidence_path $A $x0 $x1 $iA)
        (@iso_evidence_path $B $y0 $y1 $iB));

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

// 5f. Product closure for omega-equivalence
/*
  Omega-equivalence is closed under explicit product-category pairs.

  This first slice targets visible `Struct_sigma` endpoints. Opaque product
  eta can remain a later refinement; product projections already expose many
  opaque component consumers.
*/
injective symbol omega_equiv_product
  [A B : Cat]
  [x0 x1 : τ (Obj A)]
  [y0 y1 : τ (Obj B)]
  (eA : τ (OmegaEquiv A x0 x1))
  (eB : τ (OmegaEquiv B y0 y1))
  : τ (OmegaEquiv
      (Product_cat A B)
      (Struct_sigma x0 y0)
      (Struct_sigma x1 y1));

// Product closure preserves reflexive omega-equivalence.
rule @omega_equiv_product
      $A
      $B
      $x
      $x
      $y
      $y
      (@omega_equiv_refl $A $x)
      (@omega_equiv_refl $B $y)
  ↪ @omega_equiv_refl
      (Product_cat $A $B)
      (Struct_sigma $x $y);

// Arrow and inverse projections of product omega-equivalence are componentwise.
rule @omega_equiv_to
      (Product_cat $A $B)
      (Struct_sigma $x0 $y0)
      (Struct_sigma $x1 $y1)
      (@omega_equiv_product $A $B $x0 $x1 $y0 $y1 $eA $eB)
  ↪ Struct_sigma
      (@omega_equiv_to $A $x0 $x1 $eA)
      (@omega_equiv_to $B $y0 $y1 $eB)
with @omega_equiv_left_inv
      (Product_cat $A $B)
      (Struct_sigma $x0 $y0)
      (Struct_sigma $x1 $y1)
      (@omega_equiv_product $A $B $x0 $x1 $y0 $y1 $eA $eB)
  ↪ Struct_sigma
      (@omega_equiv_left_inv $A $x0 $x1 $eA)
      (@omega_equiv_left_inv $B $y0 $y1 $eB)
with @omega_equiv_right_inv
      (Product_cat $A $B)
      (Struct_sigma $x0 $y0)
      (Struct_sigma $x1 $y1)
      (@omega_equiv_product $A $B $x0 $x1 $y0 $y1 $eA $eB)
  ↪ Struct_sigma
      (@omega_equiv_right_inv $A $x0 $x1 $eA)
      (@omega_equiv_right_inv $B $y0 $y1 $eB);

// Higher inverse cells of product omega-equivalence are componentwise.
rule @omega_equiv_left_cell
      (Product_cat $A $B)
      (Struct_sigma $x0 $y0)
      (Struct_sigma $x1 $y1)
      (@omega_equiv_product $A $B $x0 $x1 $y0 $y1 $eA $eB)
  ↪ @omega_equiv_product
      (Hom_cat $A $x0 $x0)
      (Hom_cat $B $y0 $y0)
      (@comp_fapp0
        $A
        $x0
        $x1
        $x0
        (@omega_equiv_left_inv $A $x0 $x1 $eA)
        (@omega_equiv_to $A $x0 $x1 $eA))
      (@id $A $x0)
      (@comp_fapp0
        $B
        $y0
        $y1
        $y0
        (@omega_equiv_left_inv $B $y0 $y1 $eB)
        (@omega_equiv_to $B $y0 $y1 $eB))
      (@id $B $y0)
      (@omega_equiv_left_cell $A $x0 $x1 $eA)
      (@omega_equiv_left_cell $B $y0 $y1 $eB)
with @omega_equiv_right_cell
      (Product_cat $A $B)
      (Struct_sigma $x0 $y0)
      (Struct_sigma $x1 $y1)
      (@omega_equiv_product $A $B $x0 $x1 $y0 $y1 $eA $eB)
  ↪ @omega_equiv_product
      (Hom_cat $A $x1 $x1)
      (Hom_cat $B $y1 $y1)
      (@comp_fapp0
        $A
        $x1
        $x0
        $x1
        (@omega_equiv_to $A $x0 $x1 $eA)
        (@omega_equiv_right_inv $A $x0 $x1 $eA))
      (@id $A $x1)
      (@comp_fapp0
        $B
        $y1
        $y0
        $y1
        (@omega_equiv_to $B $y0 $y1 $eB)
        (@omega_equiv_right_inv $B $y0 $y1 $eB))
      (@id $B $y1)
      (@omega_equiv_right_cell $A $x0 $x1 $eA)
      (@omega_equiv_right_cell $B $y0 $y1 $eB);

// Decoder of product omega-equivalence builds the product/Sigma path view.
rule @omega_equiv_path
      (Product_cat $A $B)
      (Struct_sigma $x0 $y0)
      (Struct_sigma $x1 $y1)
      (@omega_equiv_product $A $B $x0 $x1 $y0 $y1 $eA $eB)
  ↪ @Struct_sigma
      (@= (Obj $A) $x0 $x1)
      (λ p : τ (@= (Obj $A) $x0 $x1),
        @PathOver
          (Obj $A)
          (λ _ : τ (Obj $A), Obj $B)
          $x0
          $x1
          p
          $y0
          $y1)
      (@omega_equiv_path $A $x0 $x1 $eA)
      (@const_pathover
        (Obj $A)
        (Obj $B)
        $x0
        $x1
        $y0
        $y1
        (@omega_equiv_path $A $x0 $x1 $eA)
        (@omega_equiv_path $B $y0 $y1 $eB));

// Encoding a product object path yields componentwise omega-equivalence.
rule @idtoequiv_cat
      (Product_cat $A $B)
      (Struct_sigma $x0 $y0)
      (Struct_sigma $x1 $y1)
      (Struct_sigma $pA $pB)
  ↪ @omega_equiv_product
      $A
      $B
      $x0
      $x1
      $y0
      $y1
      (@idtoequiv_cat $A $x0 $x1 $pA)
      (@idtoequiv_cat
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

// 5g. Product-pair telescope declaration

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

  For Cat-valued functors this reduces to the displayed-family category:
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

/*
  Cat-valued transfors reduce to displayed functors.

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
  Ordinary functor adjunctions.

  This is the v3.2 replacement for the draft retired-baseline `adj` interface.
  The old interface was parameterized by already-named functors/unit/counit and
  used unification rules to make projection heads behave like those parameters.
  Here the adjunction itself is first-class:

    J : Adjunction(R,L)
    left_adj_func(J)     : R ⊢ L
    right_adj_func(J)    : L ⊢ R
    unit_adj_transf(J)   : id_R => right(J) ∘ left(J)
    counit_adj_transf(J) : left(J) ∘ right(J) => id_L

  The projection heads are intentionally stable.  We do not add the v2
  evidence-irrelevance unification rules here; if a future theorem needs a
  parameterized "L is left adjoint to R" witness, add a narrow bridge after a
  focused probe.
*/
// First-class ordinary adjunction package between R and L.
injective symbol Adjunction (R L : Cat) : Grpd;

// Left adjoint projection.
//
// Surface/formula:
//   left_adj_func(J) : R ⊢ L.
symbol left_adj_func [R L : Cat]
  (J : τ (Adjunction R L))
  : τ (Functor R L);

// Right adjoint projection.
//
// Surface/formula:
//   right_adj_func(J) : L ⊢ R.
symbol right_adj_func [R L : Cat]
  (J : τ (Adjunction R L))
  : τ (Functor L R);

// Unit of the adjunction.
//
// Surface/formula:
//   unit_adj_transf(J) : id_R => right(J) ∘ left(J).
symbol unit_adj_transf [R L : Cat]
  (J : τ (Adjunction R L))
  : τ (Transf
      (@id_func R)
      (@comp_cat_fapp0
        R
        L
        R
        (@right_adj_func R L J)
        (@left_adj_func R L J)));

// Counit of the adjunction.
//
// Surface/formula:
//   counit_adj_transf(J) : left(J) ∘ right(J) => id_L.
symbol counit_adj_transf [R L : Cat]
  (J : τ (Adjunction R L))
  : τ (Transf
      (@comp_cat_fapp0
        L
        R
        L
        (@left_adj_func R L J)
        (@right_adj_func R L J))
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
        (fapp0 (@left_adj_func $R $L $J) $X')
        $Y
        (@counit_adj_transf $R $L $J)
        $f)
      (fapp1_fapp0 (@left_adj_func $R $L $J)
        (@tapp1_fapp0 _ _ _ _
          $X
          $X'
          (@unit_adj_transf $R $L $J)
          $g))
  ↪ comp_fapp0
      $f
      (fapp1_fapp0 (@left_adj_func $R $L $J) $g);

// Right triangle cut-elimination.
//
// Surface/formula:
//   right(counit[g]) ∘ unit[f] ↪ right(g) ∘ f
//
// for f : X ->^R right(Y') and g : Y' ->^L Y.
rule comp_fapp0
      (fapp1_fapp0 (@right_adj_func $R $L $J)
        (@tapp1_fapp0 _ _ _ _
          $Y'
          $Y
          (@counit_adj_transf $R $L $J)
          $g))
      (@tapp1_fapp0 _ _
        _
        _
        $X
        (fapp0 (@right_adj_func $R $L $J) $Y')
        (@unit_adj_transf $R $L $J)
        $f)
  ↪ comp_fapp0
      (fapp1_fapp0 (@right_adj_func $R $L $J) $g)
      $f;

/*
  Opposite adjunction.

  An adjunction A <-> B dualizes to B^op <-> A^op. The old right adjoint
  becomes the new left adjoint, and the original counit/unit become the dual
  unit/counit through `Op_transf`.
*/
injective symbol Op_adjunction
  [A B : Cat]
  (adj : τ (Adjunction A B))
  : τ (Adjunction (Op_cat B) (Op_cat A));

// Opposite is involutive on adjunction packages: (J^op)^op ↪ J.
rule @Op_adjunction
      (Op_cat $B) (Op_cat $A)
      (@Op_adjunction $A $B $adj)
  ↪ $adj;

// The left adjoint of J^op is the opposite of the right adjoint of J.
rule @left_adj_func
      (Op_cat $B) (Op_cat $A)
      (@Op_adjunction $A $B $adj)
  ↪ @Op_func $B $A (@right_adj_func $A $B $adj);

// The right adjoint of J^op is the opposite of the left adjoint of J.
rule @right_adj_func
      (Op_cat $B) (Op_cat $A)
      (@Op_adjunction $A $B $adj)
  ↪ @Op_func $A $B (@left_adj_func $A $B $adj);

// The unit of J^op is the opposite of the counit of J.
rule @unit_adj_transf
      (Op_cat $B) (Op_cat $A)
      (@Op_adjunction $A $B $adj)
  ↪ @Op_transf
      $B $B
      (@comp_cat_fapp0
        $B $A $B
        (@left_adj_func $A $B $adj)
        (@right_adj_func $A $B $adj))
      (@id_func $B)
      (@counit_adj_transf $A $B $adj);

// The counit of J^op is the opposite of the unit of J.
rule @counit_adj_transf
      (Op_cat $B) (Op_cat $A)
      (@Op_adjunction $A $B $adj)
  ↪ @Op_transf
      $A $A
      (@id_func $A)
      (@comp_cat_fapp0
        $A $B $A
        (@right_adj_func $A $B $adj)
        (@left_adj_func $A $B $adj))
      (@unit_adj_transf $A $B $adj);

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

// 8c. Section categories and Pi action
//
// Fixed-base layer: section category of a displayed family.
//
// Surface/formula:
//   Pi_cat(E) = Π k :^n K, E[k]
//             = k :^n K ; 1[k] ⊢ E[k]
//   section object s has components s[k] : E[k].
symbol Pi_cat [K : Cat] (E : τ (Catd K)) : Cat
≔ @Functord_cat K (@Const_catd K Terminal_cat) E;

// Proof-time comparison only: sections of a constant family are ordinary
// functors, while the displayed section-category head remains stable.
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

// Sections over the projection pullback are displayed functors R => D.
rule @Functord_cat
      (@Sigma_cat $K $R)
      (@Const_catd (@Sigma_cat $K $R) Terminal_cat)
      (@Sigma_proj1_pullback_catd $K $R $D)
  ↪ @Functord_cat $K $R $D;

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

  In the formal v3.2 normal form, a
  Cat-valued transfor is a displayed functor: `Transf_cat K Cat_cat F E`
  reduces to `Functord_cat K F E`. The declarations below keep the conceptual
  `FibCov_target_catd` family visible; assertions document the reduced heads.

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
      (@id_transfd $K $E $D $FF)
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
rule @tdapp1_int_section_arrow $K $E $D $FF $FF (@id_transfd $K $E $D $FF) $x $u
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
rule @tdapp1_int_tgt_arrow $K $E $D $FF $FF (@id_transfd $K $E $D $FF) $x $u $y
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
      $K $E $D $FF $FF (@id_transfd $K $E $D $FF) $x $u $y $v
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
      $K $E $D $FF $FF (@id_transfd $K $E $D $FF) $x $y $p $u $v
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
rule @tdapp1_int_cell $K $E $D $FF $FF (@id_transfd $K $E $D $FF) $x $y $p $u
  ↪ @fdapp1_int_cell $K $E $D $FF $x $y $p $u;

// 16e. Strict/cartesian and terminal-source specializations

// Terminal-source displayed laxity is ordinary functor arrow action.
//
// Surface/formula:
//   fdapp1_int_cell(s,p,*) = s[p].
rule @fdapp1_int_cell
      $K (@Const_catd $K Terminal_cat) (@Const_catd $K $A) $s $x $y $p Terminal_obj
  ↪ @fapp1_fapp0 $K $A $s $x $y $p;

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
      (@Const_catd K (@Functord_cat K (@Const_catd K Terminal_cat) E))
      E);

// LHS indexing guard: this source family is reconstructible from
// `pi_eval_transf`, but replacing it with `_` makes bounded kernel checking
// exceed 30 seconds. Keep it explicit as a decision-tree discriminator.
// lhs-audit: keep 3 -- measured decision-tree performance guard
rule @tapp0_fapp0
      $K Cat_cat
      (@Const_catd $K (@Functord_cat $K (@Const_catd $K Terminal_cat) $E))
      $E $k
      (@pi_eval_transf $K $E)
  ↪ @piapp0_func $K $E $k;

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

  For adj : Adjunction(A,B), M : I -> A, and F : K -> B, the mate comparison
  expresses the representable hom isomorphism

    Hom_B(left(M),F) <-> Hom_A(M,right(F)).

  The strict owner is the ambient ProfComparison certificate below. Selected
  mate maps are obtained by applying `prof_comparison_push/pull` or
  `defiso_to/from` at the use site; they are not independent runtime owners.
*/
injective symbol Adjunction_hom_prof_comparison
  [A B : Cat]
  (adj : τ (Adjunction A B))
  : τ (ProfComparison
      (@Hom_prof_along
        A B B
        (@left_adj_func A B adj)
        (@id_func B))
      (@Hom_prof_along
        A B A
        (@id_func A)
        (@right_adj_func A B adj)));

// Reindexed adjunction mate: Hom_B(LM,F) ≃ Hom_A(M,RF).
symbol Adjunction_hom_prof_comparison_along
  [A B : Cat]
  (adj : τ (Adjunction A B))
  [I K : Cat]
  (M : τ (Functor I A))
  (F : τ (Functor K B))
  : τ (ProfComparison
      (@Hom_prof_along
        I K B
        (@comp_cat_fapp0
          I A B
          (@left_adj_func A B adj)
          M)
        F)
      (@Hom_prof_along
        I K A
        M
        (@comp_cat_fapp0
          K B A
          (@right_adj_func A B adj)
          F)))
≔ @prof_comparison_fmap
    A B I K
    (@Prof_reindex_func A I B K M F)
    _
    _
    (@Adjunction_hom_prof_comparison A B adj);

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
  [W : τ (Prof J' J)]
  [F : τ (Functor J B)]
  (adj : τ (Adjunction A B))
  : τ (ProfComparison
      (@Prof_imply_cov
        A J' J
        (@Hom_prof
          J A
          (@comp_cat_fapp0
            J B A
            (@right_adj_func A B adj)
            F))
        W)
      (@Prof_imply_cov
        A J' J
        (@Hom_prof_along
          A J B
          (@left_adj_func A B adj)
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
        A B adj
        A J
        (@id_func A)
        F));

// Preservation step 2: reindex the supplied weighted-limit comparison along L.
symbol right_adjoint_weighted_limit_comp_step2
  [B J J' A : Cat]
  [W : τ (Prof J' J)]
  [F : τ (Functor J B)]
  [L : τ (Functor J' B)]
  (isl : τ (@IsWeightedLimit_cov_comp B J J' F W L))
  (adj : τ (Adjunction A B))
  : τ (ProfComparison
      (@Prof_imply_cov
        A J' J
        (@Hom_prof_along
          A J B
          (@left_adj_func A B adj)
          F)
        W)
      (@Hom_prof_along
        A J' B
        (@left_adj_func A B adj)
        L))
≔ @prof_comparison_fmap
    B J' A J'
    (@Prof_reindex_func
      B A J' J'
      (@left_adj_func A B adj)
      (@id_func J'))
    _
    _
    isl;

// Preservation step 3: apply the adjunction mate to the candidate limit L.
symbol right_adjoint_weighted_limit_comp_step3
  [B J J' A : Cat]
  [L : τ (Functor J' B)]
  (adj : τ (Adjunction A B))
  : τ (ProfComparison
      (@Hom_prof_along
        A J' B
        (@left_adj_func A B adj)
        L)
      (@Hom_prof
        J' A
        (@comp_cat_fapp0
          J' B A
          (@right_adj_func A B adj)
          L)))
≔ @Adjunction_hom_prof_comparison_along
    A B adj
    A J'
    (@id_func A)
    L;

// Composite certificate that a right adjoint preserves the weighted limit.
symbol right_adjoint_preserves_weighted_limit_cov_comp
  [B J J' A : Cat]
  [W : τ (Prof J' J)]
  [F : τ (Functor J B)]
  [L : τ (Functor J' B)]
  (isl : τ (@IsWeightedLimit_cov_comp B J J' F W L))
  (adj : τ (Adjunction A B))
  : τ (@IsWeightedLimit_cov_comp
      A J J'
      (@comp_cat_fapp0
        J B A
        (@right_adj_func A B adj)
        F)
      W
      (@comp_cat_fapp0
        J' B A
        (@right_adj_func A B adj)
        L))
≔ @prof_comparison_comp
    A J'
    _ _ _
    (@right_adjoint_weighted_limit_comp_step3
      B J J' A L adj)
    (@prof_comparison_comp
      A J'
      _ _ _
      (@right_adjoint_weighted_limit_comp_step2
        B J J' A W F L isl adj)
      (@right_adjoint_weighted_limit_comp_step1
        B J J' A W F adj));

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
  [F : τ (Functor J A)]
  [W : τ (Prof J J')]
  [L : τ (Functor J' A)]
  (isc : τ (@WeightedColimit_con A J J' F W L))
  (adj : τ (Adjunction A B))
  : τ (@WeightedColimit_con
      B J J'
      (@comp_cat_fapp0 J A B (@left_adj_func A B adj) F)
      W
      (@comp_cat_fapp0 J' A B (@left_adj_func A B adj) L))
≔ @right_adjoint_preserves_weighted_limit_cov_comp
    (Op_cat A)
    (Op_cat J)
    (Op_cat J')
    (Op_cat B)
    (@Op_prof J J' W)
    (@Op_func J A F)
    (@Op_func J' A L)
    isc
    (@Op_adjunction A B adj);

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
