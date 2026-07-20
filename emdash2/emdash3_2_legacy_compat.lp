/*
  Frozen opt-in legacy D0/D1 and decoder compatibility module.

  This module imports the active native kernel one-way. It is deliberately
  absent from the active kernel, native extensions, ordinary diagnostics, and
  normal dependency closure. It is not an implementation authority or a
  second equivalence foundation.

  Retention contract: only the seven explicitly legacy reviewer examples may
  import this surface; add no new consumer or feature. The complete two-sided
  `one_cat_iso_type_equiv` theorem is retained because the native stable cast
  does not yet provide the required facade-package/raw-path reification
  coherence. Delete this module when that coherence is implemented through a
  separately reviewed migration, or when backward compatibility is
  deliberately dropped. Until then, fixes may preserve the existing contract
  but must not expand it.
*/

require open emdash.emdash3_2;

// Legacy compatibility decoder from ordinary isomorphism evidence to object
// equality. It remains a runtime owner for reflexive and Product computation;
// no arbitrary-`Cat` univalence capability inhabits it.
symbol iso_evidence_path
  [C : Cat]
  [x y : τ (Obj C)]
  (i : τ (IsoEvidence C x y))
  : τ (x = y);

// Decoder beta on reflexive ordinary isomorphism evidence.
rule @iso_evidence_path $C $x $x (@iso_evidence_refl $C $x)
  ↪ eq_refl $x;

/*
  Candidate D0: omega-equivalence evidence indexed by a fixed arrow.

  `OmegaEquivAlong_D0(f)` is the neutral primary certificate owner. The
  first-class `OmegaEquiv_D0(x,y)` package is its dependent sum over the
  selected forward arrow. Recursive inverse cells return the same package in
  the next hom-category; they do not route through the old opaque
  `OmegaEquiv` interface below.
*/

// Primary certificate that the already-selected arrow `f : x -> y` is an
// omega-equivalence. Property-valuedness is not asserted at this stage.
constant symbol OmegaEquivAlong_D0
  [C : Cat]
  [x y : τ (Obj C)]
  (f : τ (Hom C x y))
  : Grpd;

// First-class omega-equivalence package: `Sigma f, OmegaEquivAlong_D0(f)`.
symbol OmegaEquiv_D0
  (C : Cat)
  (x y : τ (Obj C))
  : Grpd
≔ `Σ_ f : τ (Hom C x y), @OmegaEquivAlong_D0 C x y f;

// Forward-arrow projection of the first-class package.
symbol omega_equiv_to_D0
  [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv_D0 C x y))
  : τ (Hom C x y)
≔ sigma_Fst e;

// Fixed-arrow evidence projection of the first-class package.
symbol omega_equiv_evidence_D0
  [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv_D0 C x y))
  : τ (@OmegaEquivAlong_D0 C x y (omega_equiv_to_D0 e))
≔ sigma_Snd e;

// Selected left-inverse arrow of fixed-arrow evidence.
symbol omega_equiv_along_left_inv_D0
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f))
  : τ (Hom C y x);

// Selected right-inverse arrow of fixed-arrow evidence.
symbol omega_equiv_along_right_inv_D0
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f))
  : τ (Hom C y x);

// Recursive witness that `left_inv(u) o f` is omega-equivalent to `id_x`.
symbol omega_equiv_along_left_cell_D0
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f))
  : τ (OmegaEquiv_D0
      (Hom_cat C x x)
      (@comp_fapp0 C x y x
        (omega_equiv_along_left_inv_D0 u)
        f)
      (@id C x));

// Recursive witness that `f o right_inv(u)` is omega-equivalent to `id_y`.
symbol omega_equiv_along_right_cell_D0
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f))
  : τ (OmegaEquiv_D0
      (Hom_cat C y y)
      (@comp_fapp0 C y x y
        f
        (omega_equiv_along_right_inv_D0 u))
      (@id C y));

// Forward arrow of the left recursive inverse cell.
symbol omega_equiv_along_left_cell_to_D0
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f))
  : τ (Hom
      (Hom_cat C x x)
      (@comp_fapp0 C x y x
        (@omega_equiv_along_left_inv_D0 C x y f u)
        f)
      (@id C x))
≔ @omega_equiv_to_D0
    (Hom_cat C x x)
    (@comp_fapp0 C x y x
      (@omega_equiv_along_left_inv_D0 C x y f u)
      f)
    (@id C x)
    (@omega_equiv_along_left_cell_D0 C x y f u);

// Selected reverse arrow of the right recursive inverse cell.
symbol omega_equiv_along_right_cell_from_D0
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f))
  : τ (Hom
      (Hom_cat C y y)
      (@id C y)
      (@comp_fapp0 C y x y
        f
        (@omega_equiv_along_right_inv_D0 C x y f u)))
≔ @omega_equiv_along_left_inv_D0
    (Hom_cat C y y)
    (@comp_fapp0 C y x y
      f
      (@omega_equiv_along_right_inv_D0 C x y f u))
    (@id C y)
    (@omega_equiv_to_D0
      (Hom_cat C y y)
      (@comp_fapp0 C y x y
        f
        (@omega_equiv_along_right_inv_D0 C x y f u))
      (@id C y)
      (@omega_equiv_along_right_cell_D0 C x y f u))
    (@omega_equiv_evidence_D0
      (Hom_cat C y y)
      (@comp_fapp0 C y x y
        f
        (@omega_equiv_along_right_inv_D0 C x y f u))
      (@id C y)
      (@omega_equiv_along_right_cell_D0 C x y f u));

// Reflexive certificate for the fixed identity arrow.
injective symbol omega_equiv_along_refl_D0
  [C : Cat]
  (x : τ (Obj C))
  : τ (@OmegaEquivAlong_D0 C x x (@id C x));

// Reflexive first-class package, routed through the fixed-arrow certificate.
symbol omega_equiv_refl_D0
  [C : Cat]
  (x : τ (Obj C))
  : τ (OmegaEquiv_D0 C x x)
≔ @Struct_sigma
    (Hom C x x)
    (λ f : τ (Hom C x x), @OmegaEquivAlong_D0 C x x f)
    (@id C x)
    (@omega_equiv_along_refl_D0 C x);

// Reflexive inverse observations compute before the dependent cell rules.
rule omega_equiv_along_left_inv_D0
      (@omega_equiv_along_refl_D0 $C $x)
  ↪ @id $C $x
with omega_equiv_along_right_inv_D0
      (@omega_equiv_along_refl_D0 $C $x)
  ↪ @id $C $x;

// Reflexive inverse cells recursively expose reflexivity in the next hom.
rule omega_equiv_along_left_cell_D0
      (@omega_equiv_along_refl_D0 $C $x)
  ↪ @omega_equiv_refl_D0 (Hom_cat $C $x $x) (@id $C $x)
with omega_equiv_along_right_cell_D0
      (@omega_equiv_along_refl_D0 $C $x)
  ↪ @omega_equiv_refl_D0 (Hom_cat $C $x $x) (@id $C $x);

/*
  D1 public fixed-map omega-equivalence.

  The public classifier is now the dependent sum of a selected arrow and its
  fixed-arrow certificate. Public observations project the package and then
  use the D0 evidence owners; no parallel recursive semantic body remains.
  Canonical generators introduce stable evidence heads and package them with
  the shared `omega_equiv_from_along` constructor.
*/

// Public neutral fixed-arrow evidence name; D0 remains its staging owner.
symbol OmegaEquivAlong
  [C : Cat]
  [x y : τ (Obj C)]
  (f : τ (Hom C x y))
  : Grpd
≔ @OmegaEquivAlong_D0 C x y f;

// Public omega-equivalence package: `Sigma f : x -> y, OmegaEquivAlong(f)`.
symbol OmegaEquiv
  (C : Cat)
  (x y : τ (Obj C))
  : Grpd
≔ `Σ_ f : τ (Hom C x y), @OmegaEquivAlong C x y f;

// Readable direct identity view; public category-universe equality reduces here.
symbol CatPathView
  (A B : Cat)
  : Grpd
≔ OmegaEquiv Cat_cat A B;

// Forward-arrow projection of the public package.
symbol omega_equiv_to
  [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y))
  : τ (Hom C x y)
≔ sigma_Fst e;

// Fixed-arrow evidence projection of the public package.
symbol omega_equiv_evidence
  [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y))
  : τ (@OmegaEquivAlong C x y (omega_equiv_to e))
≔ sigma_Snd e;

// Package already-selected fixed-arrow evidence without duplicating its body.
symbol omega_equiv_from_along
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f))
  : τ (OmegaEquiv C x y)
≔ @Struct_sigma
    (Hom C x y)
    (λ g : τ (Hom C x y), @OmegaEquivAlong C x y g)
    f
    u;

// Selected inverse arrows route through the fixed-arrow evidence projection.
symbol omega_equiv_left_inv
  [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y))
  : τ (Hom C y x)
≔ @omega_equiv_along_left_inv_D0
    C x y (omega_equiv_to e) (omega_equiv_evidence e);

symbol omega_equiv_right_inv
  [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y))
  : τ (Hom C y x)
≔ @omega_equiv_along_right_inv_D0
    C x y (omega_equiv_to e) (omega_equiv_evidence e);

// Recursive inverse cells are the packages returned by the fixed-arrow owner.
symbol omega_equiv_left_cell
  [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y))
  : τ (OmegaEquiv
      (Hom_cat C x x)
      (@comp_fapp0 C x y x
        (omega_equiv_left_inv e)
        (omega_equiv_to e))
      (@id C x))
≔ @omega_equiv_along_left_cell_D0
    C x y (omega_equiv_to e) (omega_equiv_evidence e);

symbol omega_equiv_right_cell
  [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y))
  : τ (OmegaEquiv
      (Hom_cat C y y)
      (@comp_fapp0 C y x y
        (omega_equiv_to e)
        (omega_equiv_right_inv e))
      (@id C y))
≔ @omega_equiv_along_right_cell_D0
    C x y (omega_equiv_to e) (omega_equiv_evidence e);

// Reflexive public package, routed through the fixed-arrow certificate.
symbol omega_equiv_refl
  [C : Cat]
  (x : τ (Obj C))
  : τ (OmegaEquiv C x x)
≔ @omega_equiv_from_along
    C x x (@id C x) (@omega_equiv_along_refl_D0 C x);

/*
  Semantic compatibility fibre of the public forward projection.

  This is a reference construction, not the primary evidence owner. The map
  back to fixed-arrow evidence transports the package evidence along the fibre
  path. The displayed retraction is one-sided and does not assert package eta
  or property-valuedness.
*/
symbol OmegaEquivFibre
  [C : Cat]
  [x y : τ (Obj C)]
  (f : τ (Hom C x y))
  : Grpd
≔ `Σ_ e : τ (OmegaEquiv C x y),
    @= (Hom C x y) (@omega_equiv_to C x y e) f;

symbol omega_equiv_along_to_fibre
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f))
  : τ (@OmegaEquivFibre C x y f)
≔ @Struct_sigma
    (OmegaEquiv C x y)
    (λ e : τ (OmegaEquiv C x y),
      @= (Hom C x y) (@omega_equiv_to C x y e) f)
    (omega_equiv_from_along u)
    (eq_refl f);

symbol omega_equiv_fibre_to_along
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (h : τ (@OmegaEquivFibre C x y f))
  : τ (@OmegaEquivAlong C x y f)
≔ @coe_grpd
    (@OmegaEquivAlong C x y
      (@omega_equiv_to C x y (sigma_Fst h)))
    (@OmegaEquivAlong C x y f)
    (@eq_ap
      (Hom C x y)
      Grpd_grpd
      (λ g : τ (Hom C x y), @OmegaEquivAlong C x y g)
      (@omega_equiv_to C x y (sigma_Fst h))
      f
      (sigma_Snd h))
    (@omega_equiv_evidence C x y (sigma_Fst h));

symbol omega_equiv_along_fibre_retract
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f))
  : τ (
      @omega_equiv_fibre_to_along C x y f
        (@omega_equiv_along_to_fibre C x y f u)
      = u)
≔ eq_refl u;

// Evidence-indexed categorical decoder; canonical evidence owns computation.
symbol omega_equiv_along_path_D1
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f))
  : τ (x = y);

// Decoder beta on reflexive fixed-arrow evidence.
rule @omega_equiv_along_path_D1
      _ _ _ _
      (@omega_equiv_along_refl_D0 _ $x)
  ↪ eq_refl $x;

// Public decoder routes through the evidence projection.
symbol omega_equiv_path
  [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y))
  : τ (x = y)
≔ @omega_equiv_along_path_D1
    C x y (omega_equiv_to e) (omega_equiv_evidence e);

/*
  Object classifiers of fixed-map equivalent categories are ordinarily
  equivalent. The categorical decoder owns the category path; mapping `Obj`
  over that path and applying the groupoid encoder avoids duplicating inverse
  functor components or adding a new proof-time equation.
*/
// Object-classifier path induced by fixed-map categorical equivalence.
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
    (@omega_equiv_along_path_D1 Cat_cat A B F u);

// Canonical ordinary equivalence of the two object classifiers.
symbol omega_equiv_along_obj_type_equiv
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  : τ (TypeEquiv (Obj A) (Obj B))
≔ @idtoequiv_grpd
    (Obj A)
    (Obj B)
    (@omega_equiv_along_obj_path A B F u);

/*
  Constructor-specific fixed-arrow omega-equivalence generators.

  Path-category extraction uses the selected forward arrow. Opposite closure
  swaps the selected inverse directions while preserving the represented
  arrow; its recursive cells reuse the corresponding fixed-arrow packages.
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

// Fixed-arrow evidence is stable under passage to the opposite category.
injective symbol omega_equiv_along_op_D1
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f))
  : τ (@OmegaEquivAlong (Op_cat C) y x f);

// Opposite preserves the canonical reflexive evidence normal form.
rule @omega_equiv_along_op_D1
      $C $x $x _
      (@omega_equiv_along_refl_D0 $C $x)
  ↪ @omega_equiv_along_refl_D0 (Op_cat $C) $x;

// Opposite swaps inverse directions and recursive inverse cells.
rule @omega_equiv_along_left_inv_D0
      _ _ _ _
      (@omega_equiv_along_op_D1 $C $x $y $f $u)
  ↪ @omega_equiv_along_right_inv_D0 $C $x $y $f $u
with @omega_equiv_along_right_inv_D0
      _ _ _ _
      (@omega_equiv_along_op_D1 $C $x $y $f $u)
  ↪ @omega_equiv_along_left_inv_D0 $C $x $y $f $u;

rule @omega_equiv_along_left_cell_D0
      _ _ _ _
      (@omega_equiv_along_op_D1 $C $x $y $f $u)
  ↪ @omega_equiv_along_right_cell_D0 $C $x $y $f $u
with @omega_equiv_along_right_cell_D0
      _ _ _ _
      (@omega_equiv_along_op_D1 $C $x $y $f $u)
  ↪ @omega_equiv_along_left_cell_D0 $C $x $y $f $u;

// Opposite decoder square: reversing evidence reverses its object path.
rule @omega_equiv_along_path_D1
      _ _ _ _
      (@omega_equiv_along_op_D1 $C $x $y $f $u)
  ↪ @path_sym
      (Obj $C)
      $x
      $y
      (@omega_equiv_along_path_D1 $C $x $y $f $u);

// Public opposite closure packages the unchanged arrow with opposite evidence.
symbol omega_equiv_op
  [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y))
  : τ (OmegaEquiv (Op_cat C) y x)
≔ @omega_equiv_from_along
    (Op_cat C)
    y
    x
    (@omega_equiv_to C x y e)
    (@omega_equiv_along_op_D1
      C x y
      (@omega_equiv_to C x y e)
      (@omega_equiv_evidence C x y e));

// Convert object equality to a public fixed-map omega-equivalence package.
symbol idtoequiv_cat
  [C : Cat]
  [x y : τ (Obj C)]
  (p : τ (x = y))
  : τ (OmegaEquiv C x y);

// Reflexive object equality maps to the canonical fixed-arrow package.
rule @idtoequiv_cat $C $x $x (eq_refl $x)
  ↪ @omega_equiv_refl $C $x;

// Closed shaped-reflexivity registration for the omega-equivalence encoder.
rule @idtoequiv_cat $C $r $r (@PathRecordPathRefl _ $r)
  ↪ @omega_equiv_refl $C $r;

// Encoder forward arrows agree propositionally with the generic Core action.
symbol idtoequiv_cat_path_to_hom
  [C : Cat]
  [x y : τ (Obj C)]
  (p : τ (x = y))
  : τ (
      @omega_equiv_to C x y (@idtoequiv_cat C x y p)
      = @path_to_hom C x y p)
≔ @ind_eqr
    (Obj C)
    y
    (λ x : τ (Obj C), λ p : τ (x = y),
      @omega_equiv_to C x y (@idtoequiv_cat C x y p)
      = @path_to_hom C x y p)
    (eq_refl (@id C y))
    x
    p;

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

// Decode omega-equivalence using any supplied contractible-fibre capability.
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

// Canonical decoder-oriented omega-categorical univalence capability.
symbol cat_univalence_by_decoder
  (C : Cat)
  : τ (CatUnivalenceByDecoder C);

/*
  Categorical decoder coherence.

  The specified-inverse capability owns both round trips. It derives a
  contractible-fibre capability and a named TypeEquiv whose selected inverse
  computes to the single evidence-indexed decoder.
*/
symbol cat_univalence_from_decoder
  (C : Cat)
  : τ (CatUnivalence C)
≔ λ x : τ (Obj C), λ y : τ (Obj C),
    @is_equiv_map_by_inverse
      (@= (Obj C) x y)
      (OmegaEquiv C x y)
      (λ p : τ (@= (Obj C) x y), @idtoequiv_cat C x y p)
      (λ e : τ (OmegaEquiv C x y), @omega_equiv_path C x y e)
      (cat_univalence_by_decoder C x y);

// Concrete named equivalence between object paths and omega-equivalences.
symbol cat_univalence_type_equiv
  (C : Cat)
  (x y : τ (Obj C))
  : τ (TypeEquiv (@= (Obj C) x y) (OmegaEquiv C x y))
≔ @Struct_sigma
    (Function_grpd (@= (Obj C) x y) (OmegaEquiv C x y))
    (λ f : τ (Function_grpd (@= (Obj C) x y) (OmegaEquiv C x y)),
      @IsEquivMap (@= (Obj C) x y) (OmegaEquiv C x y) f)
    (λ p : τ (@= (Obj C) x y), @idtoequiv_cat C x y p)
    (cat_univalence_from_decoder C x y);

// The inverse selected by the named equivalence is the operational decoder.
symbol cat_univalence_selected_path
  [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y))
  : τ (x = y)
≔ @type_equiv_from
    (@= (Obj C) x y)
    (OmegaEquiv C x y)
    (@cat_univalence_type_equiv C x y)
    e;

// Decoder after encoder is propositionally the original object path.
symbol omega_equiv_path_idtoequiv_cat
  [C : Cat]
  [x y : τ (Obj C)]
  (p : τ (x = y))
  : τ (
      @omega_equiv_path C x y (@idtoequiv_cat C x y p)
      = p)
≔ (sigma_Fst (cat_univalence_by_decoder C x y)) p;

// Encoder after decoder is propositionally the original public package.
symbol idtoequiv_cat_omega_equiv_path
  [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y))
  : τ (
      @idtoequiv_cat C x y (@omega_equiv_path C x y e)
      = e)
≔ (sigma_Snd (cat_univalence_by_decoder C x y)) e;

// Decode the recursive left inverse cell to an ordinary inverse equation.
symbol omega_equiv_left_law
  [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y))
  : τ (@=
      (Hom C x x)
      (@comp_fapp0 C x y x
        (@omega_equiv_left_inv C x y e)
        (@omega_equiv_to C x y e))
      (@id C x))
≔ @omega_equiv_path
    (Hom_cat C x x)
    (@comp_fapp0 C x y x
      (@omega_equiv_left_inv C x y e)
      (@omega_equiv_to C x y e))
    (@id C x)
    (@omega_equiv_left_cell C x y e);

// Decode the recursive right inverse cell to an ordinary inverse equation.
symbol omega_equiv_right_law
  [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y))
  : τ (@=
      (Hom C y y)
      (@comp_fapp0 C y x y
        (@omega_equiv_to C x y e)
        (@omega_equiv_right_inv C x y e))
      (@id C y))
≔ @omega_equiv_path
    (Hom_cat C y y)
    (@comp_fapp0 C y x y
      (@omega_equiv_to C x y e)
      (@omega_equiv_right_inv C x y e))
    (@id C y)
    (@omega_equiv_right_cell C x y e);

/*
  Compatibility bridge between D0 certificates and equality-law evidence.

  Old D0 evidence decodes its recursive cells to ordinary equality laws. In
  the reverse direction a stable compatibility constructor specifies all D0
  observations: inverse arrows are inherited directly, while recursive cells
  are built by the defined object-path adapter and this same constructor. The
  constructor is migration surface for the otherwise opaque D0 target, not a
  new foundational encoder or an eta principle for D0 evidence.
*/

// Observe an old D0 certificate as finite equality-law evidence.
symbol omega_equiv_along_D0_to_EQ1
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f))
  : τ (@OmegaEquivAlong_EQ1 C x y f)
≔ @omega_equiv_along_intro_EQ1
    C x y f
    (@omega_equiv_along_left_inv_D0 C x y f u)
    (@omega_equiv_along_right_inv_D0 C x y f u)
    (@omega_equiv_left_law C x y
      (@omega_equiv_from_along C x y f u))
    (@omega_equiv_right_law C x y
      (@omega_equiv_from_along C x y f u));

// Observe a first-class D0 package through the stable EQ1 facade.
symbol omega_equiv_D0_to_EQ1
  [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv_D0 C x y))
  : τ (@OmegaEquiv_EQ1 C x y)
≔ @omega_equiv_pack_EQ1
    C x y
    (@omega_equiv_to_D0 C x y e)
    (@omega_equiv_along_D0_to_EQ1
      C x y
      (@omega_equiv_to_D0 C x y e)
      (@omega_equiv_evidence_D0 C x y e));

// Compatibility constructor whose D0 observations are fully specified below.
injective symbol omega_equiv_along_EQ1_to_D0
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_EQ1 C x y f))
  : τ (@OmegaEquivAlong_D0 C x y f);

// Package the selected forward arrow with compatibility evidence.
symbol omega_equiv_EQ1_to_D0
  [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (@OmegaEquiv_EQ1 C x y))
  : τ (OmegaEquiv_D0 C x y)
≔ @Struct_sigma
    (Hom C x y)
    (λ f : τ (Hom C x y), @OmegaEquivAlong_D0 C x y f)
    (@omega_equiv_to_EQ1 C x y e)
    (@omega_equiv_along_EQ1_to_D0
      C x y
      (@omega_equiv_to_EQ1 C x y e)
      (@omega_equiv_evidence_EQ1 C x y e));

// Inverse-arrow observations are inherited verbatim from EQ1.
rule @omega_equiv_along_left_inv_D0 _ _ _ _
      (@omega_equiv_along_EQ1_to_D0 $C $x $y $f $u)
  ↪ @omega_equiv_along_left_inv_EQ1 $C $x $y $f $u
with @omega_equiv_along_right_inv_D0 _ _ _ _
      (@omega_equiv_along_EQ1_to_D0 $C $x $y $f $u)
  ↪ @omega_equiv_along_right_inv_EQ1 $C $x $y $f $u;

// Recursive cells are reified from equality laws by the defined object-path
// adapter and this same compatibility constructor, not by `idtoequiv_cat`.
rule @omega_equiv_along_left_cell_D0 _ _ _ _
      (@omega_equiv_along_EQ1_to_D0 $C $x $y $f $u)
  ↪ @omega_equiv_EQ1_to_D0
      (Hom_cat $C $x $x)
      (@comp_fapp0 $C $x $y $x
        (@omega_equiv_along_left_inv_EQ1 $C $x $y $f $u)
        $f)
      (@id $C $x)
      (@object_path_equiv_EQ1
        (Hom_cat $C $x $x)
        (@comp_fapp0 $C $x $y $x
          (@omega_equiv_along_left_inv_EQ1 $C $x $y $f $u)
          $f)
        (@id $C $x)
        (@omega_equiv_along_left_law_EQ1 $C $x $y $f $u))
with @omega_equiv_along_right_cell_D0 _ _ _ _
      (@omega_equiv_along_EQ1_to_D0 $C $x $y $f $u)
  ↪ @omega_equiv_EQ1_to_D0
      (Hom_cat $C $y $y)
      (@comp_fapp0 $C $y $x $y
        $f
        (@omega_equiv_along_right_inv_EQ1 $C $x $y $f $u))
      (@id $C $y)
      (@object_path_equiv_EQ1
        (Hom_cat $C $y $y)
        (@comp_fapp0 $C $y $x $y
          $f
          (@omega_equiv_along_right_inv_EQ1 $C $x $y $f $u))
        (@id $C $y)
        (@omega_equiv_along_right_law_EQ1 $C $x $y $f $u));

// Construct a legacy D0 package from an object path through the transparent
// EQ1 adapter and the observation-complete migration constructor.
symbol object_path_equiv_D0
  [C : Cat]
  [x y : τ (Obj C)]
  (p : τ (@= (Obj C) x y))
  : τ (OmegaEquiv_D0 C x y)
≔ @omega_equiv_EQ1_to_D0 C x y
    (@object_path_equiv_EQ1 C x y p);

/*
  Strict ordinary isomorphism evidence gives recursive omega-equivalence.

  The ordinary inverse equations are genuine paths between parallel arrows.
  Encoding those paths in the two endomorphism hom-categories supplies the
  recursive inverse cells required by the D0 observation interface. The
  stable evidence head is an introduction owner only for this backed source;
  it is not an eta principle for arbitrary opaque D0 evidence.
*/
injective symbol iso_evidence_omega_along_D0
  [C : Cat]
  [x y : τ (Obj C)]
  (i : τ (IsoEvidence C x y))
  : τ (@OmegaEquivAlong_D0 C x y (@iso_evidence_to C x y i));

// Public package of the forward arrow and its recursively backed evidence.
symbol iso_evidence_omega_equiv
  [C : Cat]
  [x y : τ (Obj C)]
  (i : τ (IsoEvidence C x y))
  : τ (OmegaEquiv C x y)
≔ @omega_equiv_from_along
    C
    x
    y
    (@iso_evidence_to C x y i)
    (@iso_evidence_omega_along_D0 C x y i);

// Proof-time only: the backed lift of reflexive ordinary evidence compares
// with the canonical recursive certificate without choosing a runtime form.
unif_rule
  @iso_evidence_omega_along_D0
    $C $x $x (@iso_evidence_refl $C $x)
  ≡ @omega_equiv_along_refl_D0 $C $x
  ↪ [ tt ≡ tt ];

// Both selected inverse arrows are the ordinary inverse arrow.
rule @omega_equiv_along_left_inv_D0
      _ _ _ _
      (@iso_evidence_omega_along_D0 $C $x $y $i)
  ↪ @iso_evidence_from $C $x $y $i
with @omega_equiv_along_right_inv_D0
      _ _ _ _
      (@iso_evidence_omega_along_D0 $C $x $y $i)
  ↪ @iso_evidence_from $C $x $y $i;

// Ordinary inverse equations use the constructed object-path compatibility
// adapter rather than the legacy categorical encoder.
rule @omega_equiv_along_left_cell_D0
      _ _ _ _
      (@iso_evidence_omega_along_D0 $C $x $y $i)
  ↪ @object_path_equiv_D0
      (Hom_cat $C $x $x)
      (@comp_fapp0 $C $x $y $x
        (@iso_evidence_from $C $x $y $i)
        (@iso_evidence_to $C $x $y $i))
      (@id $C $x)
      (@iso_evidence_left $C $x $y $i)
with @omega_equiv_along_right_cell_D0
      _ _ _ _
      (@iso_evidence_omega_along_D0 $C $x $y $i)
  ↪ @object_path_equiv_D0
      (Hom_cat $C $y $y)
      (@comp_fapp0 $C $y $x $y
        (@iso_evidence_to $C $x $y $i)
        (@iso_evidence_from $C $x $y $i))
      (@id $C $y)
      (@iso_evidence_right $C $x $y $i);

// The backed lift agrees propositionally with the omega encoder on paths.
// The reflexive base uses the single proof-time certificate comparison above;
// the arbitrary theorem is retained generic J, not unification transitivity.
symbol iso_evidence_omega_equiv_idtoiso
  [C : Cat]
  [x y : τ (Obj C)]
  (p : τ (@= (Obj C) x y))
  : τ (@=
      (OmegaEquiv C x y)
      (@iso_evidence_omega_equiv C x y
        (@idtoiso_cat C x y p))
      (@idtoequiv_cat C x y p))
≔ @ind_eqr
    (Obj C)
    y
    (λ x : τ (Obj C), λ p : τ (@= (Obj C) x y),
      @=
        (OmegaEquiv C x y)
        (@iso_evidence_omega_equiv C x y
          (@idtoiso_cat C x y p))
        (@idtoequiv_cat C x y p))
    (eq_refl (@omega_equiv_refl C y))
    x
    p;

/*
  Every recursive omega-equivalence compares its selected inverse arrows.

  Whisker `id_y => f o right_inv` on the left by `left_inv`, use the
  propositional associator, then whisker `left_inv o f => id_x` on the right
  by `right_inv`. The existing post/precomposition functors own the two
  actions. Explicit theorem-level path composition avoids relying on
  unification transitivity between their distinct stable point heads.
*/
symbol omega_equiv_along_left_whisker_right_cell_from_D0
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f))
  : τ (Hom
      (Hom_cat C y x)
      (@omega_equiv_along_left_inv_D0 C x y f u)
      (@hom_postcomp_fapp0
        C C (@id Cat_cat C)
        y y x
        (@omega_equiv_along_left_inv_D0 C x y f u)
        (@comp_fapp0 C y x y
          f
          (@omega_equiv_along_right_inv_D0 C x y f u))))
≔ @fapp1_fapp0
    (Hom_cat C y y)
    (Hom_cat C y x)
    (@hom_postcomp_func
      C C (@id Cat_cat C)
      y y x
      (@omega_equiv_along_left_inv_D0 C x y f u))
    (@id C y)
    (@comp_fapp0 C y x y
      f
      (@omega_equiv_along_right_inv_D0 C x y f u))
    (@omega_equiv_along_right_cell_from_D0 C x y f u);

symbol omega_equiv_along_right_whisker_left_cell_to_D0
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f))
  : τ (Hom
      (Hom_cat C y x)
      (@hom_precomp_along_fapp0
        C C (@id Cat_cat C)
        x y x
        (@omega_equiv_along_right_inv_D0 C x y f u)
        (@comp_fapp0 C x y x
          (@omega_equiv_along_left_inv_D0 C x y f u)
          f))
      (@omega_equiv_along_right_inv_D0 C x y f u))
≔ @fapp1_fapp0
    (Hom_cat C x x)
    (Hom_cat C y x)
    (@hom_precomp_along_func
      C C (@id Cat_cat C)
      x y x
      (@omega_equiv_along_right_inv_D0 C x y f u))
    (@comp_fapp0 C x y x
      (@omega_equiv_along_left_inv_D0 C x y f u)
      f)
    (@id C x)
    (@omega_equiv_along_left_cell_to_D0 C x y f u);

// The two stable whiskering heads present the two bracketings of l o f o r.
symbol omega_equiv_along_inverse_assoc_path_D0
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f))
  : τ (@=
      (Hom C y x)
      (@hom_postcomp_fapp0
        C C (@id Cat_cat C)
        y y x
        (@omega_equiv_along_left_inv_D0 C x y f u)
        (@comp_fapp0 C y x y
          f
          (@omega_equiv_along_right_inv_D0 C x y f u)))
      (@hom_precomp_along_fapp0
        C C (@id Cat_cat C)
        x y x
        (@omega_equiv_along_right_inv_D0 C x y f u)
        (@comp_fapp0 C x y x
          (@omega_equiv_along_left_inv_D0 C x y f u)
          f)))
≔ @eq_trans
    (Hom C y x)
    (@hom_postcomp_fapp0
      C C (@id Cat_cat C)
      y y x
      (@omega_equiv_along_left_inv_D0 C x y f u)
      (@comp_fapp0 C y x y
        f
        (@omega_equiv_along_right_inv_D0 C x y f u)))
    (@comp_fapp0 C y y x
      (@omega_equiv_along_left_inv_D0 C x y f u)
      (@comp_fapp0 C y x y
        f
        (@omega_equiv_along_right_inv_D0 C x y f u)))
    (@hom_precomp_along_fapp0
      C C (@id Cat_cat C)
      x y x
      (@omega_equiv_along_right_inv_D0 C x y f u)
      (@comp_fapp0 C x y x
        (@omega_equiv_along_left_inv_D0 C x y f u)
        f))
    (eq_refl
      (@comp_fapp0 C y y x
        (@omega_equiv_along_left_inv_D0 C x y f u)
        (@comp_fapp0 C y x y
          f
          (@omega_equiv_along_right_inv_D0 C x y f u))))
    (@eq_trans
      (Hom C y x)
      (@comp_fapp0 C y y x
        (@omega_equiv_along_left_inv_D0 C x y f u)
        (@comp_fapp0 C y x y
          f
          (@omega_equiv_along_right_inv_D0 C x y f u)))
      (@comp_fapp0 C y x x
        (@comp_fapp0 C x y x
          (@omega_equiv_along_left_inv_D0 C x y f u)
          f)
        (@omega_equiv_along_right_inv_D0 C x y f u))
      (@hom_precomp_along_fapp0
        C C (@id Cat_cat C)
        x y x
        (@omega_equiv_along_right_inv_D0 C x y f u)
        (@comp_fapp0 C x y x
          (@omega_equiv_along_left_inv_D0 C x y f u)
          f))
      (@comp_assoc
        C y x y x
        (@omega_equiv_along_left_inv_D0 C x y f u)
        f
        (@omega_equiv_along_right_inv_D0 C x y f u))
      (eq_refl
        (@comp_fapp0 C y x x
          (@comp_fapp0 C x y x
            (@omega_equiv_along_left_inv_D0 C x y f u)
            f)
          (@omega_equiv_along_right_inv_D0 C x y f u))));

symbol omega_equiv_along_inverse_assoc_D0
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f))
  : τ (Hom
      (Hom_cat C y x)
      (@hom_postcomp_fapp0
        C C (@id Cat_cat C)
        y y x
        (@omega_equiv_along_left_inv_D0 C x y f u)
        (@comp_fapp0 C y x y
          f
          (@omega_equiv_along_right_inv_D0 C x y f u)))
      (@hom_precomp_along_fapp0
        C C (@id Cat_cat C)
        x y x
        (@omega_equiv_along_right_inv_D0 C x y f u)
        (@comp_fapp0 C x y x
          (@omega_equiv_along_left_inv_D0 C x y f u)
          f)))
≔ @path_to_hom
    (Hom_cat C y x)
    (@hom_postcomp_fapp0
      C C (@id Cat_cat C)
      y y x
      (@omega_equiv_along_left_inv_D0 C x y f u)
      (@comp_fapp0 C y x y
        f
        (@omega_equiv_along_right_inv_D0 C x y f u)))
    (@hom_precomp_along_fapp0
      C C (@id Cat_cat C)
      x y x
      (@omega_equiv_along_right_inv_D0 C x y f u)
      (@comp_fapp0 C x y x
        (@omega_equiv_along_left_inv_D0 C x y f u)
        f))
    (@omega_equiv_along_inverse_assoc_path_D0 C x y f u);

symbol omega_equiv_along_left_to_right_D0
  [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f))
  : τ (Hom
      (Hom_cat C y x)
      (@omega_equiv_along_left_inv_D0 C x y f u)
      (@omega_equiv_along_right_inv_D0 C x y f u))
≔ @comp_fapp0
    (Hom_cat C y x)
    (@omega_equiv_along_left_inv_D0 C x y f u)
    (@hom_precomp_along_fapp0
      C C (@id Cat_cat C)
      x y x
      (@omega_equiv_along_right_inv_D0 C x y f u)
      (@comp_fapp0 C x y x
        (@omega_equiv_along_left_inv_D0 C x y f u)
        f))
    (@omega_equiv_along_right_inv_D0 C x y f u)
    (@omega_equiv_along_right_whisker_left_cell_to_D0 C x y f u)
    (@comp_fapp0
      (Hom_cat C y x)
      (@omega_equiv_along_left_inv_D0 C x y f u)
      (@hom_postcomp_fapp0
        C C (@id Cat_cat C)
        y y x
        (@omega_equiv_along_left_inv_D0 C x y f u)
        (@comp_fapp0 C y x y
          f
          (@omega_equiv_along_right_inv_D0 C x y f u)))
      (@hom_precomp_along_fapp0
        C C (@id Cat_cat C)
        x y x
        (@omega_equiv_along_right_inv_D0 C x y f u)
        (@comp_fapp0 C x y x
          (@omega_equiv_along_left_inv_D0 C x y f u)
          f))
      (@omega_equiv_along_inverse_assoc_D0 C x y f u)
      (@omega_equiv_along_left_whisker_right_cell_from_D0 C x y f u));


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

// 5f. Product closure for omega-equivalence
/*
  Omega-equivalence is closed under explicit product-category pairs.

  This first slice targets visible `Struct_sigma` endpoints. Opaque product
  eta can remain a later refinement; product projections already expose many
  opaque component consumers. Componentwise evidence provenance is preserved
  at reflexivity rather than collapsed to the generic reflexive evidence head.
*/
// Fixed-map Product evidence over the componentwise selected arrow.
injective symbol omega_equiv_along_product_D1
  [A B : Cat]
  [x0 x1 : τ (Obj A)]
  [y0 y1 : τ (Obj B)]
  [fA : τ (Hom A x0 x1)]
  [fB : τ (Hom B y0 y1)]
  (uA : τ (@OmegaEquivAlong A x0 x1 fA))
  (uB : τ (@OmegaEquivAlong B y0 y1 fB))
  : τ (@OmegaEquivAlong
      (Product_cat A B)
      (Struct_sigma x0 y0)
      (Struct_sigma x1 y1)
      (Struct_sigma fA fB));

// Public Product closure packages component evidence through the shared owner.
symbol omega_equiv_product
  [A B : Cat]
  [x0 x1 : τ (Obj A)]
  [y0 y1 : τ (Obj B)]
  (eA : τ (OmegaEquiv A x0 x1))
  (eB : τ (OmegaEquiv B y0 y1))
  : τ (OmegaEquiv
      (Product_cat A B)
      (Struct_sigma x0 y0)
      (Struct_sigma x1 y1))
≔ @omega_equiv_from_along
    (Product_cat A B)
    (Struct_sigma x0 y0)
    (Struct_sigma x1 y1)
    (Struct_sigma (omega_equiv_to eA) (omega_equiv_to eB))
    (@omega_equiv_along_product_D1
      A B x0 x1 y0 y1
      (omega_equiv_to eA)
      (omega_equiv_to eB)
      (omega_equiv_evidence eA)
      (omega_equiv_evidence eB));

// Selected inverse arrows of Product evidence are componentwise.
rule omega_equiv_along_left_inv_D0
      (omega_equiv_along_product_D1 $uA $uB)
  ↪ Struct_sigma
      (omega_equiv_along_left_inv_D0 $uA)
      (omega_equiv_along_left_inv_D0 $uB)
with omega_equiv_along_right_inv_D0
      (omega_equiv_along_product_D1 $uA $uB)
  ↪ Struct_sigma
      (omega_equiv_along_right_inv_D0 $uA)
      (omega_equiv_along_right_inv_D0 $uB);

// Recursive inverse cells of Product evidence are componentwise packages.
rule omega_equiv_along_left_cell_D0
      (omega_equiv_along_product_D1 $uA $uB)
  ↪ omega_equiv_product
      (omega_equiv_along_left_cell_D0 $uA)
      (omega_equiv_along_left_cell_D0 $uB)
with omega_equiv_along_right_cell_D0
      (omega_equiv_along_product_D1 $uA $uB)
  ↪ omega_equiv_product
      (omega_equiv_along_right_cell_D0 $uA)
      (omega_equiv_along_right_cell_D0 $uB);

// Decoder of Product evidence builds the Product/Sigma object-path view.
rule @omega_equiv_along_path_D1
      _ _ _ _
      (@omega_equiv_along_product_D1
        $A $B $x0 $x1 $y0 $y1 $fA $fB $uA $uB)
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
      (@omega_equiv_along_path_D1 $A $x0 $x1 $fA $uA)
      (@const_pathover
        (Obj $A)
        (Obj $B)
        $x0
        $x1
        $y0
        $y1
        (@omega_equiv_along_path_D1 $A $x0 $x1 $fA $uA)
        (@omega_equiv_along_path_D1 $B $y0 $y1 $fB $uB));

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

/*
  Candidate D0b: fixed-arrow equivalence of a functor's hom action.

  Variable evidence `u : OmegaEquivAlong_D0(F)` induces evidence for
  `F_1[x,y]`. Raw hom action of either selected inverse functor has endpoints
  at the inverse images of `F[x]` and `F[y]`; the functors below repair those
  endpoints with components of the recursive inverse cells before installing
  the canonical evidence generator.
*/

// Selected inverse functors of the fixed-arrow category equivalence.
symbol omega_equiv_along_left_functor_D0
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  : τ (Functor B A)
≔ @omega_equiv_along_left_inv_D0 Cat_cat A B F u;

symbol omega_equiv_along_right_functor_D0
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  : τ (Functor B A)
≔ @omega_equiv_along_right_inv_D0 Cat_cat A B F u;

// Forward and selected reverse transformations of `left_inv(u) o F ~ id_A`.
symbol omega_equiv_along_left_to_transf_D0
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  : τ (@Transf
      A A
      (@comp_cat_fapp0 A B A
        (omega_equiv_along_left_functor_D0 u)
        F)
      (@id_func A))
≔ @omega_equiv_to_D0
    (Functor_cat A A)
    (@comp_cat_fapp0 A B A
      (omega_equiv_along_left_functor_D0 u)
      F)
    (@id_func A)
    (@omega_equiv_along_left_cell_D0 Cat_cat A B F u);

symbol omega_equiv_along_left_from_transf_D0
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  : τ (@Transf
      A A
      (@id_func A)
      (@comp_cat_fapp0 A B A
        (omega_equiv_along_left_functor_D0 u)
        F))
≔ @omega_equiv_along_right_inv_D0
    (Functor_cat A A)
    (@comp_cat_fapp0 A B A
      (omega_equiv_along_left_functor_D0 u)
      F)
    (@id_func A)
    (omega_equiv_along_left_to_transf_D0 u)
    (@omega_equiv_evidence_D0
      (Functor_cat A A)
      (@comp_cat_fapp0 A B A
        (omega_equiv_along_left_functor_D0 u)
        F)
      (@id_func A)
      (@omega_equiv_along_left_cell_D0 Cat_cat A B F u));

// Forward and selected reverse transformations of `F o right_inv(u) ~ id_B`.
symbol omega_equiv_along_right_to_transf_D0
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  : τ (@Transf
      B B
      (@comp_cat_fapp0 B A B
        F
        (omega_equiv_along_right_functor_D0 u))
      (@id_func B))
≔ @omega_equiv_to_D0
    (Functor_cat B B)
    (@comp_cat_fapp0 B A B
      F
      (omega_equiv_along_right_functor_D0 u))
    (@id_func B)
    (@omega_equiv_along_right_cell_D0 Cat_cat A B F u);

symbol omega_equiv_along_right_from_transf_D0
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  : τ (@Transf
      B B
      (@id_func B)
      (@comp_cat_fapp0 B A B
        F
        (omega_equiv_along_right_functor_D0 u)))
≔ @omega_equiv_along_right_inv_D0
    (Functor_cat B B)
    (@comp_cat_fapp0 B A B
      F
      (omega_equiv_along_right_functor_D0 u))
    (@id_func B)
    (omega_equiv_along_right_to_transf_D0 u)
    (@omega_equiv_evidence_D0
      (Functor_cat B B)
      (@comp_cat_fapp0 B A B
        F
        (omega_equiv_along_right_functor_D0 u))
      (@id_func B)
      (@omega_equiv_along_right_cell_D0 Cat_cat A B F u));

// Endpoint components supplied by the two recursive inverse cells.
symbol omega_equiv_along_left_to_component_D0
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x : τ (Obj A))
  : τ (Hom A
      (@fapp0 B A
        (omega_equiv_along_left_functor_D0 u)
        (@fapp0 A B F x))
      x)
≔ @tapp0_fapp0
    A A
    (@comp_cat_fapp0 A B A
      (omega_equiv_along_left_functor_D0 u)
      F)
    (@id_func A)
    x
    (omega_equiv_along_left_to_transf_D0 u);

symbol omega_equiv_along_left_from_component_D0
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x : τ (Obj A))
  : τ (Hom A
      x
      (@fapp0 B A
        (omega_equiv_along_left_functor_D0 u)
        (@fapp0 A B F x)))
≔ @tapp0_fapp0
    A A
    (@id_func A)
    (@comp_cat_fapp0 A B A
      (omega_equiv_along_left_functor_D0 u)
      F)
    x
    (omega_equiv_along_left_from_transf_D0 u);

symbol omega_equiv_along_right_to_component_D0
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (b : τ (Obj B))
  : τ (Hom B
      (@fapp0 A B F
        (@fapp0 B A (omega_equiv_along_right_functor_D0 u) b))
      b)
≔ @tapp0_fapp0
    B B
    (@comp_cat_fapp0 B A B
      F
      (omega_equiv_along_right_functor_D0 u))
    (@id_func B)
    b
    (omega_equiv_along_right_to_transf_D0 u);

symbol omega_equiv_along_right_from_component_D0
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (b : τ (Obj B))
  : τ (Hom B
      b
      (@fapp0 A B F
        (@fapp0 B A (omega_equiv_along_right_functor_D0 u) b)))
≔ @tapp0_fapp0
    B B
    (@id_func B)
    (@comp_cat_fapp0 B A B
      F
      (omega_equiv_along_right_functor_D0 u))
    b
    (omega_equiv_along_right_from_transf_D0 u);

// Comparison components between the selected right and left inverse functors.
// R[b] -> L[b] uses R[b] -> L[F[R[b]]] -> L[b].
symbol omega_equiv_along_right_to_left_component_D0
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (b : τ (Obj B))
  : τ (Hom A
      (@fapp0 B A (omega_equiv_along_right_functor_D0 u) b)
      (@fapp0 B A (omega_equiv_along_left_functor_D0 u) b))
≔ @comp_fapp0
    A
    (@fapp0 B A (omega_equiv_along_right_functor_D0 u) b)
    (@fapp0 B A
      (omega_equiv_along_left_functor_D0 u)
      (@fapp0 A B F
        (@fapp0 B A (omega_equiv_along_right_functor_D0 u) b)))
    (@fapp0 B A (omega_equiv_along_left_functor_D0 u) b)
    (@fapp1_fapp0
      B A
      (omega_equiv_along_left_functor_D0 u)
      (@fapp0 A B F
        (@fapp0 B A (omega_equiv_along_right_functor_D0 u) b))
      b
      (omega_equiv_along_right_to_component_D0 u b))
    (omega_equiv_along_left_from_component_D0
      u
      (@fapp0 B A (omega_equiv_along_right_functor_D0 u) b));

// L[b] -> R[b] uses L[b] -> L[F[R[b]]] -> R[b].
symbol omega_equiv_along_left_to_right_component_D0
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (b : τ (Obj B))
  : τ (Hom A
      (@fapp0 B A (omega_equiv_along_left_functor_D0 u) b)
      (@fapp0 B A (omega_equiv_along_right_functor_D0 u) b))
≔ @comp_fapp0
    A
    (@fapp0 B A (omega_equiv_along_left_functor_D0 u) b)
    (@fapp0 B A
      (omega_equiv_along_left_functor_D0 u)
      (@fapp0 A B F
        (@fapp0 B A (omega_equiv_along_right_functor_D0 u) b)))
    (@fapp0 B A (omega_equiv_along_right_functor_D0 u) b)
    (omega_equiv_along_left_to_component_D0
      u
      (@fapp0 B A (omega_equiv_along_right_functor_D0 u) b))
    (@fapp1_fapp0
      B A
      (omega_equiv_along_left_functor_D0 u)
      b
      (@fapp0 A B F
        (@fapp0 B A (omega_equiv_along_right_functor_D0 u) b))
      (omega_equiv_along_right_from_component_D0 u b));

// The selected left inverse also has a right-target component. It is derived
// by comparing the selected left and right inverses, then using the existing
// right recursive cell; no cancellation rewrite is installed.
symbol omega_equiv_along_left_inverse_right_component_D0
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (b : τ (Obj B))
  : τ (Hom B
      (@fapp0 A B F
        (@fapp0 B A (omega_equiv_along_left_functor_D0 u) b))
      b)
≔ @comp_fapp0
    B
    (@fapp0 A B F
      (@fapp0 B A (omega_equiv_along_left_functor_D0 u) b))
    (@fapp0 A B F
      (@fapp0 B A (omega_equiv_along_right_functor_D0 u) b))
    b
    (omega_equiv_along_right_to_component_D0 u b)
    (@fapp1_fapp0
      A B F
      (@fapp0 B A (omega_equiv_along_left_functor_D0 u) b)
      (@fapp0 B A (omega_equiv_along_right_functor_D0 u) b)
      (omega_equiv_along_left_to_right_component_D0 u b));

// Endpoint repairs for the selected right inverse hom functor.
symbol omega_equiv_along_fapp1_right_source_D0
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x : τ (Obj A))
  : τ (Hom A
      x
      (@fapp0 B A
        (omega_equiv_along_right_functor_D0 u)
        (@fapp0 A B F x)))
≔ @comp_fapp0
    A
    x
    (@fapp0 B A
      (omega_equiv_along_left_functor_D0 u)
      (@fapp0 A B F x))
    (@fapp0 B A
      (omega_equiv_along_right_functor_D0 u)
      (@fapp0 A B F x))
    (omega_equiv_along_left_to_right_component_D0
      u
      (@fapp0 A B F x))
    (omega_equiv_along_left_from_component_D0 u x);

symbol omega_equiv_along_fapp1_right_target_D0
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (y : τ (Obj A))
  : τ (Hom A
      (@fapp0 B A
        (omega_equiv_along_right_functor_D0 u)
        (@fapp0 A B F y))
      y)
≔ @comp_fapp0
    A
    (@fapp0 B A
      (omega_equiv_along_right_functor_D0 u)
      (@fapp0 A B F y))
    (@fapp0 B A
      (omega_equiv_along_left_functor_D0 u)
      (@fapp0 A B F y))
    y
    (omega_equiv_along_left_to_component_D0 u y)
    (omega_equiv_along_right_to_left_component_D0
      u
      (@fapp0 A B F y));

// Endpoint-correct selected inverse functors for `F_1[x,y]`.
symbol omega_equiv_along_fapp1_left_inv_D0
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A))
  : τ (Functor
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (Hom_cat A x y))
≔ @comp_cat_fapp0
    (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
    (Hom_cat A
      (@fapp0 B A
        (omega_equiv_along_left_functor_D0 u)
        (@fapp0 A B F x))
      (@fapp0 B A
        (omega_equiv_along_left_functor_D0 u)
        (@fapp0 A B F y)))
    (Hom_cat A x y)
    (@Hom_func
      A
      (@fapp0 B A
        (omega_equiv_along_left_functor_D0 u)
        (@fapp0 A B F x))
      x
      (@fapp0 B A
        (omega_equiv_along_left_functor_D0 u)
        (@fapp0 A B F y))
      y
      (omega_equiv_along_left_from_component_D0 u x)
      (omega_equiv_along_left_to_component_D0 u y))
    (@fapp1_func
      B A
      (omega_equiv_along_left_functor_D0 u)
      (@fapp0 A B F x)
      (@fapp0 A B F y));

symbol omega_equiv_along_fapp1_right_inv_D0
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A))
  : τ (Functor
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (Hom_cat A x y))
≔ @comp_cat_fapp0
    (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
    (Hom_cat A
      (@fapp0 B A
        (omega_equiv_along_right_functor_D0 u)
        (@fapp0 A B F x))
      (@fapp0 B A
        (omega_equiv_along_right_functor_D0 u)
        (@fapp0 A B F y)))
    (Hom_cat A x y)
    (@Hom_func
      A
      (@fapp0 B A
        (omega_equiv_along_right_functor_D0 u)
        (@fapp0 A B F x))
      x
      (@fapp0 B A
        (omega_equiv_along_right_functor_D0 u)
        (@fapp0 A B F y))
      y
      (omega_equiv_along_fapp1_right_source_D0 u x)
      (omega_equiv_along_fapp1_right_target_D0 u y))
    (@fapp1_func
      B A
      (omega_equiv_along_right_functor_D0 u)
      (@fapp0 A B F x)
      (@fapp0 A B F y));

// Stable forward cells and their recursive evidence at the next hom rung.
symbol omega_equiv_along_fapp1_left_cell_to_D0
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A))
  : τ (@Transf
      (Hom_cat A x y)
      (Hom_cat A x y)
      (@comp_cat_fapp0
        (Hom_cat A x y)
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (Hom_cat A x y)
        (omega_equiv_along_fapp1_left_inv_D0 u x y)
        (@fapp1_func A B F x y))
      (@id_func (Hom_cat A x y)));

symbol omega_equiv_along_fapp1_left_cell_evidence_D0
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A))
  : τ (@OmegaEquivAlong_D0
      (Functor_cat (Hom_cat A x y) (Hom_cat A x y))
      (@comp_cat_fapp0
        (Hom_cat A x y)
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (Hom_cat A x y)
        (omega_equiv_along_fapp1_left_inv_D0 u x y)
        (@fapp1_func A B F x y))
      (@id_func (Hom_cat A x y))
      (omega_equiv_along_fapp1_left_cell_to_D0 u x y));

symbol omega_equiv_along_fapp1_left_cell_D0
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A))
  : τ (OmegaEquiv_D0
      (Functor_cat (Hom_cat A x y) (Hom_cat A x y))
      (@comp_cat_fapp0
        (Hom_cat A x y)
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (Hom_cat A x y)
        (omega_equiv_along_fapp1_left_inv_D0 u x y)
        (@fapp1_func A B F x y))
      (@id_func (Hom_cat A x y)))
≔ Struct_sigma
    (omega_equiv_along_fapp1_left_cell_to_D0 u x y)
    (omega_equiv_along_fapp1_left_cell_evidence_D0 u x y);

symbol omega_equiv_along_fapp1_right_cell_to_D0
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A))
  : τ (@Transf
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (@comp_cat_fapp0
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (Hom_cat A x y)
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (@fapp1_func A B F x y)
        (omega_equiv_along_fapp1_right_inv_D0 u x y))
      (@id_func
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))));

symbol omega_equiv_along_fapp1_right_cell_evidence_D0
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A))
  : τ (@OmegaEquivAlong_D0
      (Functor_cat
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y)))
      (@comp_cat_fapp0
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (Hom_cat A x y)
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (@fapp1_func A B F x y)
        (omega_equiv_along_fapp1_right_inv_D0 u x y))
      (@id_func
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y)))
      (omega_equiv_along_fapp1_right_cell_to_D0 u x y));

symbol omega_equiv_along_fapp1_right_cell_D0
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A))
  : τ (OmegaEquiv_D0
      (Functor_cat
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y)))
      (@comp_cat_fapp0
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (Hom_cat A x y)
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (@fapp1_func A B F x y)
        (omega_equiv_along_fapp1_right_inv_D0 u x y))
      (@id_func
        (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))))
≔ Struct_sigma
    (omega_equiv_along_fapp1_right_cell_to_D0 u x y)
    (omega_equiv_along_fapp1_right_cell_evidence_D0 u x y);

// Canonical variable-evidence hom-action generator.
injective symbol omega_equiv_along_fapp1_D0
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A))
  : τ (@OmegaEquivAlong_D0
      Cat_cat
      (Hom_cat A x y)
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (@fapp1_func A B F x y));

// Its selected inverse observations expose the endpoint-correct functors.
rule omega_equiv_along_left_inv_D0
      (@omega_equiv_along_fapp1_D0 $A $B $F $u $x $y)
  ↪ @omega_equiv_along_fapp1_left_inv_D0 $A $B $F $u $x $y
with omega_equiv_along_right_inv_D0
      (@omega_equiv_along_fapp1_D0 $A $B $F $u $x $y)
  ↪ @omega_equiv_along_fapp1_right_inv_D0 $A $B $F $u $x $y;

// Recursive observations expose packaged next-hom cells in both directions.
rule omega_equiv_along_left_cell_D0
      (@omega_equiv_along_fapp1_D0 $A $B $F $u $x $y)
  ↪ @omega_equiv_along_fapp1_left_cell_D0 $A $B $F $u $x $y
with omega_equiv_along_right_cell_D0
      (@omega_equiv_along_fapp1_D0 $A $B $F $u $x $y)
  ↪ @omega_equiv_along_fapp1_right_cell_D0 $A $B $F $u $x $y;

/*
  First integrated next-hom univalence/action witness.

  A path between categories selects a public omega-equivalence and hence a
  functor. D0b acts on its fixed-arrow evidence to produce an iterable public
  omega-equivalence between the corresponding hom-categories. No per-instance
  unification equation identifies or repairs the selected functor.
*/
symbol idtoequiv_cat_functor_D1
  [A B : Cat]
  (p : τ (@= (Obj Cat_cat) A B))
  : τ (Functor A B)
≔ @omega_equiv_to
    Cat_cat A B (@object_path_equiv_D0 Cat_cat A B p);

symbol idtoequiv_cat_fapp1_along_D1
  [A B : Cat]
  (p : τ (@= (Obj Cat_cat) A B))
  (x y : τ (Obj A))
  : τ (@OmegaEquivAlong
      Cat_cat
      (Hom_cat A x y)
      (Hom_cat B
        (@fapp0 A B (idtoequiv_cat_functor_D1 p) x)
        (@fapp0 A B (idtoequiv_cat_functor_D1 p) y))
      (@fapp1_func A B (idtoequiv_cat_functor_D1 p) x y))
≔ @omega_equiv_along_fapp1_D0
    A
    B
    (idtoequiv_cat_functor_D1 p)
    (@omega_equiv_evidence
      Cat_cat A B (@object_path_equiv_D0 Cat_cat A B p))
    x
    y;

symbol idtoequiv_cat_fapp1_D1
  [A B : Cat]
  (p : τ (@= (Obj Cat_cat) A B))
  (x y : τ (Obj A))
  : τ (OmegaEquiv
      Cat_cat
      (Hom_cat A x y)
      (Hom_cat B
        (@fapp0 A B (idtoequiv_cat_functor_D1 p) x)
        (@fapp0 A B (idtoequiv_cat_functor_D1 p) y)))
≔ @omega_equiv_from_along
    Cat_cat
    (Hom_cat A x y)
    (Hom_cat B
      (@fapp0 A B (idtoequiv_cat_functor_D1 p) x)
      (@fapp0 A B (idtoequiv_cat_functor_D1 p) y))
    (@fapp1_func A B (idtoequiv_cat_functor_D1 p) x y)
    (@idtoequiv_cat_fapp1_along_D1 A B p x y);

/*
  Direct category-universe identity interface.

  The classifier rule above makes public equality expose the existing
  fixed-map Sigma package. These readable operations route through the
  canonical encoder, decoder, Product action, and D0b next-hom owners. Raw
  `eq_refl` remains a distinct proof normal form so generic J and `eq_ap`
  retain their guarded literal-reflexivity betas.
*/
// Canonical package reflexivity, distinct from retained generic `eq_refl`.
symbol cat_path_refl
  (A : Cat)
  : τ (CatPathView A A)
≔ @omega_equiv_refl Cat_cat A;

// Encode a public universe path through the canonical categorical encoder.
symbol cat_path_encode
  [A B : Cat]
  (p : τ (@= (Obj Cat_cat) A B))
  : τ (CatPathView A B)
≔ @idtoequiv_cat Cat_cat A B p;

// Decode direct package data through the sole operational category decoder.
symbol cat_path_decode
  [A B : Cat]
  (e : τ (CatPathView A B))
  : τ (@= (Obj Cat_cat) A B)
≔ @omega_equiv_path Cat_cat A B e;

// Decoder after encoder is propositionally the original public path.
symbol cat_path_decode_encode
  [A B : Cat]
  (p : τ (@= (Obj Cat_cat) A B))
  : τ (
      @cat_path_decode A B (@cat_path_encode A B p)
      = p)
≔ @omega_equiv_path_idtoequiv_cat Cat_cat A B p;

// Encoder after decoder is propositionally the original direct package.
symbol cat_path_encode_decode
  [A B : Cat]
  (e : τ (CatPathView A B))
  : τ (
      @cat_path_encode A B (@cat_path_decode A B e)
      = e)
≔ @idtoequiv_cat_omega_equiv_path Cat_cat A B e;

// The selected functor is the public package's forward-arrow projection.
symbol cat_path_functor
  [A B : Cat]
  (e : τ (CatPathView A B))
  : τ (Functor A B)
≔ @omega_equiv_to Cat_cat A B e;

// Direct path evidence is the public package's fixed-arrow certificate.
symbol cat_path_evidence
  [A B : Cat]
  (e : τ (CatPathView A B))
  : τ (@OmegaEquivAlong
      Cat_cat A B (@cat_path_functor A B e))
≔ @omega_equiv_evidence Cat_cat A B e;

// Encoder functors agree propositionally with generic path-to-hom action.
symbol cat_path_encode_functor
  [A B : Cat]
  (p : τ (@= (Obj Cat_cat) A B))
  : τ (
      @cat_path_functor A B (@cat_path_encode A B p)
      = @path_to_hom Cat_cat A B p)
≔ @idtoequiv_cat_path_to_hom Cat_cat A B p;

// Product acts by decoding both inputs, applying generic path action, and
// re-encoding once; reflexive inputs therefore recover canonical package data.
symbol cat_path_product
  [A A' B B' : Cat]
  (eA : τ (CatPathView A A'))
  (eB : τ (CatPathView B B'))
  : τ (CatPathView (Product_cat A B) (Product_cat A' B'))
≔ @cat_path_encode
    (Product_cat A B)
    (Product_cat A' B')
    (@eq_trans
      (Obj Cat_cat)
      (Product_cat A B)
      (Product_cat A' B)
      (Product_cat A' B')
      (@eq_ap
        (Obj Cat_cat)
        (Obj Cat_cat)
        (λ X : Cat, Product_cat X B)
        A
        A'
        (@cat_path_decode A A' eA))
      (@eq_ap
        (Obj Cat_cat)
        (Obj Cat_cat)
        (λ Y : Cat, Product_cat A' Y)
        B
        B'
        (@cat_path_decode B B' eB)));

// Direct fixed-map evidence acts iterably on the next hom level through D0b.
symbol cat_path_fapp1_along
  [A B : Cat]
  (e : τ (CatPathView A B))
  (x y : τ (Obj A))
  : τ (@OmegaEquivAlong
      Cat_cat
      (Hom_cat A x y)
      (Hom_cat B
        (@fapp0 A B (cat_path_functor e) x)
        (@fapp0 A B (cat_path_functor e) y))
      (@fapp1_func A B (cat_path_functor e) x y))
≔ @omega_equiv_along_fapp1_D0
    A
    B
    (cat_path_functor e)
    (cat_path_evidence e)
    x
    y;

// Package the next-hom action as a first-class iterable omega-equivalence.
symbol cat_path_fapp1
  [A B : Cat]
  (e : τ (CatPathView A B))
  (x y : τ (Obj A))
  : τ (OmegaEquiv
      Cat_cat
      (Hom_cat A x y)
      (Hom_cat B
        (@fapp0 A B (cat_path_functor e) x)
        (@fapp0 A B (cat_path_functor e) y)))
≔ @omega_equiv_from_along
    Cat_cat
    (Hom_cat A x y)
    (Hom_cat B
      (@fapp0 A B (cat_path_functor e) x)
      (@fapp0 A B (cat_path_functor e) y))
    (@fapp1_func A B (cat_path_functor e) x y)
    (@cat_path_fapp1_along A B e x y);

/*
  Temporary downstream D0 compatibility for the legacy OneCat iso decoder.

  These names are deliberately explicit compatibility owners. The canonical
  homwise path-selection API lives in the native hom-action extension.
*/
symbol is_discrete_cat_core_equiv_D0
  [C : Cat]
  (d : τ (IsDiscreteCat C))
  : τ (@OmegaEquivAlong
      Cat_cat
      (Core_cat C)
      C
      (Core_incl_func C))
≔ @omega_equiv_along_EQ1_to_D0
    Cat_cat
    (Core_cat C)
    C
    (Core_incl_func C)
    (@is_discrete_cat_core_equiv C d);

// Compatibility D0b specialization of the native field.
symbol discrete_core_homwise_D0
  [C : Cat]
  (d : τ (IsDiscreteCat C))
  (x y : τ (Obj C))
  : τ (@OmegaEquivAlong
      Cat_cat
      (Path_cat (@= (Obj C) x y))
      (Hom_cat C x y)
      (@core_incl_hom_func C x y))
≔ @omega_equiv_along_fapp1_D0
    (Core_cat C)
    C
    (Core_incl_func C)
    (is_discrete_cat_core_equiv_D0 d)
    x y;

// Compatibility selected inverse functor on a core-inclusion hom action.
symbol discrete_core_hom_inv_func_D0
  [C : Cat]
  (d : τ (IsDiscreteCat C))
  (x y : τ (Obj C))
  : τ (Functor
      (Hom_cat C x y)
      (Path_cat (@= (Obj C) x y)))
≔ @omega_equiv_along_left_inv_D0
    Cat_cat
    (Path_cat (@= (Obj C) x y))
    (Hom_cat C x y)
    (@core_incl_hom_func C x y)
    (@discrete_core_homwise_D0 C d x y);

// Compatibility path reader retained only for the legacy OneCat decoder.
symbol hom_to_path_D0
  [C : Cat]
  (d : τ (IsDiscreteCat C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y))
  : τ (@= (Obj C) x y)
≔ @fapp0
    (Hom_cat C x y)
    (Path_cat (@= (Obj C) x y))
    (@discrete_core_hom_inv_func_D0 C d x y)
    f;

// Compatibility recursive left cell at the next hom rung.
symbol discrete_core_hom_left_cell_D0
  [C : Cat]
  (d : τ (IsDiscreteCat C))
  (x y : τ (Obj C))
  : τ (OmegaEquiv
      (Functor_cat
        (Path_cat (@= (Obj C) x y))
        (Path_cat (@= (Obj C) x y)))
      (@comp_cat_fapp0
        (Path_cat (@= (Obj C) x y))
        (Hom_cat C x y)
        (Path_cat (@= (Obj C) x y))
        (@discrete_core_hom_inv_func_D0 C d x y)
        (@core_incl_hom_func C x y))
      (@id_func (Path_cat (@= (Obj C) x y))))
≔ @omega_equiv_along_left_cell_D0
    Cat_cat
    (Path_cat (@= (Obj C) x y))
    (Hom_cat C x y)
    (@core_incl_hom_func C x y)
    (@discrete_core_homwise_D0 C d x y);

// `hom_to_path(path_to_hom(p)) = p`, supplied by the recursive left cell.
symbol hom_to_path_path_to_hom_D0
  [C : Cat]
  (d : τ (IsDiscreteCat C))
  [x y : τ (Obj C)]
  (p : τ (@= (Obj C) x y))
  : τ (@=
      (@= (Obj C) x y)
      (@hom_to_path_D0 C d x y (@path_to_hom C x y p))
      p)
≔ @omega_equiv_along_left_to_component_D0
    (Path_cat (@= (Obj C) x y))
    (Hom_cat C x y)
    (@core_incl_hom_func C x y)
    (@discrete_core_homwise_D0 C d x y)
    p;

// `path_to_hom(hom_to_path(f)) => f` at the directed next hom level.
symbol path_to_hom_hom_to_path_D0
  [C : Cat]
  (d : τ (IsDiscreteCat C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y))
  : τ (Hom
      (Hom_cat C x y)
      (@path_to_hom C x y (@hom_to_path_D0 C d x y f))
      f)
≔ @omega_equiv_along_left_inverse_right_component_D0
    (Path_cat (@= (Obj C) x y))
    (Hom_cat C x y)
    (@core_incl_hom_func C x y)
    (@discrete_core_homwise_D0 C d x y)
    f;

/*
  Object truncation is invariant under fixed-map categorical equivalence.
  This is the categorical consumer of the general TypeEquiv invariance owner;
  it does not yet prove the recursive IsNCat object-truncation theorem.
*/
// Canonical equivalence between the two object-truncation evidence classifiers.
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

// Transport object-truncation evidence forward along the fixed functor.
symbol is_obj_trunc_cat_equiv_to
  [n : TruncLevel]
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (h : τ (IsObjTruncCat n A))
  : τ (IsObjTruncCat n B)
≔ type_equiv_to (@is_obj_trunc_cat_equiv_type_equiv n A B F u) h;

// Transport object-truncation evidence backward along the fixed functor.
symbol is_obj_trunc_cat_equiv_from
  [n : TruncLevel]
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (h : τ (IsObjTruncCat n B))
  : τ (IsObjTruncCat n A)
≔ type_equiv_from (@is_obj_trunc_cat_equiv_type_equiv n A B F u) h;

/*
  OneCat decoder compatibility island.

  The canonical dimension spine above is native EQ1. The following recursive
  D0 decoder theorem remains only because the stable native cast does not
  reify an explicit native package as a raw object path, even at reflexivity.
  Keep its two round trips intact until a separately justified package/path
  coherence theorem exists or the whole island moves to opt-in compatibility.
*/
// In a OneCat, the directed comparison between selected omega inverses is a path.
symbol one_cat_omega_inverse_path
  (X : τ OneCat)
  [x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))]
  (e : τ (OmegaEquiv
      (@ncat_carrier (cat_succ cat_zero) X)
      x
      y))
  : τ (@=
      (Hom (@ncat_carrier (cat_succ cat_zero) X) y x)
      (@omega_equiv_left_inv
        (@ncat_carrier (cat_succ cat_zero) X) x y e)
      (@omega_equiv_right_inv
        (@ncat_carrier (cat_succ cat_zero) X) x y e))
≔ @hom_to_path_D0
    (Hom_cat (@ncat_carrier (cat_succ cat_zero) X) y x)
    (@one_cat_hom_discrete X y x)
    (@omega_equiv_left_inv
      (@ncat_carrier (cat_succ cat_zero) X) x y e)
    (@omega_equiv_right_inv
      (@ncat_carrier (cat_succ cat_zero) X) x y e)
    (@omega_equiv_along_left_to_right_D0
      (@ncat_carrier (cat_succ cat_zero) X)
      x
      y
      (@omega_equiv_to
        (@ncat_carrier (cat_succ cat_zero) X) x y e)
      (@omega_equiv_evidence
        (@ncat_carrier (cat_succ cat_zero) X) x y e));

// Transport the decoded right law to the selected left inverse.
symbol one_cat_omega_right_law_at_left
  (X : τ OneCat)
  [x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))]
  (e : τ (OmegaEquiv
      (@ncat_carrier (cat_succ cat_zero) X)
      x
      y))
  : τ (@=
      (Hom (@ncat_carrier (cat_succ cat_zero) X) y y)
      (@comp_fapp0
        (@ncat_carrier (cat_succ cat_zero) X)
        y x y
        (@omega_equiv_to
          (@ncat_carrier (cat_succ cat_zero) X) x y e)
        (@omega_equiv_left_inv
          (@ncat_carrier (cat_succ cat_zero) X) x y e))
      (@id (@ncat_carrier (cat_succ cat_zero) X) y))
≔ @eq_trans
    (Hom (@ncat_carrier (cat_succ cat_zero) X) y y)
    (@comp_fapp0
      (@ncat_carrier (cat_succ cat_zero) X)
      y x y
      (@omega_equiv_to
        (@ncat_carrier (cat_succ cat_zero) X) x y e)
      (@omega_equiv_left_inv
        (@ncat_carrier (cat_succ cat_zero) X) x y e))
    (@comp_fapp0
      (@ncat_carrier (cat_succ cat_zero) X)
      y x y
      (@omega_equiv_to
        (@ncat_carrier (cat_succ cat_zero) X) x y e)
      (@omega_equiv_right_inv
        (@ncat_carrier (cat_succ cat_zero) X) x y e))
    (@id (@ncat_carrier (cat_succ cat_zero) X) y)
    (@eq_ap
      (Hom (@ncat_carrier (cat_succ cat_zero) X) y x)
      (Hom (@ncat_carrier (cat_succ cat_zero) X) y y)
      (λ q : τ (Hom (@ncat_carrier (cat_succ cat_zero) X) y x),
        @comp_fapp0
          (@ncat_carrier (cat_succ cat_zero) X)
          y x y
          (@omega_equiv_to
            (@ncat_carrier (cat_succ cat_zero) X) x y e)
          q)
      (@omega_equiv_left_inv
        (@ncat_carrier (cat_succ cat_zero) X) x y e)
      (@omega_equiv_right_inv
        (@ncat_carrier (cat_succ cat_zero) X) x y e)
      (@one_cat_omega_inverse_path X x y e))
    (@omega_equiv_right_law
      (@ncat_carrier (cat_succ cat_zero) X) x y e);

// Reconstruct ordinary isomorphism evidence from OneCat omega-equivalence.
symbol one_cat_omega_iso_evidence
  (X : τ OneCat)
  [x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))]
  (e : τ (OmegaEquiv
      (@ncat_carrier (cat_succ cat_zero) X)
      x
      y))
  : τ (IsoEvidence
      (@ncat_carrier (cat_succ cat_zero) X)
      x
      y)
≔ Struct_sigma
    (@omega_equiv_to
      (@ncat_carrier (cat_succ cat_zero) X) x y e)
    (Struct_sigma
      (@omega_equiv_left_inv
        (@ncat_carrier (cat_succ cat_zero) X) x y e)
      (Struct_sigma
        (@omega_equiv_left_law
          (@ncat_carrier (cat_succ cat_zero) X) x y e)
        (@one_cat_omega_right_law_at_left X x y e)));


// The reconstructed left-law proof agrees with the original ordinary proof.
symbol one_cat_omega_iso_lift_left_path
  (X : τ OneCat)
  [x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))]
  (i : τ (IsoEvidence
      (@ncat_carrier (cat_succ cat_zero) X) x y))
  : τ (@=
      (@=
        (Hom (@ncat_carrier (cat_succ cat_zero) X) x x)
        (@comp_fapp0
          (@ncat_carrier (cat_succ cat_zero) X)
          x y x
          (@iso_evidence_from
            (@ncat_carrier (cat_succ cat_zero) X) x y i)
          (@iso_evidence_to
            (@ncat_carrier (cat_succ cat_zero) X) x y i))
        (@id (@ncat_carrier (cat_succ cat_zero) X) x))
      (@iso_evidence_left
        (@ncat_carrier (cat_succ cat_zero) X) x y
        (@one_cat_omega_iso_evidence
          X x y
          (@iso_evidence_omega_equiv
            (@ncat_carrier (cat_succ cat_zero) X) x y i)))
      (@iso_evidence_left
        (@ncat_carrier (cat_succ cat_zero) X) x y i))
≔ @discrete_cat_path_proof
    (Hom_cat (@ncat_carrier (cat_succ cat_zero) X) x x)
    (@one_cat_hom_discrete X x x)
    (@comp_fapp0
      (@ncat_carrier (cat_succ cat_zero) X)
      x y x
      (@iso_evidence_from
        (@ncat_carrier (cat_succ cat_zero) X) x y i)
      (@iso_evidence_to
        (@ncat_carrier (cat_succ cat_zero) X) x y i))
    (@id (@ncat_carrier (cat_succ cat_zero) X) x)
    (@iso_evidence_left
      (@ncat_carrier (cat_succ cat_zero) X) x y
      (@one_cat_omega_iso_evidence
        X x y
        (@iso_evidence_omega_equiv
          (@ncat_carrier (cat_succ cat_zero) X) x y i)))
    (@iso_evidence_left
      (@ncat_carrier (cat_succ cat_zero) X) x y i);

// The transported right-law proof agrees with the original ordinary proof.
symbol one_cat_omega_iso_lift_right_path
  (X : τ OneCat)
  [x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))]
  (i : τ (IsoEvidence
      (@ncat_carrier (cat_succ cat_zero) X) x y))
  : τ (@=
      (@=
        (Hom (@ncat_carrier (cat_succ cat_zero) X) y y)
        (@comp_fapp0
          (@ncat_carrier (cat_succ cat_zero) X)
          y x y
          (@iso_evidence_to
            (@ncat_carrier (cat_succ cat_zero) X) x y i)
          (@iso_evidence_from
            (@ncat_carrier (cat_succ cat_zero) X) x y i))
        (@id (@ncat_carrier (cat_succ cat_zero) X) y))
      (@iso_evidence_right
        (@ncat_carrier (cat_succ cat_zero) X) x y
        (@one_cat_omega_iso_evidence
          X x y
          (@iso_evidence_omega_equiv
            (@ncat_carrier (cat_succ cat_zero) X) x y i)))
      (@iso_evidence_right
        (@ncat_carrier (cat_succ cat_zero) X) x y i))
≔ @discrete_cat_path_proof
    (Hom_cat (@ncat_carrier (cat_succ cat_zero) X) y y)
    (@one_cat_hom_discrete X y y)
    (@comp_fapp0
      (@ncat_carrier (cat_succ cat_zero) X)
      y x y
      (@iso_evidence_to
        (@ncat_carrier (cat_succ cat_zero) X) x y i)
      (@iso_evidence_from
        (@ncat_carrier (cat_succ cat_zero) X) x y i))
    (@id (@ncat_carrier (cat_succ cat_zero) X) y)
    (@iso_evidence_right
      (@ncat_carrier (cat_succ cat_zero) X) x y
      (@one_cat_omega_iso_evidence
        X x y
        (@iso_evidence_omega_equiv
          (@ncat_carrier (cat_succ cat_zero) X) x y i)))
    (@iso_evidence_right
      (@ncat_carrier (cat_succ cat_zero) X) x y i);

// Reconstructing ordinary evidence after its omega lift is propositionally identity.
symbol one_cat_omega_iso_lift_retract
  (X : τ OneCat)
  [x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))]
  (i : τ (IsoEvidence
      (@ncat_carrier (cat_succ cat_zero) X) x y))
  : τ (@=
      (IsoEvidence (@ncat_carrier (cat_succ cat_zero) X) x y)
      (@one_cat_omega_iso_evidence
        X x y
        (@iso_evidence_omega_equiv
          (@ncat_carrier (cat_succ cat_zero) X) x y i))
      i)
≔ Struct_sigma
    (eq_refl
      (@iso_evidence_to
        (@ncat_carrier (cat_succ cat_zero) X) x y i))
    (Struct_sigma
      (eq_refl
        (@iso_evidence_from
          (@ncat_carrier (cat_succ cat_zero) X) x y i))
      (Struct_sigma
        (@one_cat_omega_iso_lift_left_path X x y i)
        (@const_pathover
          (@=
            (Hom (@ncat_carrier (cat_succ cat_zero) X) x x)
            (@comp_fapp0
              (@ncat_carrier (cat_succ cat_zero) X)
              x y x
              (@iso_evidence_from
                (@ncat_carrier (cat_succ cat_zero) X) x y i)
              (@iso_evidence_to
                (@ncat_carrier (cat_succ cat_zero) X) x y i))
            (@id (@ncat_carrier (cat_succ cat_zero) X) x))
          (@=
            (Hom (@ncat_carrier (cat_succ cat_zero) X) y y)
            (@comp_fapp0
              (@ncat_carrier (cat_succ cat_zero) X)
              y x y
              (@iso_evidence_to
                (@ncat_carrier (cat_succ cat_zero) X) x y i)
              (@iso_evidence_from
                (@ncat_carrier (cat_succ cat_zero) X) x y i))
            (@id (@ncat_carrier (cat_succ cat_zero) X) y))
          (@iso_evidence_left
            (@ncat_carrier (cat_succ cat_zero) X) x y
            (@one_cat_omega_iso_evidence
              X x y
              (@iso_evidence_omega_equiv
                (@ncat_carrier (cat_succ cat_zero) X) x y i)))
          (@iso_evidence_left
            (@ncat_carrier (cat_succ cat_zero) X) x y i)
          (@iso_evidence_right
            (@ncat_carrier (cat_succ cat_zero) X) x y
            (@one_cat_omega_iso_evidence
              X x y
              (@iso_evidence_omega_equiv
                (@ncat_carrier (cat_succ cat_zero) X) x y i)))
          (@iso_evidence_right
            (@ncat_carrier (cat_succ cat_zero) X) x y i)
          (@one_cat_omega_iso_lift_left_path X x y i)
          (@one_cat_omega_iso_lift_right_path X x y i))));

// Reconstruction of a path-encoded omega-equivalence agrees with idtoiso.
symbol one_cat_omega_iso_evidence_idtoequiv
  (X : τ OneCat)
  [x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))]
  (p : τ (@= (Obj (@ncat_carrier (cat_succ cat_zero) X)) x y))
  : τ (@=
      (IsoEvidence (@ncat_carrier (cat_succ cat_zero) X) x y)
      (@one_cat_omega_iso_evidence
        X x y
        (@idtoequiv_cat
          (@ncat_carrier (cat_succ cat_zero) X) x y p))
      (@idtoiso_cat
        (@ncat_carrier (cat_succ cat_zero) X) x y p))
≔ @eq_trans
    (IsoEvidence (@ncat_carrier (cat_succ cat_zero) X) x y)
    (@one_cat_omega_iso_evidence
      X x y
      (@idtoequiv_cat
        (@ncat_carrier (cat_succ cat_zero) X) x y p))
    (@one_cat_omega_iso_evidence
      X x y
      (@iso_evidence_omega_equiv
        (@ncat_carrier (cat_succ cat_zero) X) x y
        (@idtoiso_cat
          (@ncat_carrier (cat_succ cat_zero) X) x y p)))
    (@idtoiso_cat
      (@ncat_carrier (cat_succ cat_zero) X) x y p)
    (@eq_ap
      (OmegaEquiv (@ncat_carrier (cat_succ cat_zero) X) x y)
      (IsoEvidence (@ncat_carrier (cat_succ cat_zero) X) x y)
      (λ e : τ (OmegaEquiv
          (@ncat_carrier (cat_succ cat_zero) X) x y),
        @one_cat_omega_iso_evidence X x y e)
      (@idtoequiv_cat
        (@ncat_carrier (cat_succ cat_zero) X) x y p)
      (@iso_evidence_omega_equiv
        (@ncat_carrier (cat_succ cat_zero) X) x y
        (@idtoiso_cat
          (@ncat_carrier (cat_succ cat_zero) X) x y p))
      (@eq_sym
        (OmegaEquiv (@ncat_carrier (cat_succ cat_zero) X) x y)
        (@iso_evidence_omega_equiv
          (@ncat_carrier (cat_succ cat_zero) X) x y
          (@idtoiso_cat
            (@ncat_carrier (cat_succ cat_zero) X) x y p))
        (@idtoequiv_cat
          (@ncat_carrier (cat_succ cat_zero) X) x y p)
        (@iso_evidence_omega_equiv_idtoiso
          (@ncat_carrier (cat_succ cat_zero) X) x y p)))
    (@one_cat_omega_iso_lift_retract
      X x y
      (@idtoiso_cat
        (@ncat_carrier (cat_succ cat_zero) X) x y p));

// Derived OneCat-scoped ordinary-iso decoder through omega univalence.
symbol one_cat_iso_path
  (X : τ OneCat)
  [x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))]
  (i : τ (IsoEvidence
      (@ncat_carrier (cat_succ cat_zero) X)
      x
      y))
  : τ (@= (Obj (@ncat_carrier (cat_succ cat_zero) X)) x y)
≔ @omega_equiv_path
    (@ncat_carrier (cat_succ cat_zero) X)
    x
    y
    (@iso_evidence_omega_equiv
      (@ncat_carrier (cat_succ cat_zero) X)
      x
      y
      i);

// The derived decoder is a left inverse of the ordinary path encoder.
symbol one_cat_iso_path_idtoiso
  (X : τ OneCat)
  [x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))]
  (p : τ (@= (Obj (@ncat_carrier (cat_succ cat_zero) X)) x y))
  : τ (@=
      (@= (Obj (@ncat_carrier (cat_succ cat_zero) X)) x y)
      (@one_cat_iso_path X x y
        (@idtoiso_cat
          (@ncat_carrier (cat_succ cat_zero) X)
          x
          y
          p))
      p)
≔ @eq_trans
    (@= (Obj (@ncat_carrier (cat_succ cat_zero) X)) x y)
    (@one_cat_iso_path X x y
      (@idtoiso_cat
        (@ncat_carrier (cat_succ cat_zero) X)
        x
        y
        p))
    (@omega_equiv_path
      (@ncat_carrier (cat_succ cat_zero) X)
      x
      y
      (@idtoequiv_cat
        (@ncat_carrier (cat_succ cat_zero) X)
        x
        y
        p))
    p
    (@eq_ap
      (OmegaEquiv (@ncat_carrier (cat_succ cat_zero) X) x y)
      (@= (Obj (@ncat_carrier (cat_succ cat_zero) X)) x y)
      (λ e : τ (OmegaEquiv
          (@ncat_carrier (cat_succ cat_zero) X) x y),
        @omega_equiv_path
          (@ncat_carrier (cat_succ cat_zero) X)
          x
          y
          e)
      (@iso_evidence_omega_equiv
        (@ncat_carrier (cat_succ cat_zero) X)
        x
        y
        (@idtoiso_cat
          (@ncat_carrier (cat_succ cat_zero) X)
          x
          y
          p))
      (@idtoequiv_cat
        (@ncat_carrier (cat_succ cat_zero) X)
        x
        y
        p)
      (@iso_evidence_omega_equiv_idtoiso
        (@ncat_carrier (cat_succ cat_zero) X)
        x
        y
        p))
    (@omega_equiv_path_idtoequiv_cat
      (@ncat_carrier (cat_succ cat_zero) X)
      x
      y
      p);

// The ordinary encoder after the scoped decoder is propositionally identity.
symbol one_cat_idtoiso_iso_path
  (X : τ OneCat)
  [x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))]
  (i : τ (IsoEvidence
      (@ncat_carrier (cat_succ cat_zero) X) x y))
  : τ (@=
      (IsoEvidence (@ncat_carrier (cat_succ cat_zero) X) x y)
      (@idtoiso_cat
        (@ncat_carrier (cat_succ cat_zero) X)
        x
        y
        (@one_cat_iso_path X x y i))
      i)
≔ @eq_trans
    (IsoEvidence (@ncat_carrier (cat_succ cat_zero) X) x y)
    (@idtoiso_cat
      (@ncat_carrier (cat_succ cat_zero) X)
      x
      y
      (@one_cat_iso_path X x y i))
    (@one_cat_omega_iso_evidence
      X x y
      (@idtoequiv_cat
        (@ncat_carrier (cat_succ cat_zero) X)
        x
        y
        (@one_cat_iso_path X x y i)))
    i
    (@eq_sym
      (IsoEvidence (@ncat_carrier (cat_succ cat_zero) X) x y)
      (@one_cat_omega_iso_evidence
        X x y
        (@idtoequiv_cat
          (@ncat_carrier (cat_succ cat_zero) X)
          x
          y
          (@one_cat_iso_path X x y i)))
      (@idtoiso_cat
        (@ncat_carrier (cat_succ cat_zero) X)
        x
        y
        (@one_cat_iso_path X x y i))
      (@one_cat_omega_iso_evidence_idtoequiv
        X x y (@one_cat_iso_path X x y i)))
    (@eq_trans
      (IsoEvidence (@ncat_carrier (cat_succ cat_zero) X) x y)
      (@one_cat_omega_iso_evidence
        X x y
        (@idtoequiv_cat
          (@ncat_carrier (cat_succ cat_zero) X)
          x
          y
          (@one_cat_iso_path X x y i)))
      (@one_cat_omega_iso_evidence
        X x y
        (@iso_evidence_omega_equiv
          (@ncat_carrier (cat_succ cat_zero) X) x y i))
      i
      (@eq_ap
        (OmegaEquiv (@ncat_carrier (cat_succ cat_zero) X) x y)
        (IsoEvidence (@ncat_carrier (cat_succ cat_zero) X) x y)
        (λ e : τ (OmegaEquiv
            (@ncat_carrier (cat_succ cat_zero) X) x y),
          @one_cat_omega_iso_evidence X x y e)
        (@idtoequiv_cat
          (@ncat_carrier (cat_succ cat_zero) X)
          x
          y
          (@one_cat_iso_path X x y i))
        (@iso_evidence_omega_equiv
          (@ncat_carrier (cat_succ cat_zero) X) x y i)
        (@idtoequiv_cat_omega_equiv_path
          (@ncat_carrier (cat_succ cat_zero) X)
          x
          y
          (@iso_evidence_omega_equiv
            (@ncat_carrier (cat_succ cat_zero) X) x y i)))
      (@one_cat_omega_iso_lift_retract X x y i));

// OneCat-indexed specified-inverse capability with the scoped decoder.
symbol OneCatIsoUnivalenceByDecoder
  (X : τ OneCat)
  : Grpd
≔ @Pi_grpd
    (Obj (@ncat_carrier (cat_succ cat_zero) X))
    (λ x : τ (Obj (@ncat_carrier (cat_succ cat_zero) X)),
      @Pi_grpd
        (Obj (@ncat_carrier (cat_succ cat_zero) X))
        (λ y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X)),
          @EquivByInverse
            (@= (Obj (@ncat_carrier (cat_succ cat_zero) X)) x y)
            (IsoEvidence (@ncat_carrier (cat_succ cat_zero) X) x y)
            (λ p : τ (@= (Obj
                (@ncat_carrier (cat_succ cat_zero) X)) x y),
              @idtoiso_cat
                (@ncat_carrier (cat_succ cat_zero) X) x y p)
            (λ i : τ (IsoEvidence
                (@ncat_carrier (cat_succ cat_zero) X) x y),
              @one_cat_iso_path X x y i)));

// Scoped specified-inverse ordinary-isomorphism univalence for OneCat.
symbol one_cat_iso_univalence_by_decoder
  (X : τ OneCat)
  : τ (OneCatIsoUnivalenceByDecoder X)
≔ λ x : τ (Obj (@ncat_carrier (cat_succ cat_zero) X)),
   λ y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X)),
    @Product_pair_grpd
      (@Pi_grpd
        (@= (Obj (@ncat_carrier (cat_succ cat_zero) X)) x y)
        (λ p : τ (@= (Obj
            (@ncat_carrier (cat_succ cat_zero) X)) x y),
          @=
            (@= (Obj (@ncat_carrier (cat_succ cat_zero) X)) x y)
            (@one_cat_iso_path
              X x y
              (@idtoiso_cat
                (@ncat_carrier (cat_succ cat_zero) X) x y p))
            p))
      (@Pi_grpd
        (IsoEvidence (@ncat_carrier (cat_succ cat_zero) X) x y)
        (λ i : τ (IsoEvidence
            (@ncat_carrier (cat_succ cat_zero) X) x y),
          @=
            (IsoEvidence (@ncat_carrier (cat_succ cat_zero) X) x y)
            (@idtoiso_cat
              (@ncat_carrier (cat_succ cat_zero) X)
              x
              y
              (@one_cat_iso_path X x y i))
            i))
      (λ p : τ (@= (Obj (@ncat_carrier (cat_succ cat_zero) X)) x y),
        @one_cat_iso_path_idtoiso X x y p)
      (λ i : τ (IsoEvidence
          (@ncat_carrier (cat_succ cat_zero) X) x y),
        @one_cat_idtoiso_iso_path X x y i);

// Contractible-fibre ordinary-isomorphism univalence derived from the decoder.
symbol one_cat_iso_univalence
  (X : τ OneCat)
  : τ (CatIsoUnivalence
      (@ncat_carrier (cat_succ cat_zero) X))
≔ λ x : τ (Obj (@ncat_carrier (cat_succ cat_zero) X)),
   λ y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X)),
    @is_equiv_map_by_inverse
      (@= (Obj (@ncat_carrier (cat_succ cat_zero) X)) x y)
      (IsoEvidence (@ncat_carrier (cat_succ cat_zero) X) x y)
      (λ p : τ (@= (Obj (@ncat_carrier (cat_succ cat_zero) X)) x y),
        @idtoiso_cat
          (@ncat_carrier (cat_succ cat_zero) X) x y p)
      (λ i : τ (IsoEvidence
          (@ncat_carrier (cat_succ cat_zero) X) x y),
        @one_cat_iso_path X x y i)
      (@one_cat_iso_univalence_by_decoder X x y);

// Named ordinary type equivalence between OneCat object paths and isomorphisms.
symbol one_cat_iso_type_equiv
  (X : τ OneCat)
  (x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X)))
  : τ (TypeEquiv
      (@= (Obj (@ncat_carrier (cat_succ cat_zero) X)) x y)
      (IsoEvidence (@ncat_carrier (cat_succ cat_zero) X) x y))
≔ @Struct_sigma
    (Function_grpd
      (@= (Obj (@ncat_carrier (cat_succ cat_zero) X)) x y)
      (IsoEvidence (@ncat_carrier (cat_succ cat_zero) X) x y))
    (λ f : τ (Function_grpd
        (@= (Obj (@ncat_carrier (cat_succ cat_zero) X)) x y)
        (IsoEvidence (@ncat_carrier (cat_succ cat_zero) X) x y)),
      @IsEquivMap
        (@= (Obj (@ncat_carrier (cat_succ cat_zero) X)) x y)
        (IsoEvidence (@ncat_carrier (cat_succ cat_zero) X) x y)
        f)
    (λ p : τ (@= (Obj (@ncat_carrier (cat_succ cat_zero) X)) x y),
      @idtoiso_cat
        (@ncat_carrier (cat_succ cat_zero) X) x y p)
    (@one_cat_iso_univalence X x y);
