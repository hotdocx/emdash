/*
  Minimal internal Path_int action probe.

  The public construction uses only iterated ordinary functor action:

    Path_map(f)       := Path_int_1(f)
    Path_transf(h)    := (Path_int_1)_1(h).

  No external family of transfor components and no hand-written naturality
  square occurs in the interface.
*/

require open emdash.emdash3_2;

// Internal path-category constructor.
injective symbol probe_path_int_internal
  : τ (Functor Grpd_cat Cat_cat);

rule @fapp0 Grpd_cat Cat_cat probe_path_int_internal $A
  ↪ Path_cat $A;

// Readable alias for the first internal action.
symbol probe_path_map_internal
  [A B : Grpd]
  (f : τ (@Function_grpd A B))
  : τ (Functor (Path_cat A) (Path_cat B))
≔ @fapp1_fapp0
    Grpd_cat Cat_cat probe_path_int_internal
    A B f;

// Computation of Path_int's first action.
rule @fapp0
      _ _
      (@fapp1_fapp0
        Grpd_cat Cat_cat probe_path_int_internal
        _ _ $f)
      $x
  ↪ $f $x;

rule @fapp1_func
      _ _
      (@fapp1_fapp0
        Grpd_cat Cat_cat probe_path_int_internal
        $A $B $f)
      $x $y
  ↪ @fapp1_fapp0
      Grpd_cat Cat_cat probe_path_int_internal
      (@= $A $x $y)
      (@= $B ($f $x) ($f $y))
      (λ p : τ (@= $A $x $y),
        @eq_ap $A $B $f $x $y p);

// lhs-audit: keep 1,2 -- Path_cat guards the generic identity-action overlap.
rule @fapp1_fapp0
      (Path_cat $A) (Path_cat $B)
      (@fapp1_fapp0
        Grpd_cat Cat_cat probe_path_int_internal
        _ _ $f)
      $x $y $p
  ↪ @eq_ap $A $B $f $x $y $p;

// Direct proof-time stable view of Path_int functoriality.  Generic strict
// functoriality first produces action on categorical Grpd composition; this
// bridge avoids relying on transitivity through the existing comparison with
// the pointwise `grpd_comp_function` head.
unif_rule
  @comp_fapp0
    Cat_cat
    (Path_cat $A) (Path_cat $B) (Path_cat $C)
    (@fapp1_fapp0
      Grpd_cat Cat_cat probe_path_int_internal
      $B $C $g)
    (@fapp1_fapp0
      Grpd_cat Cat_cat probe_path_int_internal
      $A $B $f)
  ≡ @fapp1_fapp0
    Grpd_cat Cat_cat probe_path_int_internal
    $A $C
    (@grpd_comp_function $A $B $C $g $f)
  ↪ [ tt ≡ tt ];

// Congruence-level companion after generic strict functoriality has already
// folded the composite to action on categorical Grpd composition.
unif_rule
  @fapp1_fapp0
    Grpd_cat Cat_cat probe_path_int_internal
    $A $C
    (@comp_fapp0 Grpd_cat $A $B $C $g $f)
  ≡ @fapp1_fapp0
    Grpd_cat Cat_cat probe_path_int_internal
    $A $C
    (@grpd_comp_function $A $B $C $g $f)
  ↪ [ tt ≡ tt ];

// Canonical off-diagonal action of a function equality.
symbol probe_path_transf_cell_internal
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

// Readable alias for the second internal action.
symbol probe_path_transf_internal
  [A B : Grpd]
  [f g : τ (@Function_grpd A B)]
  (h : τ (@= (@Function_grpd A B) f g))
  : τ (Transf
      (@probe_path_map_internal A B f)
      (@probe_path_map_internal A B g))
≔ @fapp1_fapp0
    (Path_cat (@Function_grpd A B))
    (Functor_cat (Path_cat A) (Path_cat B))
    (@fapp1_func
      Grpd_cat Cat_cat probe_path_int_internal A B)
    f g h;

// Point component of the internal second action.
rule @tapp0_fapp0
      _ _ _ _
      $x
      (@fapp1_fapp0
        _ _
        (@fapp1_func
          Grpd_cat Cat_cat probe_path_int_internal $A $B)
        $f $g $h)
  ↪ @PiHapply
      $A (λ _ : τ $A, $B) $f $g $h $x;

// Full off-diagonal action stays internal and iterable.
rule @tapp1_func
      _ _ _ _
      $x $y
      (@fapp1_fapp0
        (Path_cat (@Pi_grpd $A (λ _ : τ $A, $B)))
        (Functor_cat (Path_cat $A) (Path_cat $B))
        (@fapp1_func
          Grpd_cat Cat_cat probe_path_int_internal $A $B)
        $f $g $h)
  ↪ @fapp1_fapp0
      Grpd_cat Cat_cat probe_path_int_internal
      (@= $A $x $y)
      (@= $B ($f $x) ($g $y))
      (λ p : τ (@= $A $x $y),
        @probe_path_transf_cell_internal
          $A $B $f $g $h $x $y p);

rule @tapp1_fapp0
      _ _ _ _
      $x $y
      (@fapp1_fapp0
        (Path_cat (@Pi_grpd $A (λ _ : τ $A, $B)))
        (Functor_cat (Path_cat $A) (Path_cat $B))
        (@fapp1_func
          Grpd_cat Cat_cat probe_path_int_internal $A $B)
        $f $g $h)
      $p
  ↪ @probe_path_transf_cell_internal
      $A $B $f $g $h $x $y $p;

/*
  Whole-functor endpoint comparison for Core inclusion along F.

  This is proof-time conversion only.  It does not introduce a transfor or
  ask the caller for a naturality square:

    F o CoreIncl(C)  ≡  CoreIncl(D) o Path_int_1(F_0).

  The point/arrow theorem is J-derived (`F(path_to_hom p) =
  path_to_hom(ap F_0 p)`).  The equation registers its whole-functor form at
  the two rigid composite heads.
*/
// Transparent semantic object-function of an ordinary functor.
symbol probe_functor_object_function_semantic
  [C D : Cat]
  (F : τ (Functor C D))
  : τ (@Function_grpd (Obj C) (Obj D))
≔ λ x : τ (Obj C), @fapp0 C D F x;

// Rigid normal-form view used only inside proof-time endpoint equations.
injective symbol probe_functor_object_function
  [C D : Cat]
  (F : τ (Functor C D))
  : τ (@Function_grpd (Obj C) (Obj D));

rule @probe_functor_object_function _ _ $F $x
  ↪ @probe_functor_object_function_semantic _ _ $F $x;

// Internal extensional agreement of the rigid view with x |-> F[x].
symbol probe_functor_object_function_agrees
  [C D : Cat]
  (F : τ (Functor C D))
  : τ (@=
      (@Function_grpd (Obj C) (Obj D))
      (@probe_functor_object_function C D F)
      (@probe_functor_object_function_semantic C D F))
≔ @PiFunext
    (Obj C)
    (λ _ : τ (Obj C), Obj D)
    (@probe_functor_object_function C D F)
    (@probe_functor_object_function_semantic C D F)
    (λ x : τ (Obj C),
      @eq_refl (Obj D) (@fapp0 C D F x));

unif_rule
  @comp_fapp0 Cat_cat
    (Path_cat (Obj $C)) $C $D
    $F
    (Core_incl_func $C)
  ≡ @comp_fapp0 Cat_cat
    (Path_cat (Obj $C)) (Path_cat (Obj $D)) $D
    (Core_incl_func $D)
    (@fapp1_fapp0
      Grpd_cat Cat_cat probe_path_int_internal
      (Obj $C) (Obj $D)
      (@probe_functor_object_function $C $D $F))
  ↪ [ tt ≡ tt ];

// Typed eq_refl exercises the proof-time comparison.
symbol probe_core_incl_internal_eq
  [C D : Cat]
  (F : τ (Functor C D))
  : τ (@=
      (Functor (Core_cat C) D)
      (@comp_cat_fapp0
        (Core_cat C) C D
        F
        (Core_incl_func C))
      (@comp_cat_fapp0
        (Core_cat C) (Core_cat D) D
        (Core_incl_func D)
        (@fapp1_fapp0
          Grpd_cat Cat_cat probe_path_int_internal
          (Obj C) (Obj D)
          (@probe_functor_object_function C D F))))
≔ @eq_refl
    (Functor (Core_cat C) D)
    (@comp_cat_fapp0
      (Core_cat C) C D
      F
      (Core_incl_func C));

/*
  Internal lift of an object function A -> Obj(C) to a functor Path(A) -> C.

  This is an ordinary composite of two existing functors:

    Path_int_1(A,Obj(C))
      : Hom_Grpd(A,Obj(C)) -> Functor(Path(A),Core(C))

    postcompose(CoreIncl(C))
      : Functor(Path(A),Core(C)) -> Functor(Path(A),C).
*/
symbol probe_path_lift_internal
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
      Grpd_cat Cat_cat probe_path_int_internal
      A (Obj C));

// Object projection after postcomposition specifically by Core inclusion.
// This is the semantic consumer used by PathLift; it avoids choosing a broad
// object beta for every stable Cat postcomposition head.
rule @fapp0
      $W $C
      (@hom_postcomp_fapp0
        Cat_cat Cat_cat (@id Cat_cat Cat_cat)
        $W (Path_cat (Obj $C)) $C
        (Core_incl_func $C) $G)
      $w
  ↪ @fapp0 $W (Path_cat (Obj $C)) $G $w;

assert
  [W C : Cat]
  (G : τ (Functor W (Path_cat (Obj C))))
  (w : τ (Obj W))
  ⊢ @fapp0
      W C
      (@hom_postcomp_fapp0
        Cat_cat Cat_cat (@id Cat_cat Cat_cat)
        W (Path_cat (Obj C)) C
        (Core_incl_func C) G)
      w
    ≡ @fapp0 W (Path_cat (Obj C)) G w;

/*
  The two reusable whole-functor endpoint equations.

  They are proof-time views of the transparent internal composite above, not
  naturality-square terms or constructor-specific runtime rules.  They are
  registered at the composite's actual rigid normal form because Lambdapi
  does not reliably chain the Core comparison, generic composition, and the
  Grpd pointwise-composition comparison under an outer functor context.
*/
unif_rule
  @comp_fapp0
    Cat_cat
    (Path_cat $A) $C $D
    $F
    (@hom_postcomp_fapp0
      Cat_cat Cat_cat (@id Cat_cat Cat_cat)
      (Path_cat $A) (Path_cat (Obj $C)) $C
      (Core_incl_func $C)
      (@fapp1_fapp0
        Grpd_cat Cat_cat probe_path_int_internal
        $A (Obj $C) $f))
  ≡ @hom_postcomp_fapp0
    Cat_cat Cat_cat (@id Cat_cat Cat_cat)
    (Path_cat $A) (Path_cat (Obj $D)) $D
    (Core_incl_func $D)
    (@fapp1_fapp0
      Grpd_cat Cat_cat probe_path_int_internal
      $A (Obj $D)
      (@grpd_comp_function
        $A (Obj $C) (Obj $D)
        (@probe_functor_object_function $C $D $F)
        $f))
  ↪ [ tt ≡ tt ];

unif_rule
  @hom_postcomp_fapp0
    Cat_cat Cat_cat (@id Cat_cat Cat_cat)
    (Path_cat $A) (Path_cat (Obj $C)) $C
    (Core_incl_func $C)
    (@fapp1_fapp0
      Grpd_cat Cat_cat probe_path_int_internal
      $A (Obj $C)
      (@comp_fapp0 Grpd_cat $A $B (Obj $C) $f $g))
  ≡ @hom_postcomp_fapp0
    Cat_cat Cat_cat (@id Cat_cat Cat_cat)
    (Path_cat $A) (Path_cat (Obj $C)) $C
    (Core_incl_func $C)
    (@fapp1_fapp0
      Grpd_cat Cat_cat probe_path_int_internal
      $A (Obj $C)
      (@grpd_comp_function $A $B (Obj $C) $f $g))
  ↪ [ tt ≡ tt ];

// Typed reflexivity exercises postcomposition compatibility of PathLift.
symbol probe_path_lift_postcomp_eq
  [A : Grpd]
  [C D : Cat]
  (F : τ (Functor C D))
  (f : τ (@Function_grpd A (Obj C)))
  : τ (@=
      (Functor (Path_cat A) D)
      (@comp_cat_fapp0
        (Path_cat A) C D
        F
        (@fapp0
          (Path_cat (@Function_grpd A (Obj C)))
          (Functor_cat (Path_cat A) C)
          (@probe_path_lift_internal A C)
          f))
      (@fapp0
        (Path_cat (@Function_grpd A (Obj D)))
        (Functor_cat (Path_cat A) D)
        (@probe_path_lift_internal A D)
        (@grpd_comp_function
          A (Obj C) (Obj D)
          (@probe_functor_object_function C D F)
          f)))
≔ @eq_refl
    (Functor (Path_cat A) D)
    (@comp_cat_fapp0
      (Path_cat A) C D
      F
      (@fapp0
        (Path_cat (@Function_grpd A (Obj C)))
        (Functor_cat (Path_cat A) C)
        (@probe_path_lift_internal A C)
        f));

// Typed reflexivity exercises precomposition compatibility of PathLift.
symbol probe_path_lift_precomp_eq
  [A B : Grpd]
  [C : Cat]
  (f : τ (@Function_grpd B (Obj C)))
  (g : τ (@Function_grpd A B))
  : τ (@=
      (Functor (Path_cat A) C)
      (@comp_cat_fapp0
        (Path_cat A) (Path_cat B) C
        (@fapp0
          (Path_cat (@Function_grpd B (Obj C)))
          (Functor_cat (Path_cat B) C)
          (@probe_path_lift_internal B C)
          f)
        (@probe_path_map_internal A B g))
      (@fapp0
        (Path_cat (@Function_grpd A (Obj C)))
        (Functor_cat (Path_cat A) C)
        (@probe_path_lift_internal A C)
        (@grpd_comp_function A B (Obj C) f g)))
≔ @eq_refl
    (Functor (Path_cat A) C)
    (@comp_cat_fapp0
      (Path_cat A) (Path_cat B) C
      (@fapp0
        (Path_cat (@Function_grpd B (Obj C)))
        (Functor_cat (Path_cat B) C)
        (@probe_path_lift_internal B C)
        f)
      (@probe_path_map_internal A B g));

symbol probe_nat_succ_function_internal
  : τ (@Function_grpd Nat_grpd Nat_grpd)
≔ λ n : τ Nat_grpd, succ n;

symbol probe_nat_succ_func_internal
  : τ (Functor (Path_cat Nat_grpd) (Path_cat Nat_grpd))
≔ @probe_path_map_internal
    Nat_grpd Nat_grpd
    probe_nat_succ_function_internal;

symbol probe_iter_power_internal
  [C : Cat]
  (S : τ (Functor C C))
  (c : τ (Obj C))
  (n : τ Nat_grpd)
  : τ (Obj C)
≔ @nat_elim
    (λ _ : τ Nat_grpd, Obj C)
    c
    (λ _ : τ Nat_grpd,
      λ x : τ (Obj C),
        @fapp0 C C S x)
    n;

symbol probe_iter_power_function_internal
  [C : Cat]
  (S : τ (Functor C C))
  (c : τ (Obj C))
  : τ (@Function_grpd Nat_grpd (Obj C))
≔ λ n : τ Nat_grpd,
    @probe_iter_power_internal C S c n;

symbol probe_iter_left_function_internal
  [C : Cat]
  (S : τ (Functor C C))
  (c : τ (Obj C))
  : τ (@Function_grpd Nat_grpd (Obj C))
≔ @grpd_comp_function
    Nat_grpd (Obj C) (Obj C)
    (@probe_functor_object_function C C S)
    (@probe_iter_power_function_internal C S c);

symbol probe_iter_right_function_internal
  [C : Cat]
  (S : τ (Functor C C))
  (c : τ (Obj C))
  : τ (@Function_grpd Nat_grpd (Obj C))
≔ @grpd_comp_function
    Nat_grpd Nat_grpd (Obj C)
    (@probe_iter_power_function_internal C S c)
    probe_nat_succ_function_internal;

// Ordinary internal function equality supplied by the Nat successor beta.
symbol probe_iter_step_path_internal
  [C : Cat]
  (S : τ (Functor C C))
  (c : τ (Obj C))
  : τ (@=
      (@Function_grpd Nat_grpd (Obj C))
      (@probe_iter_left_function_internal C S c)
      (@probe_iter_right_function_internal C S c))
≔ @PiFunext
    Nat_grpd
    (λ _ : τ Nat_grpd, Obj C)
    (@probe_iter_left_function_internal C S c)
    (@probe_iter_right_function_internal C S c)
    (λ n : τ Nat_grpd,
      @eq_refl
        (Obj C)
        (@fapp0 C C S (@probe_iter_power_internal C S c n)));

symbol probe_iter_power_func_internal
  [C : Cat]
  (S : τ (Functor C C))
  (c : τ (Obj C))
  : τ (Functor (Path_cat Nat_grpd) C)
≔ @fapp0
    (Path_cat (@Function_grpd Nat_grpd (Obj C)))
    (Functor_cat (Path_cat Nat_grpd) C)
    (@probe_path_lift_internal Nat_grpd C)
    (@probe_iter_power_function_internal C S c);

// The transparent lift retains the expected object computation.
assert
  [C : Cat]
  (S : τ (Functor C C))
  (c : τ (Obj C))
  (n : τ Nat_grpd)
  ⊢ @fapp0
      (Path_cat Nat_grpd) C
      (@probe_iter_power_func_internal C S c)
      n
    ≡ @probe_iter_power_internal C S c n;

assert
  [C : Cat]
  (S : τ (Functor C C))
  (c : τ (Obj C))
  (n : τ Nat_grpd)
  ⊢ @fapp0
      (Path_cat Nat_grpd) C
      (@comp_cat_fapp0
        (Path_cat Nat_grpd) C C
        S
        (@probe_iter_power_func_internal C S c))
      n
    ≡ @fapp0 C C S (@probe_iter_power_internal C S c n);

assert
  [C : Cat]
  (S : τ (Functor C C))
  (c : τ (Obj C))
  (n : τ Nat_grpd)
  ⊢ @fapp0
      (Path_cat Nat_grpd) C
      (@comp_cat_fapp0
        (Path_cat Nat_grpd) (Path_cat Nat_grpd) C
        (@probe_iter_power_func_internal C S c)
        probe_nat_succ_func_internal)
      n
    ≡ @fapp0 C C S (@probe_iter_power_internal C S c n);

// Applying the internal lift functor to the internal function equality gives
// the structured spiral; its endpoint comparison is handled by ordinary
// Path_int functoriality plus the Core-inclusion proof-time equation above.
symbol probe_iter_exact_spiral_internal
  [C : Cat]
  (S : τ (Functor C C))
  (c : τ (Obj C))
  : τ (Transf
      (@comp_cat_fapp0
        (Path_cat Nat_grpd) C C
        S
        (@probe_iter_power_func_internal C S c))
      (@comp_cat_fapp0
        (Path_cat Nat_grpd) (Path_cat Nat_grpd) C
        (@probe_iter_power_func_internal C S c)
        probe_nat_succ_func_internal))
≔ @fapp1_fapp0
    (Path_cat (@Function_grpd Nat_grpd (Obj C)))
    (Functor_cat (Path_cat Nat_grpd) C)
    (@probe_path_lift_internal Nat_grpd C)
    (@probe_iter_left_function_internal C S c)
    (@probe_iter_right_function_internal C S c)
    (@probe_iter_step_path_internal C S c);

assert
  [C : Cat]
  (S : τ (Functor C C))
  (c : τ (Obj C))
  ⊢ @probe_iter_exact_spiral_internal C S c
    : τ (Transf
        (@comp_cat_fapp0
          (Path_cat Nat_grpd) C C
          S
          (@probe_iter_power_func_internal C S c))
        (@comp_cat_fapp0
          (Path_cat Nat_grpd) (Path_cat Nat_grpd) C
          (@probe_iter_power_func_internal C S c)
          probe_nat_succ_func_internal));

// The recursive successor path is reflexive, so every spiral component
// computes to the categorical identity.
assert
  [C : Cat]
  (S : τ (Functor C C))
  (c : τ (Obj C))
  (n : τ Nat_grpd)
  ⊢ @tapp0_fapp0
      (Path_cat Nat_grpd)
      C
      (@comp_cat_fapp0
        (Path_cat Nat_grpd) C C
        S
        (@probe_iter_power_func_internal C S c))
      (@comp_cat_fapp0
        (Path_cat Nat_grpd) (Path_cat Nat_grpd) C
        (@probe_iter_power_func_internal C S c)
        probe_nat_succ_func_internal)
      n
      (@probe_iter_exact_spiral_internal C S c)
    ≡ @id C
        (@fapp0 C C S
          (@probe_iter_power_internal C S c n));

// Its off-diagonal action remains a full functor and can be iterated further.
assert
  [C : Cat]
  (S : τ (Functor C C))
  (c : τ (Obj C))
  (n m : τ Nat_grpd)
  ⊢ @tapp1_func
      (Path_cat Nat_grpd)
      C
      (@comp_cat_fapp0
        (Path_cat Nat_grpd) C C
        S
        (@probe_iter_power_func_internal C S c))
      (@comp_cat_fapp0
        (Path_cat Nat_grpd) (Path_cat Nat_grpd) C
        (@probe_iter_power_func_internal C S c)
        probe_nat_succ_func_internal)
      n m
      (@probe_iter_exact_spiral_internal C S c)
    : τ (Functor
        (Path_cat (@= Nat_grpd n m))
        (Hom_cat C
          (@fapp0 C C S
            (@probe_iter_power_internal C S c n))
          (@probe_iter_power_internal C S c (succ m))));

assert
  [A B : Grpd]
  (f : τ (@Function_grpd A B))
  ⊢ @probe_path_map_internal A B f
    : τ (Functor (Path_cat A) (Path_cat B));

assert
  [A B : Grpd]
  (f g : τ (@Function_grpd A B))
  (h : τ (@= (@Function_grpd A B) f g))
  ⊢ @probe_path_transf_internal A B f g h
    : τ (Transf
        (@probe_path_map_internal A B f)
        (@probe_path_map_internal A B g));

assert
  [A B : Grpd]
  (f g : τ (@Function_grpd A B))
  (h : τ (@= (@Function_grpd A B) f g))
  (x : τ A)
  ⊢ @tapp0_fapp0
      (Path_cat A) (Path_cat B)
      (@probe_path_map_internal A B f)
      (@probe_path_map_internal A B g)
      x
      (@probe_path_transf_internal A B f g h)
    ≡ @PiHapply A (λ _ : τ A, B) f g h x;

assert
  [A B : Grpd]
  (f g : τ (@Function_grpd A B))
  (h : τ (@= (@Function_grpd A B) f g))
  (x y : τ A)
  (p : τ (@= A x y))
  ⊢ @tapp1_fapp0
      (Path_cat A) (Path_cat B)
      (@probe_path_map_internal A B f)
      (@probe_path_map_internal A B g)
      x y
      (@probe_path_transf_internal A B f g h)
      p
    ≡ @probe_path_transf_cell_internal A B f g h x y p;

assert
  [A B : Grpd]
  (f g : τ (@Function_grpd A B))
  (h : τ (@= (@Function_grpd A B) f g))
  (x y : τ A)
  ⊢ @tapp1_func
      (Path_cat A) (Path_cat B)
      (@probe_path_map_internal A B f)
      (@probe_path_map_internal A B g)
      x y
      (@probe_path_transf_internal A B f g h)
    : τ (Functor
        (Path_cat (@= A x y))
        (Path_cat (@= B (f x) (g y))));

