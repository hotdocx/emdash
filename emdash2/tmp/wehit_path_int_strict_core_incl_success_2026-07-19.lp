/*
  Minimal internal Path_int action probe.

  The public construction uses only iterated ordinary functor action:

    Path_map(f)       := Path_int_1(f)
    Path_transf(h)    := (Path_int_1)_1(h).

  No external family of transfor components and no hand-written naturality
  square occurs in the interface.
*/

require open emdash.emdash3_2;

// Retain the kernel's categorical `comp_Grpd` presentation.  This probe does
// not promote the broad experimental fold to `grpd_comp_function`.

// Capped evaluation of categorical function composition.  The whole
// `comp_Grpd` term remains the runtime normal form; only its application to an
// element computes pointwise.
rule @comp_fapp0 Grpd_cat $A $B $C $g $f $x
  ↪ $g ($f $x);

assert
  [A B C : Grpd]
  (g : τ (@Function_grpd B C))
  (f : τ (@Function_grpd A B))
  (x : τ A)
  ⊢ @comp_fapp0 Grpd_cat A B C g f x ≡ g (f x);

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

// Generic strict functoriality already owns
//   PathMap(g) ∘ PathMap(f) ↪ PathMap(comp_Grpd(g,f)).
// Keep that categorical composition normal form throughout this probe.

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
        _ (Functor_cat (Path_cat $A) (Path_cat $B))
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
  Strict Core-inclusion naturality along a fixed ordinary functor:

    F ∘ CoreIncl(C) ↪ CoreIncl(D) ∘ PathMap(F₀).

  The object function is transparent.  No rigid eta surrogate or endpoint
  unification rule is introduced.
*/
symbol probe_functor_object_function
  [C D : Cat]
  (F : τ (Functor C D))
  : τ (@Function_grpd (Obj C) (Obj D))
≔ λ x : τ (Obj C), @fapp0 C D F x;

// Selected runtime normal form for fixed-functor Core-inclusion naturality.
rule @comp_fapp0
    Cat_cat
    _ $C $D
    $F
    (Core_incl_func $C)
  ↪ @comp_fapp0
    Cat_cat
    (Path_cat (Obj $C)) (Path_cat (Obj $D)) $D
    (Core_incl_func $D)
    (@fapp1_fapp0
      Grpd_cat Cat_cat probe_path_int_internal
      (Obj $C) (Obj $D)
      (@probe_functor_object_function $C $D $F));

// Both sides now compute to the selected strict normal form.
assert
  [C D : Cat]
  (F : τ (Functor C D))
  ⊢ @comp_cat_fapp0
      (Core_cat C) C D
      F
      (Core_incl_func C)
    ≡ @comp_cat_fapp0
        (Core_cat C) (Core_cat D) D
        (Core_incl_func D)
        (@fapp1_fapp0
          Grpd_cat Cat_cat probe_path_int_internal
          (Obj C) (Obj D)
          (@probe_functor_object_function C D F));

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

// Generic object projection for Cat-valued postcomposition:
// `hom_postcomp_E(p,G)[w] ↪ E[p](G[w])`.
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

assert
  [B W : Cat]
  (E : τ (Functor B Cat_cat))
  (X Y : τ (Obj B))
  (p : τ (Hom B X Y))
  (G : τ (Functor W (@fapp0 B Cat_cat E X)))
  (w : τ (Obj W))
  ⊢ @fapp0
      W (@fapp0 B Cat_cat E Y)
      (@hom_postcomp_fapp0
        Cat_cat B E W X Y p G)
      w
    ≡ @fapp0
        (@fapp0 B Cat_cat E X)
        (@fapp0 B Cat_cat E Y)
        (@fapp1_fapp0 B Cat_cat E X Y p)
        (@fapp0 W (@fapp0 B Cat_cat E X) G w);

/*
  Stable consumer of strict Core-inclusion naturality.

  The inner functor is retained under the established Cat-valued
  postcomposition owner.  Generic PathInt functoriality subsequently folds
  `PathMap(F₀) ∘ PathMap(f)` to `PathMap(comp_Grpd(F₀,f))`.
*/
rule @comp_fapp0
      Cat_cat
      _ $C $D
      $F
      (@hom_postcomp_fapp0
        Cat_cat Cat_cat (@id Cat_cat Cat_cat)
        (Path_cat $A) (Path_cat (Obj $C)) $C
        (Core_incl_func $C)
        $G)
  ↪ @hom_postcomp_fapp0
      Cat_cat Cat_cat (@id Cat_cat Cat_cat)
      (Path_cat $A) (Path_cat (Obj $D)) $D
      (Core_incl_func $D)
      (@comp_fapp0
        Cat_cat
        (Path_cat $A) (Path_cat (Obj $C)) (Path_cat (Obj $D))
        (@fapp1_fapp0
          Grpd_cat Cat_cat probe_path_int_internal
          (Obj $C) (Obj $D)
          (@probe_functor_object_function $C $D $F))
        $G);

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
        (@comp_fapp0
          Grpd_cat A (Obj C) (Obj D)
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
        (@comp_fapp0 Grpd_cat A B (Obj C) f g)))
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
≔ @comp_fapp0
    Grpd_cat Nat_grpd (Obj C) (Obj C)
    (@probe_functor_object_function C C S)
    (@probe_iter_power_function_internal C S c);

symbol probe_iter_right_function_internal
  [C : Cat]
  (S : τ (Functor C C))
  (c : τ (Obj C))
  : τ (@Function_grpd Nat_grpd (Obj C))
≔ @comp_fapp0
    Grpd_cat Nat_grpd Nat_grpd (Obj C)
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

// PathLift's full off-diagonal action computes to Core inclusion applied to
// the internally generated Path_int action; no opaque higher action remains.
assert
  [A : Grpd]
  [C : Cat]
  (f g : τ (@Function_grpd A (Obj C)))
  (h : τ (@= (@Function_grpd A (Obj C)) f g))
  (x y : τ A)
  ⊢ @tapp1_func
      (Path_cat A) C
      (@fapp0
        (Path_cat (@Function_grpd A (Obj C)))
        (Functor_cat (Path_cat A) C)
        (@probe_path_lift_internal A C)
        f)
      (@fapp0
        (Path_cat (@Function_grpd A (Obj C)))
        (Functor_cat (Path_cat A) C)
        (@probe_path_lift_internal A C)
        g)
      x y
      (@fapp1_fapp0
        (Path_cat (@Function_grpd A (Obj C)))
        (Functor_cat (Path_cat A) C)
        (@probe_path_lift_internal A C)
        f g h)
    ≡ @comp_cat_fapp0
        (Path_cat (@= A x y))
        (Path_cat (@= (Obj C) (f x) (g y)))
        (Hom_cat C (f x) (g y))
        (@fapp1_func
          (Path_cat (Obj C)) C
          (Core_incl_func C)
          (f x) (g y))
        (@fapp1_fapp0
          Grpd_cat Cat_cat probe_path_int_internal
          (@= A x y)
          (@= (Obj C) (f x) (g y))
          (λ p : τ (@= A x y),
            @probe_path_transf_cell_internal
              A (Obj C) f g h x y p));

// Capping the full action at p computes to the corresponding directed arrow.
assert
  [A : Grpd]
  [C : Cat]
  (f g : τ (@Function_grpd A (Obj C)))
  (h : τ (@= (@Function_grpd A (Obj C)) f g))
  (x y : τ A)
  (p : τ (@= A x y))
  ⊢ @tapp1_fapp0
      (Path_cat A) C
      (@fapp0
        (Path_cat (@Function_grpd A (Obj C)))
        (Functor_cat (Path_cat A) C)
        (@probe_path_lift_internal A C)
        f)
      (@fapp0
        (Path_cat (@Function_grpd A (Obj C)))
        (Functor_cat (Path_cat A) C)
        (@probe_path_lift_internal A C)
        g)
      x y
      (@fapp1_fapp0
        (Path_cat (@Function_grpd A (Obj C)))
        (Functor_cat (Path_cat A) C)
        (@probe_path_lift_internal A C)
        f g h)
      p
    ≡ @path_to_hom
        C (f x) (g y)
        (@probe_path_transf_cell_internal
          A (Obj C) f g h x y p);
