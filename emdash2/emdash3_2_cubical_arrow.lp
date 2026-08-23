/*
  Emdash v3.2: the intrinsic directed cubical arrow category.

  Objects are arrows u:x->y. The Hom between two visible arrow objects is
  the already-checked two-sided square total, so its objects are directed
  lax squares alpha:b o u => v o a with both side arrows variable.

  Whole source and target functors project both arrow objects and square
  arrows. This first module deliberately leaves square identity/composition
  and functorial lifting to focused continuation modules; it adds no filler
  axiom, proof-time unifier, Gray dependency, or triangular-hom dependency.
*/

require open emdash.emdash3_2_cubical_square_total;

injective symbol CubicalArrow_cat
  (C : Cat)
  : Cat;

// Arrow objects decode to (x,(y,u)) with u : Hom_C(x,y).
rule τ (Obj (@CubicalArrow_cat $C))
  ↪ `τΣ_ x : τ (Obj $C),
      @Σ_
        (Obj $C)
        (λ y : τ (Obj $C), Obj (Hom_cat $C x y));

symbol cubical_edge
  [C : Cat]
  (x y : τ (Obj C))
  (u : τ (Hom C x y))
  : τ (Obj (@CubicalArrow_cat C))
≔ Struct_sigma x (Struct_sigma y u);

// The Hom between visible arrows is the full variable-side square total.
rule Hom_cat
      (@CubicalArrow_cat $C)
      (Struct_sigma $x1 (Struct_sigma $x2 $u))
      (Struct_sigma $y1 (Struct_sigma $y2 $v))
  ↪ @homdc_square_cat
      $C $C
      (@hom_int $C $C (@id_func $C))
      $x1 $y1 $x2 $y2 $u $v;

symbol cubical_square
  [C : Cat]
  [x1 y1 x2 y2 : τ (Obj C)]
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (a : τ (Hom C x1 y1))
  (b : τ (Hom C x2 y2))
  (alpha : τ (Obj
    (@homdc_square_fibre C x1 y1 x2 y2 u v a b)))
  : τ (Hom
      (@CubicalArrow_cat C)
      (@cubical_edge C x1 x2 u)
      (@cubical_edge C y1 y2 v))
≔ Struct_sigma a (Struct_sigma b alpha);

injective symbol cubical_src_func
  (C : Cat)
  : τ (Functor (@CubicalArrow_cat C) C);

injective symbol cubical_tgt_func
  (C : Cat)
  : τ (Functor (@CubicalArrow_cat C) C);

rule @fapp0 _ _ (@cubical_src_func _)
      (Struct_sigma $x (Struct_sigma _ _))
  ↪ $x;

rule @fapp0 _ _ (@cubical_tgt_func _)
      (Struct_sigma _ (Struct_sigma $y _))
  ↪ $y;

rule @fapp1_fapp0
      _ $C
      (@cubical_src_func $C)
      (Struct_sigma _ (Struct_sigma _ _))
      (Struct_sigma _ (Struct_sigma _ _))
      (Struct_sigma $a (Struct_sigma _ _))
  ↪ $a;

rule @fapp1_fapp0
      _ $C
      (@cubical_tgt_func $C)
      (Struct_sigma _ (Struct_sigma _ _))
      (Struct_sigma _ (Struct_sigma _ _))
      (Struct_sigma _ (Struct_sigma $b _))
  ↪ $b;
