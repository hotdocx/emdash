/*
  Focused reviewer for the augmented semi-simplex category.

  Category formation, locally discrete Homs, identity, and visible-point
  composition use the promoted face-code substrate. The three literal
  dimension-two coface relations compute through category composition.
  Generic functor/transfor action remains untouched.
*/

require open emdash.emdash3_2_semisimplicial_index;

assert ⊢
  Obj SemiDeltaPlus_cat
  ≡ Nat_grpd;

assert (p n : τ Nat_grpd) ⊢
  Hom_cat SemiDeltaPlus_cat p n
  ≡ Path_cat (@FaceCode p n);

assert (n : τ Nat_grpd) ⊢
  @id SemiDeltaPlus_cat n
  ≡ @face_identity n;

// Both reduction orders meet at the existing public composition owner.
assert
  (p q n : τ Nat_grpd)
  (g : τ (@RawFaceCode q n))
  (f : τ (@RawFaceCode p q)) ⊢
  @comp_fapp0
    SemiDeltaPlus_cat p q n
    (@trunc_intro trunc_zero (@RawFaceCode q n) g)
    (@trunc_intro trunc_zero (@RawFaceCode p q) f)
  ≡ @face_comp
      p q n
      (@trunc_intro trunc_zero (@RawFaceCode q n) g)
      (@trunc_intro trunc_zero (@RawFaceCode p q) f);

assert (p n : τ Nat_grpd) ⊢
  @semi_delta_plus_hom_is_discrete p n
  : τ (IsDiscreteCat (Hom_cat SemiDeltaPlus_cat p n));

// The next Hom is still the generic iterated path category.
assert
  (p n : τ Nat_grpd)
  (f g : τ (@FaceCode p n)) ⊢
  Hom_cat (Hom_cat SemiDeltaPlus_cat p n) f g
  ≡ Path_cat (@= (@FaceCode p n) f g);

// The two vertices of the directed edge.
symbol semi_delta_vertex_zero
  : τ (Hom SemiDeltaPlus_cat (succ zero) (succ (succ zero)))
≔ @face_skip
    (succ zero) (succ zero)
    (@face_identity (succ zero));

symbol semi_delta_vertex_one
  : τ (Hom SemiDeltaPlus_cat (succ zero) (succ (succ zero)))
≔ @face_keep
    zero (succ zero)
    (@face_skip zero zero face_nil);

// The three edges of the directed two-simplex.
symbol semi_delta_edge_zero_one
  : τ (Hom SemiDeltaPlus_cat
      (succ (succ zero))
      (succ (succ (succ zero))))
≔ @face_skip
    (succ (succ zero))
    (succ (succ zero))
    (@face_identity (succ (succ zero)));

symbol semi_delta_edge_zero_two
  : τ (Hom SemiDeltaPlus_cat
      (succ (succ zero))
      (succ (succ (succ zero))))
≔ @face_keep
    (succ zero)
    (succ (succ zero))
    semi_delta_vertex_zero;

symbol semi_delta_edge_one_two
  : τ (Hom SemiDeltaPlus_cat
      (succ (succ zero))
      (succ (succ (succ zero))))
≔ @face_keep
    (succ zero)
    (succ (succ zero))
    semi_delta_vertex_one;

// The two routes through edges 01 and 02 select vertex zero.
assert ⊢
  @comp_fapp0
    SemiDeltaPlus_cat
    (succ zero)
    (succ (succ zero))
    (succ (succ (succ zero)))
    semi_delta_edge_zero_one
    semi_delta_vertex_zero
  ≡ @comp_fapp0
      SemiDeltaPlus_cat
      (succ zero)
      (succ (succ zero))
      (succ (succ (succ zero)))
      semi_delta_edge_zero_two
      semi_delta_vertex_zero;

// The routes through edges 01 and 12 select vertex one.
assert ⊢
  @comp_fapp0
    SemiDeltaPlus_cat
    (succ zero)
    (succ (succ zero))
    (succ (succ (succ zero)))
    semi_delta_edge_zero_one
    semi_delta_vertex_one
  ≡ @comp_fapp0
      SemiDeltaPlus_cat
      (succ zero)
      (succ (succ zero))
      (succ (succ (succ zero)))
      semi_delta_edge_one_two
      semi_delta_vertex_zero;

// The routes through edges 02 and 12 select vertex two.
assert ⊢
  @comp_fapp0
    SemiDeltaPlus_cat
    (succ zero)
    (succ (succ zero))
    (succ (succ (succ zero)))
    semi_delta_edge_zero_two
    semi_delta_vertex_one
  ≡ @comp_fapp0
      SemiDeltaPlus_cat
      (succ zero)
      (succ (succ zero))
      (succ (succ (succ zero)))
      semi_delta_edge_one_two
      semi_delta_vertex_one;

// The index category remains directed rather than silently groupoid-complete.
assertnot ⊢
  semi_delta_vertex_zero
  : τ (Hom SemiDeltaPlus_cat (succ (succ zero)) (succ zero));
