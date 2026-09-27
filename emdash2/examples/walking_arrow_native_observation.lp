/* Ordinary native observation retains actual diagram data and whole action.
   The constructor round trip is not a whole representation theorem. */
require open emdash.emdash3_2_walking_arrow_native_observation;
require open emdash.emdash3_2_one_cat_arrow_diagrams;

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) (d : τ (Functor WalkingArrow_cat C)) ⊢
  @fapp0 (Functor_cat WalkingArrow_cat C) (@LaxArrow_cat C) (@diagram_native_arrow_func C C1) d
  ≡ @lax_edge C (@fapp0 WalkingArrow_cat C d walking_arrow_src)
    (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
    (@diagram_native_arrow_value C C1 d);

// The existing scoped comparison recovers the same raw generator at proof time.
assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) (d : τ (Functor WalkingArrow_cat C)) ⊢
  @eq_refl (Obj (@LaxArrow_cat C))
    (@fapp0 (Functor_cat WalkingArrow_cat C) (@LaxArrow_cat C) (@diagram_native_arrow_func C C1) d)
  : τ (@= (Obj (@LaxArrow_cat C))
      (@fapp0 (Functor_cat WalkingArrow_cat C) (@LaxArrow_cat C) (@diagram_native_arrow_func C C1) d)
      (@lax_edge C (@fapp0 WalkingArrow_cat C d walking_arrow_src)
    (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
    (@fapp1_fapp0 WalkingArrow_cat C d walking_arrow_src walking_arrow_tgt walking_arrow_generator)));

// Both sides of the actual nonidentity diagram transformation are retained.
assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) (d e : τ (Functor WalkingArrow_cat C))
  (h : τ (@Transf WalkingArrow_cat C d e)) ⊢
  sigma_Fst (@fapp1_fapp0 (Functor_cat WalkingArrow_cat C) (@LaxArrow_cat C)
    (@diagram_native_arrow_func C C1) d e h)
  ≡ @tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_src h;

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) (d e : τ (Functor WalkingArrow_cat C))
  (h : τ (@Transf WalkingArrow_cat C d e)) ⊢
  sigma_Fst (sigma_Snd (@fapp1_fapp0 (Functor_cat WalkingArrow_cat C) (@LaxArrow_cat C)
    (@diagram_native_arrow_func C C1) d e h))
  ≡ @tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_tgt h;

// The whole next Hom is still the action of the same native functor.
type λ C : Cat, λ C1 : τ (IsNCat (cat_succ cat_zero) C), λ d : τ (Functor WalkingArrow_cat C), λ e : τ (Functor WalkingArrow_cat C),
  λ h : τ (@Transf WalkingArrow_cat C d e), λ k : τ (@Transf WalkingArrow_cat C d e),
  @fapp1_func _ _ (@fapp1_func (Functor_cat WalkingArrow_cat C) (@LaxArrow_cat C)
    (@diagram_native_arrow_func C C1) d e) h k;

// E(D(edge)) retains the original constructor-visible object at proof time.
assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [x y : τ (Obj C)] (f : τ (Hom C x y)) ⊢
  @eq_refl (Obj (@LaxArrow_cat C))
    (@fapp0 (Functor_cat WalkingArrow_cat C) (@LaxArrow_cat C) (@diagram_native_arrow_func C C1)
    (@fapp0 (@LaxArrow_cat C) (Functor_cat WalkingArrow_cat C)
      (@one_cat_arrow_diagram_func C C1) (@lax_edge C x y f)))
  : τ (@= (Obj (@LaxArrow_cat C))
    (@fapp0 (Functor_cat WalkingArrow_cat C) (@LaxArrow_cat C) (@diagram_native_arrow_func C C1)
    (@fapp0 (@LaxArrow_cat C) (Functor_cat WalkingArrow_cat C)
      (@one_cat_arrow_diagram_func C C1) (@lax_edge C x y f)))
    (@lax_edge C x y f));

// Ambient raw-generator agreement is not an additional runtime erasure.
assertnot [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) (d : τ (Functor WalkingArrow_cat C)) ⊢
  @fapp0 (Functor_cat WalkingArrow_cat C) (@LaxArrow_cat C) (@diagram_native_arrow_func C C1) d
  ≡ @lax_edge C (@fapp0 WalkingArrow_cat C d walking_arrow_src)
    (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
    (@fapp1_fapp0 WalkingArrow_cat C d walking_arrow_src walking_arrow_tgt walking_arrow_generator);


// The admitted profile also stays visible in the constructor round trip.
assertnot [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [x y : τ (Obj C)] (f : τ (Hom C x y)) ⊢
  @fapp0 (Functor_cat WalkingArrow_cat C) (@LaxArrow_cat C) (@diagram_native_arrow_func C C1)
    (@fapp0 (@LaxArrow_cat C) (Functor_cat WalkingArrow_cat C)
      (@one_cat_arrow_diagram_func C C1) (@lax_edge C x y f))
  ≡ @lax_edge C x y f;
