/* Whole reconstruction, computing endpoints, and derived map reflection. */
require open emdash.emdash3_2_one_cat_diagram_reconstruction;

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (d : τ (Functor WalkingArrow_cat C)) ⊢
  @tapp0_fapp0 WalkingArrow_cat C
    (@fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@one_cat_diagram_roundtrip_func C C1) d) (@fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@id_func (Functor_cat WalkingArrow_cat C)) d) walking_arrow_src
    (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@one_cat_diagram_roundtrip_func C C1) (@id_func (Functor_cat WalkingArrow_cat C)) d
      (@defiso_to (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_roundtrip_func C C1) (@id_func (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_reconstruction_iso C C1)))
  ≡ @id C (@fapp0 WalkingArrow_cat C d walking_arrow_src);

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (d : τ (Functor WalkingArrow_cat C)) ⊢
  @tapp0_fapp0 WalkingArrow_cat C
    (@fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@one_cat_diagram_roundtrip_func C C1) d) (@fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@id_func (Functor_cat WalkingArrow_cat C)) d) walking_arrow_tgt
    (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@one_cat_diagram_roundtrip_func C C1) (@id_func (Functor_cat WalkingArrow_cat C)) d
      (@defiso_to (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_roundtrip_func C C1) (@id_func (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_reconstruction_iso C C1)))
  ≡ @id C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt);

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (d : τ (Functor WalkingArrow_cat C)) ⊢
  @tapp0_fapp0 WalkingArrow_cat C
    (@fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@id_func (Functor_cat WalkingArrow_cat C)) d) (@fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@one_cat_diagram_roundtrip_func C C1) d) walking_arrow_src
    (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@id_func (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_roundtrip_func C C1) d
      (@defiso_from (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_roundtrip_func C C1) (@id_func (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_reconstruction_iso C C1)))
  ≡ @id C (@fapp0 WalkingArrow_cat C d walking_arrow_src);

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (d : τ (Functor WalkingArrow_cat C)) ⊢
  @tapp0_fapp0 WalkingArrow_cat C
    (@fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@id_func (Functor_cat WalkingArrow_cat C)) d) (@fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@one_cat_diagram_roundtrip_func C C1) d) walking_arrow_tgt
    (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@id_func (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_roundtrip_func C C1) d
      (@defiso_from (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_roundtrip_func C C1) (@id_func (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_reconstruction_iso C C1)))
  ≡ @id C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt);

// The whole natural comparison retains its computational inverse.
assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) ⊢
  @comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_roundtrip_func C C1) (@id_func (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_roundtrip_func C C1)
    (@defiso_from (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_roundtrip_func C C1) (@id_func (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_reconstruction_iso C C1)) (@defiso_to (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_roundtrip_func C C1) (@id_func (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_reconstruction_iso C C1))
  ≡ @id (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_roundtrip_func C C1);

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) ⊢
  @comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@id_func (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_roundtrip_func C C1) (@id_func (Functor_cat WalkingArrow_cat C))
    (@defiso_to (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_roundtrip_func C C1) (@id_func (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_reconstruction_iso C C1)) (@defiso_from (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_roundtrip_func C C1) (@id_func (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_reconstruction_iso C C1))
  ≡ @id (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@id_func (Functor_cat WalkingArrow_cat C));

// Reflection applies to arbitrary original diagram maps.
assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [d e : τ (Functor WalkingArrow_cat C)] (h k : τ (@Transf WalkingArrow_cat C d e))
  (p : τ (@= (Hom (@LaxArrow_cat C) (@fapp0 (Functor_cat WalkingArrow_cat C) (@LaxArrow_cat C) (@diagram_native_arrow_func C) d) (@fapp0 (Functor_cat WalkingArrow_cat C) (@LaxArrow_cat C) (@diagram_native_arrow_func C) e)) (@fapp1_fapp0 (Functor_cat WalkingArrow_cat C) (@LaxArrow_cat C) (@diagram_native_arrow_func C) d e h) (@fapp1_fapp0 (Functor_cat WalkingArrow_cat C) (@LaxArrow_cat C) (@diagram_native_arrow_func C) d e k))) ⊢
  @one_cat_diagram_observation_reflect_path C C1 d e h k p
  : τ (@= (@Transf WalkingArrow_cat C d e) h k);

// An arbitrary unrelated map still needs equality of the actual images.
assertnot [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [d e : τ (Functor WalkingArrow_cat C)] (h k : τ (@Transf WalkingArrow_cat C d e)) ⊢
  @one_cat_diagram_observation_reflect_path C C1 d e h k
    (@eq_refl (Hom (@LaxArrow_cat C) (@fapp0 (Functor_cat WalkingArrow_cat C) (@LaxArrow_cat C) (@diagram_native_arrow_func C) d) (@fapp0 (Functor_cat WalkingArrow_cat C) (@LaxArrow_cat C) (@diagram_native_arrow_func C) e)) (@fapp1_fapp0 (Functor_cat WalkingArrow_cat C) (@LaxArrow_cat C) (@diagram_native_arrow_func C) d e h))
  : τ (@= (@Transf WalkingArrow_cat C d e) h k);

// The same whole comparison retains mixed action and a further Hom.
type λ C : Cat, λ C1 : τ (IsNCat (cat_succ cat_zero) C),
  λ d : τ (Functor WalkingArrow_cat C), λ e : τ (Functor WalkingArrow_cat C),
  λ h : τ (@Transf WalkingArrow_cat C d e), λ k : τ (@Transf WalkingArrow_cat C d e),
  @fapp1_func _ _ (@tapp1_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@one_cat_diagram_roundtrip_func C C1) (@id_func (Functor_cat WalkingArrow_cat C)) d e
    (@defiso_to (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_roundtrip_func C C1) (@id_func (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_reconstruction_iso C C1))) h k;
