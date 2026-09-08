/* Whole naturally varying arrow diagrams and their exact observations. */
require open emdash.emdash3_2_arrow_diagram_families;

assert (K C : Cat) (F G : τ (Functor K C)) (eta : τ (@Transf K C F G))
  (x : τ (Obj K))
  ⊢ @fapp0 WalkingArrow_cat C
      (@fapp0 K (Functor_cat WalkingArrow_cat C)
        (@transf_arrow_diagram_func K C F G eta) x) walking_arrow_src
    ≡ @fapp0 K C F x;

assert (K C : Cat) (F G : τ (Functor K C)) (eta : τ (@Transf K C F G))
  (x : τ (Obj K))
  ⊢ @fapp0 WalkingArrow_cat C
      (@fapp0 K (Functor_cat WalkingArrow_cat C)
        (@transf_arrow_diagram_func K C F G eta) x) walking_arrow_tgt
    ≡ @fapp0 K C G x;

assert (K C : Cat) (F G : τ (Functor K C)) (eta : τ (@Transf K C F G))
  (x : τ (Obj K))
  ⊢ @fapp1_fapp0 WalkingArrow_cat C
      (@fapp0 K (Functor_cat WalkingArrow_cat C)
        (@transf_arrow_diagram_func K C F G eta) x)
      walking_arrow_src walking_arrow_tgt walking_arrow_generator
    ≡ @tapp0_fapp0 K C F G x eta;

// Actual transformation action on a nonidentity base arrow.
assert (K C : Cat) (F G : τ (Functor K C)) (eta : τ (@Transf K C F G))
  (x y : τ (Obj K)) (p : τ (Hom K x y))
  ⊢ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_src
      (@fapp1_fapp0 K (Functor_cat WalkingArrow_cat C)
        (@transf_arrow_diagram_func K C F G eta) x y p)
    ≡ @fapp1_fapp0 K C F x y p;

assert (K C : Cat) (F G : τ (Functor K C)) (eta : τ (@Transf K C F G))
  (x y : τ (Obj K)) (p : τ (Hom K x y))
  ⊢ @tapp0_fapp0 WalkingArrow_cat C _ _ walking_arrow_tgt
      (@fapp1_fapp0 K (Functor_cat WalkingArrow_cat C)
        (@transf_arrow_diagram_func K C F G eta) x y p)
    ≡ @fapp1_fapp0 K C G x y p;

assert (K C : Cat) (F G : τ (Functor K C)) (eta : τ (@Transf K C F G))
  (x y : τ (Obj K)) (p : τ (Hom K x y))
  ⊢ @tapp1_fapp0 WalkingArrow_cat C _ _ walking_arrow_src walking_arrow_tgt
      (@fapp1_fapp0 K (Functor_cat WalkingArrow_cat C)
        (@transf_arrow_diagram_func K C F G eta) x y p)
      walking_arrow_generator
    ≡ @tapp1_fapp0 K C F G x y eta p;

// Whole functoriality, before observing the two components.
assert (K C : Cat) (F G : τ (Functor K C)) (eta : τ (@Transf K C F G))
  (x : τ (Obj K))
  ⊢ @fapp1_fapp0 K (Functor_cat WalkingArrow_cat C)
      (@transf_arrow_diagram_func K C F G eta) x x (@id K x)
    ≡ @id (Functor_cat WalkingArrow_cat C)
      (@fapp0 K (Functor_cat WalkingArrow_cat C)
        (@transf_arrow_diagram_func K C F G eta) x);

assert (K C : Cat) (F G : τ (Functor K C)) (eta : τ (@Transf K C F G))
  (x y z : τ (Obj K)) (p : τ (Hom K x y)) (q : τ (Hom K y z))
  ⊢ @comp_fapp0 (Functor_cat WalkingArrow_cat C) _ _ _
      (@fapp1_fapp0 K (Functor_cat WalkingArrow_cat C)
        (@transf_arrow_diagram_func K C F G eta) y z q)
      (@fapp1_fapp0 K (Functor_cat WalkingArrow_cat C)
        (@transf_arrow_diagram_func K C F G eta) x y p)
    ≡ @fapp1_fapp0 K (Functor_cat WalkingArrow_cat C)
      (@transf_arrow_diagram_func K C F G eta) x z (@comp_fapp0 K x y z q p);

assert (K C : Cat) (F G : τ (Functor K C)) (eta : τ (@Transf K C F G))
  ⊢ @diagram_family_at_func K WalkingArrow_cat C
      (@transf_arrow_diagram_func K C F G eta) walking_arrow_src ≡ F;

assert (K C : Cat) (F G : τ (Functor K C)) (eta : τ (@Transf K C F G))
  ⊢ @diagram_family_at_func K WalkingArrow_cat C
      (@transf_arrow_diagram_func K C F G eta) walking_arrow_tgt ≡ G;

assert (K C : Cat) (F G : τ (Functor K C)) (eta : τ (@Transf K C F G))
  ⊢ @diagram_family_transf K WalkingArrow_cat C
      (@transf_arrow_diagram_func K C F G eta)
      walking_arrow_src walking_arrow_tgt walking_arrow_generator ≡ eta;

// Whole observations retain their original Hom actions, not capped maps.
assert (K C : Cat) (F G : τ (Functor K C)) (eta : τ (@Transf K C F G))
  (x y : τ (Obj K))
  ⊢ @fapp1_func K C
      (@diagram_family_at_func K WalkingArrow_cat C
        (@transf_arrow_diagram_func K C F G eta) walking_arrow_src) x y
    ≡ @fapp1_func K C F x y;

assert (K C : Cat) (F G : τ (Functor K C)) (eta : τ (@Transf K C F G))
  (x y : τ (Obj K))
  ⊢ @tapp1_func K C F G x y
      (@diagram_family_transf K WalkingArrow_cat C
        (@transf_arrow_diagram_func K C F G eta)
        walking_arrow_src walking_arrow_tgt walking_arrow_generator)
    ≡ @tapp1_func K C F G x y eta;

assert (K C : Cat) (F G : τ (Functor K C)) (eta : τ (@Transf K C F G))
  (x y : τ (Obj K)) (p q : τ (Hom K x y))
  ⊢ @fapp1_func (Hom_cat K x y)
      (Hom_cat C (@fapp0 K C F x) (@fapp0 K C G y))
      (@tapp1_func K C F G x y
        (@diagram_family_transf K WalkingArrow_cat C
          (@transf_arrow_diagram_func K C F G eta)
          walking_arrow_src walking_arrow_tgt walking_arrow_generator)) p q
    ≡ @fapp1_func (Hom_cat K x y)
      (Hom_cat C (@fapp0 K C F x) (@fapp0 K C G y))
      (@tapp1_func K C F G x y eta) p q;

// Noncollapse at the whole transformation, not merely one component.
assertnot (K C : Cat) (F G : τ (Functor K C))
  (eta other : τ (@Transf K C F G))
  ⊢ @diagram_family_transf K WalkingArrow_cat C
      (@transf_arrow_diagram_func K C F G eta)
      walking_arrow_src walking_arrow_tgt walking_arrow_generator ≡ other;
