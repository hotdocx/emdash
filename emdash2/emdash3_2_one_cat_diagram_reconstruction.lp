/* Ordinary walking-arrow reconstruction as a whole natural isomorphism.
   The beta-only Join interface does not yet derive this assembly. The
   declaration below adds the standard ordinary-target shape-universality
   law explicitly, with coherent native DefIso inverse cuts. It compares
   endofunctors by an actual natural isomorphism, not by identifying diagram
   objects or installing a general functor-eta rewrite. Faithfulness below
   is a derived consequence, with no caller-supplied injectivity premise. */
require open emdash.emdash3_2_functor_reconstruction_paths;
require open emdash.emdash3_2_walking_arrow_native_observation;
require open emdash.emdash3_2_one_cat_arrow_diagrams;

// The existing functors, composed without changing their runtime heads.
symbol one_cat_diagram_roundtrip_func
  [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  : τ (Functor (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C))
≔ @comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) (@LaxArrow_cat C)
    (Functor_cat WalkingArrow_cat C)
    (@one_cat_arrow_diagram_func C C1) (@diagram_native_arrow_func C);

/* Ordinary walking-arrow universality: reconstruction is naturally
   isomorphic to the original diagram. This is a new whole assembly law,
   not a theorem extracted from the current beta-only join recursor. */
injective symbol one_cat_diagram_reconstruction_iso
  [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  : τ (@DefIso
      (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C))
      (@one_cat_diagram_roundtrip_func C C1) (@id_func (Functor_cat WalkingArrow_cat C)));

// The two walking-arrow endpoints are genuine shape discriminators.
rule @tapp0_fapp0 _ _ _ _
      (@fapp0 _ _ (@join_fst_func Terminal_cat Terminal_cat) Terminal_obj)
      (@tapp0_fapp0 _ _ _ _ $d
        (@defiso_to _ _ _ (@one_cat_diagram_reconstruction_iso $C _)))
  ↪ @id $C (@fapp0 WalkingArrow_cat $C $d walking_arrow_src);
rule @tapp0_fapp0 _ _ _ _
      (@fapp0 _ _ (@join_snd_func Terminal_cat Terminal_cat) Terminal_obj)
      (@tapp0_fapp0 _ _ _ _ $d
        (@defiso_to _ _ _ (@one_cat_diagram_reconstruction_iso $C _)))
  ↪ @id $C (@fapp0 WalkingArrow_cat $C $d walking_arrow_tgt);
rule @tapp0_fapp0 _ _ _ _
      (@fapp0 _ _ (@join_fst_func Terminal_cat Terminal_cat) Terminal_obj)
      (@tapp0_fapp0 _ _ _ _ $d
        (@defiso_from _ _ _ (@one_cat_diagram_reconstruction_iso $C _)))
  ↪ @id $C (@fapp0 WalkingArrow_cat $C $d walking_arrow_src);
rule @tapp0_fapp0 _ _ _ _
      (@fapp0 _ _ (@join_snd_func Terminal_cat Terminal_cat) Terminal_obj)
      (@tapp0_fapp0 _ _ _ _ $d
        (@defiso_from _ _ _ (@one_cat_diagram_reconstruction_iso $C _)))
  ↪ @id $C (@fapp0 WalkingArrow_cat $C $d walking_arrow_tgt);

// Defined component view at the existing canonical introduction endpoints.
symbol one_cat_diagram_reconstruction_to [C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) (d : τ (Functor WalkingArrow_cat C))
  : τ (@Transf WalkingArrow_cat C (@walking_arrow_func C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp1_fapp0 WalkingArrow_cat C d walking_arrow_src walking_arrow_tgt walking_arrow_generator)) d)
≔ @tapp0_fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@one_cat_diagram_roundtrip_func C C1) (@id_func (Functor_cat WalkingArrow_cat C)) d
    (@defiso_to (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_roundtrip_func C C1) (@id_func (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_reconstruction_iso C C1));

// Defined component view at the existing canonical introduction endpoints.
symbol one_cat_diagram_reconstruction_from [C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) (d : τ (Functor WalkingArrow_cat C))
  : τ (@Transf WalkingArrow_cat C d (@walking_arrow_func C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp1_fapp0 WalkingArrow_cat C d walking_arrow_src walking_arrow_tgt walking_arrow_generator)))
≔ @tapp0_fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@id_func (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_roundtrip_func C C1) d
    (@defiso_from (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_roundtrip_func C C1) (@id_func (Functor_cat WalkingArrow_cat C)) (@one_cat_diagram_reconstruction_iso C C1));

symbol one_cat_diagram_observation_reflect_path [C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [d e : τ (Functor WalkingArrow_cat C)] (h k : τ (@Transf WalkingArrow_cat C d e))
  (p : τ (@= (Hom (@LaxArrow_cat C)
      (@fapp0 (Functor_cat WalkingArrow_cat C) (@LaxArrow_cat C) (@diagram_native_arrow_func C) d)
      (@fapp0 (Functor_cat WalkingArrow_cat C) (@LaxArrow_cat C) (@diagram_native_arrow_func C) e))
    (@fapp1_fapp0 (Functor_cat WalkingArrow_cat C) (@LaxArrow_cat C) (@diagram_native_arrow_func C) d e h)
    (@fapp1_fapp0 (Functor_cat WalkingArrow_cat C) (@LaxArrow_cat C) (@diagram_native_arrow_func C) d e k)))
  : τ (@= (@Transf WalkingArrow_cat C d e) h k)
≔ @functor_reconstruction_along_reflect_path (Functor_cat WalkingArrow_cat C) (@LaxArrow_cat C)
    (@diagram_native_arrow_func C) (@one_cat_arrow_diagram_func C C1)
    (@one_cat_diagram_reconstruction_iso C C1) d e h k p;
