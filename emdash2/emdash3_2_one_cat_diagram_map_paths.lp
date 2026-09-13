/* Derived ordinary diagram-map equality through native square paths.
   The reconstruction law is the explicit shape-universality primitive;
   this module adds only its derived ordinary consequence. */
require open emdash.emdash3_2_one_cat_native_square_paths;
require open emdash.emdash3_2_one_cat_diagram_reconstruction;

// Equal endpoint components determine an ordinary diagram transformation.
// Native square equality is reflected through the whole reconstruction law.
symbol one_cat_diagram_map_path [C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [d e : τ (Functor WalkingArrow_cat C)] (h k : τ (@Transf WalkingArrow_cat C d e))
  (p : τ (@= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C e walking_arrow_src)) (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_src h) (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_src k)))
  (q : τ (@= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0 WalkingArrow_cat C e walking_arrow_tgt)) (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_tgt h) (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_tgt k)))
  : τ (@= (@Transf WalkingArrow_cat C d e) h k)
≔ @one_cat_diagram_observation_reflect_path C C1 d e h k
    (@one_cat_native_square_path C C1 (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C e walking_arrow_src)
      (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0 WalkingArrow_cat C e walking_arrow_tgt) (@fapp1_fapp0 WalkingArrow_cat C d walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@fapp1_fapp0 WalkingArrow_cat C e walking_arrow_src walking_arrow_tgt walking_arrow_generator)
      (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_src h) (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_src k) (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_tgt h) (@tapp0_fapp0 WalkingArrow_cat C d e walking_arrow_tgt k)
      (sigma_Snd (sigma_Snd (@fapp1_fapp0 (Functor_cat WalkingArrow_cat C) (@LaxArrow_cat C) (@diagram_native_arrow_func C) d e h)))
      (sigma_Snd (sigma_Snd (@fapp1_fapp0 (Functor_cat WalkingArrow_cat C) (@LaxArrow_cat C) (@diagram_native_arrow_func C) d e k))) p q);
