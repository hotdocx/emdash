/*
  Naturally varying arrows as whole walking-arrow diagrams.

  A transformation eta:F⇒G is an arrow in Functor_cat(K,C). Introduce its
  walking-arrow diagram there, then exchange the shape and parameter axes.
  Source, target and differential whole observations recover F, G and eta;
  the parameter action has components F[p], G[p] and mixed action eta[p].
  No arrow-data square record, new primitive, or equality bridge is added.
*/
require open emdash.emdash3_2_walking_arrow_introduction;
require open emdash.emdash3_2_diagram_evaluation;

// Transparent family introduction from the existing whole transformation.
symbol transf_arrow_diagram_func
  [K C : Cat] [F G : τ (Functor K C)] (eta : τ (@Transf K C F G))
  : τ (Functor K (Functor_cat WalkingArrow_cat C))
≔ @sym_func WalkingArrow_cat K C
    (@walking_arrow_func (Functor_cat K C) F G eta);

// The two Terminal domains are actual walking-arrow shape discriminators.
// All remaining inferred LHS type slots are variables or wildcards.
unif_rule
  @sym_fapp0_func _ $K $C
    (@join_elim_func Terminal_cat Terminal_cat _
      (@Const_func _ _ $F) (@Const_func _ _ $G) (@Const_func _ _ $eta)) $x
  ≡ @join_elim_func $A $B $E
      (@Const_func _ _ $Fx) (@Const_func _ _ $Gx) (@Const_func _ _ $etax)
  ↪ [ $A ≡ Terminal_cat; $B ≡ Terminal_cat; $E ≡ $C;
      $Fx ≡ (@fapp0 $K $C $F $x);
      $Gx ≡ (@fapp0 $K $C $G $x);
      $etax ≡ (@tapp0_fapp0 $K $C $F $G $x $eta) ];

// Proof-time point comparison; neither whole runtime head is folded.
symbol transf_arrow_diagram_point_path
  [K C : Cat] [F G : τ (Functor K C)]
  (eta : τ (@Transf K C F G)) (x : τ (Obj K))
  : τ (@= (Functor WalkingArrow_cat C)
      (@fapp0 K (Functor_cat WalkingArrow_cat C)
        (@transf_arrow_diagram_func K C F G eta) x)
      (@walking_arrow_func C (@fapp0 K C F x) (@fapp0 K C G x)
        (@tapp0_fapp0 K C F G x eta)))
≔ @eq_refl (Functor WalkingArrow_cat C)
    (@fapp0 K (Functor_cat WalkingArrow_cat C)
      (@transf_arrow_diagram_func K C F G eta) x);
