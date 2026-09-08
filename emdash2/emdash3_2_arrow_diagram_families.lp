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
