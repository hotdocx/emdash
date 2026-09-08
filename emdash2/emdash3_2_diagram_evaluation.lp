/*
  Whole evaluation in the varying diagram-shape argument.

  Exchange applied to the identity of Functor_cat(I,C) gives i ↦ ev_i.
  Its arrow action is an actual transformation and its mixed action is
  ordinary off-diagonal transfor evaluation. This is a transparent use of
  existing structural owners, not a new category, functor primitive or rule.
*/
require open emdash.emdash3_2;

symbol diagram_evaluation_func
  [I C : Cat]
  : τ (Functor I (Functor_cat (Functor_cat I C) C))
≔ @sym_func (Functor_cat I C) I C (@id_func (Functor_cat I C));

symbol diagram_evaluation_at_func
  [I C : Cat] (i : τ (Obj I))
  : τ (Functor (Functor_cat I C) C)
≔ @fapp0 I (Functor_cat (Functor_cat I C) C)
    (@diagram_evaluation_func I C) i;

symbol diagram_evaluation_transf
  [I C : Cat] [i j : τ (Obj I)] (u : τ (Hom I i j))
  : τ (@Transf (Functor_cat I C) C
      (@diagram_evaluation_at_func I C i) (@diagram_evaluation_at_func I C j))
≔ @fapp1_fapp0 I (Functor_cat (Functor_cat I C) C)
    (@diagram_evaluation_func I C) i j u;

// Whole component functor of a naturally varying diagram D:K→(I→C).
// Exchange retains K as a functorial variable, rather than evaluating D at
// one object and reconstructing its action separately.
symbol diagram_family_at_func
  [K I C : Cat]
  (D : τ (Functor K (Functor_cat I C))) (i : τ (Obj I))
  : τ (Functor K C)
≔ @fapp0 I (Functor_cat K C) (@sym_func K I C D) i;

// A shape arrow induces an actual whole transformation of component functors.
symbol diagram_family_transf
  [K I C : Cat]
  (D : τ (Functor K (Functor_cat I C)))
  [i j : τ (Obj I)] (u : τ (Hom I i j))
  : τ (@Transf K C
      (@diagram_family_at_func K I C D i)
      (@diagram_family_at_func K I C D j))
≔ @fapp1_fapp0 I (Functor_cat K C) (@sym_func K I C D) i j u;
