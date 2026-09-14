/*
  Whole evaluation in the varying diagram-shape argument.

  Exchange applied to the identity of Functor_cat(I,C) gives i ↦ ev_i.
  Its arrow action is an actual transformation and its mixed action is
  ordinary off-diagonal transfor evaluation. Definitions use existing owners;
  the later projection folds and proof-time comparisons retain whole action.
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

// Whole evaluation on families, retaining the family itself as a variable.
// Its action on transformations computes to sym_transf_tapp0_transf.
symbol diagram_family_evaluation_func [K I C : Cat] (i : τ (Obj I))
  : τ (Functor (Functor_cat K (Functor_cat I C)) (Functor_cat K C))
≔ @comp_cat_fapp0 (Functor_cat K (Functor_cat I C))
    (Functor_cat I (Functor_cat K C)) (Functor_cat K C)
    (@fapp0_func I (Functor_cat K C) i) (@sym_func_func K I C);

// Whole component functor of a naturally varying diagram D:K→(I→C).
// Exchange retains K as a functorial variable, rather than evaluating D at
// one object and reconstructing its action separately.
symbol diagram_family_at_func
  [K I C : Cat]
  (D : τ (Functor K (Functor_cat I C))) (i : τ (Obj I))
  : τ (Functor K C)
≔ @fapp0 (Functor_cat K (Functor_cat I C)) (Functor_cat K C)
    (@diagram_family_evaluation_func K I C i) D;

// A shape arrow induces an actual whole transformation of component functors.
symbol diagram_family_transf
  [K I C : Cat]
  (D : τ (Functor K (Functor_cat I C)))
  [i j : τ (Obj I)] (u : τ (Hom I i j))
  : τ (@Transf K C
      (@diagram_family_at_func K I C D i)
      (@diagram_family_at_func K I C D j))
≔ @fapp1_fapp0 I (Functor_cat K C) (@sym_func K I C D) i j u;

// Whole evaluation after precomposition: (D∘F)(−)[i] = D(−)[i]∘F.
// This preserves the whole remaining parameter action.
rule @sym_fapp0_func _ $I $C
      (@comp_fapp0 Cat_cat $A $B _ $D $F) $i
  ↪ @comp_cat_fapp0 $A $B $C (@sym_fapp0_func $B $I $C $D $i) $F;

// Constant diagrams evaluate to an actual constant parameter functor.
// Keep the whole functor as owner, with the original diagram and shape point.
rule @sym_fapp0_func $K $I $C (@Const_func _ _ $D) $i
  ↪ @Const_func $K $C (@fapp0 $I $C $D $i);

// The same evaluation fold after its Hom projection has already occurred.
// A measured preprojected consumer otherwise retains a different whole head.
rule @sym_fapp0_fapp1_func _ $I $C
      (@comp_fapp0 Cat_cat $A $B _ $D $F) $i $x $y
  ↪ @fapp1_func $A $C
      (@comp_cat_fapp0 $A $B $C (@sym_fapp0_func $B $I $C $D $i) $F) $x $y;

// Companion after projection to Hom: reuse the original constant-functor action.
rule @sym_fapp0_fapp1_func $K $I $C (@Const_func _ _ $D) $i $x $y
  ↪ @fapp1_func $K $C (@Const_func $K $C (@fapp0 $I $C $D $i)) $x $y;

// Proof-time whole evaluation comparison; retain both runtime owners.
unif_rule
  @sym_fapp0_func _ $I $C $F $i
  ≡ @comp_fapp0 Cat_cat _ _ _
      (@sym_fapp0_func _ $I1 $C1 (@id Cat_cat _) $i1) $F1
  ↪ [ $I1 ≡ $I; $C1 ≡ $C; $F1 ≡ $F; $i1 ≡ $i ];

// Whole transformation evaluation, after the Cat-specialized postwhiskering
// projection has exposed product composition. The identity second component
// is the genuine postwhiskering discriminator.
unif_rule
  @sym_transf_tapp0_transf _ $I $C $F $G $h $i
  ≡ @comp_prod_fapp1_fapp0 Cat_cat _ _ _
      (@Struct_sigma _ _ $F1
        (@sym_fapp0_func _ $I1 $C1 (@id Cat_cat _) $i1))
      (@Struct_sigma _ _ $G1 _)
      (@Struct_sigma _ _ $h1 (@id _ _))
  ↪ [ $I1 ≡ $I; $C1 ≡ $C; $F1 ≡ $F; $G1 ≡ $G; $h1 ≡ $h; $i1 ≡ $i ];

// Proof-time shape-arrow evaluation through prewhiskering by the same family.
// Compare both factors, their endpoint evaluations, and the original shape arrow.
unif_rule
  @sym_tapp1_fapp0_transf $A $I $C $E $i $j $u
  ≡ @comp_prod_fapp1_fapp0 Cat_cat $A1 $B $C1
      (@Struct_sigma _ _ $F1 $Ei)
      (@Struct_sigma _ _ $F2 $Ej)
      (@Struct_sigma _ _ (@id _ $F3)
        (@sym_tapp1_fapp0_transf $B1 $I1 $C2 $D $i1 $j1 $u1))
  ↪ [ $A1 ≡ $A; $B1 ≡ $B; $I1 ≡ $I; $C1 ≡ $C; $C2 ≡ $C;
      $F2 ≡ $F1; $F3 ≡ $F1; $i1 ≡ $i; $j1 ≡ $j; $u1 ≡ $u;
      $E ≡ (@comp_cat_fapp0 $A $B (Functor_cat $I $C) $D $F1);
      $Ei ≡ (@sym_fapp0_func $B $I $C $D $i);
      $Ej ≡ (@sym_fapp0_func $B $I $C $D $j) ];

// Existing generic composition evidence at the ordinary family target.
symbol one_cat_diagram_family_evaluation_comp_path [B I C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) (i : τ (Obj I))
  (F G H : τ (Functor B (Functor_cat I C)))
  (g : τ (@Transf B (Functor_cat I C) G H))
  (f : τ (@Transf B (Functor_cat I C) F G))
  : τ (@= (@Transf B C (@diagram_family_at_func B I C F i) (@diagram_family_at_func B I C H i))
      (@sym_transf_tapp0_transf B I C F H (@comp_fapp0 (Functor_cat B (Functor_cat I C)) F G H g f) i)
      (@comp_fapp0 (Functor_cat B C)
        (@diagram_family_at_func B I C F i) (@diagram_family_at_func B I C G i) (@diagram_family_at_func B I C H i)
        (@sym_transf_tapp0_transf B I C G H g i) (@sym_transf_tapp0_transf B I C F G f i)))
≔ @fapp1_comp_path (Functor_cat B (Functor_cat I C)) (Functor_cat B C)
    (@diagram_family_evaluation_func B I C i) F G H g f;

// Whole shape-arrow observation in the qualified ordinary target.
symbol one_cat_diagram_family_transf_whisker_path [B I C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (D : τ (Functor B (Functor_cat I C))) [i j : τ (Obj I)] (u : τ (Hom I i j))
  : τ (@= (@Transf B C (@diagram_family_at_func B I C D i) (@diagram_family_at_func B I C D j))
      (@diagram_family_transf B I C D i j u)
      (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat I C) C D
        (@diagram_evaluation_at_func I C i) (@diagram_evaluation_at_func I C j))
        (@diagram_evaluation_transf I C i j u)))
≔ eq_refl (@diagram_family_transf B I C D i j u);

// Whole shape-arrow observation in the qualified ordinary target.
symbol one_cat_diagram_family_transf_reindex_path [A B I C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (D : τ (Functor B (Functor_cat I C))) (F : τ (Functor A B))
  [i j : τ (Obj I)] (u : τ (Hom I i j))
  : τ (@= (@Transf A C
      (@comp_cat_fapp0 A B C (@diagram_family_at_func B I C D i) F)
      (@comp_cat_fapp0 A B C (@diagram_family_at_func B I C D j) F))
      (@diagram_family_transf A I C (@comp_cat_fapp0 A B (Functor_cat I C) D F) i j u)
      (@fapp0 _ _ (@comp_cat_con_fapp1_func A B C F
        (@diagram_family_at_func B I C D i) (@diagram_family_at_func B I C D j))
        (@diagram_family_transf B I C D i j u)))
≔ eq_refl (@diagram_family_transf A I C (@comp_cat_fapp0 A B (Functor_cat I C) D F) i j u);
