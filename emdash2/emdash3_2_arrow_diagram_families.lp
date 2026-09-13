/*
  Naturally varying arrows as whole walking-arrow diagrams.

  A transformation eta:F⇒G is an arrow in Functor_cat(K,C). Introduce its
  walking-arrow diagram there, then exchange the shape and parameter axes.
  Source, target and differential whole observations recover F, G and eta;
  the parameter action has components F[p], G[p] and mixed action eta[p].
  No arrow-data square record or new functor primitive is added.
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

// Proof-time comparison of the introduced arrow family after exchange.
// The two Terminal domains are walking-arrow discriminators; whole runtime
// heads are retained. This is the existing point-introduction comparison
// observed through exchange, not injectivity of arbitrary functor action.
unif_rule
  @sym_func _ $B $C
    (@sym_fapp0_func _ $I _
      (@join_elim_func Terminal_cat Terminal_cat _
        (@Const_func _ _ $F) (@Const_func _ _ $G) (@Const_func _ _ $eta)) $i)
  ≡ @sym_func _ $B1 $C1
      (@join_elim_func $L $R $D
        (@Const_func _ _ $Fi) (@Const_func _ _ $Gi) (@Const_func _ _ $etai))
  ↪ [ $B1 ≡ $B; $C1 ≡ $C; $L ≡ Terminal_cat; $R ≡ Terminal_cat;
      $D ≡ (Functor_cat $B $C);
      $Fi ≡ (@fapp0 $I (Functor_cat $B $C) $F $i);
      $Gi ≡ (@fapp0 $I (Functor_cat $B $C) $G $i);
      $etai ≡ (@tapp0_fapp0 $I (Functor_cat $B $C) $F $G $i $eta) ];

// E₀/E₁ after postcomposition by Arr(η) compute to postcomposition by F/G.
// Cat/id and the two Terminal domains discriminate the existing represented
// action and walking-arrow constructor. This is constructor evaluation.
rule @comp_fapp0 Cat_cat _ _ _
      (@comp_fapp0 Cat_cat _ _ _
        (@fapp0_func _ _ (@fapp0 _ _ (@join_fst_func Terminal_cat Terminal_cat) Terminal_obj))
        (@sym_func_func $B _ $C))
      (@hom_postcomp_func Cat_cat Cat_cat (@id Cat_cat Cat_cat) $B $A _
        (@sym_func _ $A $C
          (@join_elim_func Terminal_cat Terminal_cat _
            (@Const_func _ _ $F) (@Const_func _ _ _) (@Const_func _ _ _))))
  ↪ @comp_cat_cov_func $B $A $C $F;

rule @comp_fapp0 Cat_cat _ _ _
      (@comp_fapp0 Cat_cat _ _ _
        (@fapp0_func _ _ (@fapp0 _ _ (@join_snd_func Terminal_cat Terminal_cat) Terminal_obj))
        (@sym_func_func $B _ $C))
      (@hom_postcomp_func Cat_cat Cat_cat (@id Cat_cat Cat_cat) $B $A _
        (@sym_func _ $A $C
          (@join_elim_func Terminal_cat Terminal_cat _
            (@Const_func _ _ _) (@Const_func _ _ $G) (@Const_func _ _ _))))
  ↪ @comp_cat_cov_func $B $A $C $G;

// The object-first route has already erased the composite-functor head.
// Complete the same constructor projection there; both routes retain X.
rule @sym_fapp0_func _ _ $C
      (@hom_postcomp_fapp0 Cat_cat Cat_cat (@id Cat_cat Cat_cat) $B $A _
        (@sym_func _ $A $C
          (@join_elim_func Terminal_cat Terminal_cat _
            (@Const_func _ _ $F) (@Const_func _ _ _) (@Const_func _ _ _))) $X)
      (@fapp0 _ _ (@join_fst_func Terminal_cat Terminal_cat) Terminal_obj)
  ↪ @hom_postcomp_fapp0 Cat_cat Cat_cat (@id Cat_cat Cat_cat) $B $A $C $F $X;

rule @sym_fapp0_func _ _ $C
      (@hom_postcomp_fapp0 Cat_cat Cat_cat (@id Cat_cat Cat_cat) $B $A _
        (@sym_func _ $A $C
          (@join_elim_func Terminal_cat Terminal_cat _
            (@Const_func _ _ _) (@Const_func _ _ $G) (@Const_func _ _ _))) $X)
      (@fapp0 _ _ (@join_snd_func Terminal_cat Terminal_cat) Terminal_obj)
  ↪ @hom_postcomp_fapp0 Cat_cat Cat_cat (@id Cat_cat Cat_cat) $B $A $C $G $X;
