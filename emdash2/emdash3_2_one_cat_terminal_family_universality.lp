/* Native whole terminal/initial family universality, in an ordinary target.
   This explicitly extends the pointwise-uniqueness terminal-object presentation:
   the whole DefIso instances below are not derived from its existing beta
   rules. Both directions preserve both endpoints by identity, and reuse
   the generic DefIso inverse cuts. No connecting or exactness axiom occurs. */
require open emdash.emdash3_2_zero_arrow_diagrams;

// Whole normalization of a terminal arrow family, with its original F and h.
injective symbol one_cat_terminal_arrow_family_iso
  [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F : τ (Functor B C)) (h : τ (@Transf B C F (@Const_func B C t)))
  : τ (@DefIso (Functor_cat B (Functor_cat WalkingArrow_cat C))
      (@transf_arrow_diagram_func B C F (@Const_func B C t) h)
      (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) F));

// terminal to: the src component is the same endpoint identity.
// The walking-arrow constructor is the actual shape discriminator.
rule @tapp0_fapp0 _ _ _ _
      (@fapp0 _ _ (@join_fst_func Terminal_cat Terminal_cat) Terminal_obj)
      (@tapp0_fapp0 _ _ _ _ $b
        (@defiso_to _ _ _ (@one_cat_terminal_arrow_family_iso $B $C _ _ _ $F _)))
  ↪ @id $C (@fapp0 $B $C $F $b);

// terminal to: the tgt component is the same endpoint identity.
// The walking-arrow constructor is the actual shape discriminator.
rule @tapp0_fapp0 _ _ _ _
      (@fapp0 _ _ (@join_snd_func Terminal_cat Terminal_cat) Terminal_obj)
      (@tapp0_fapp0 _ _ _ _ _
        (@defiso_to _ _ _ (@one_cat_terminal_arrow_family_iso _ $C _ $t _ _ _)))
  ↪ @id $C $t;

// terminal from: the src component is the same endpoint identity.
// The walking-arrow constructor is the actual shape discriminator.
rule @tapp0_fapp0 _ _ _ _
      (@fapp0 _ _ (@join_fst_func Terminal_cat Terminal_cat) Terminal_obj)
      (@tapp0_fapp0 _ _ _ _ $b
        (@defiso_from _ _ _ (@one_cat_terminal_arrow_family_iso $B $C _ _ _ $F _)))
  ↪ @id $C (@fapp0 $B $C $F $b);

// terminal from: the tgt component is the same endpoint identity.
// The walking-arrow constructor is the actual shape discriminator.
rule @tapp0_fapp0 _ _ _ _
      (@fapp0 _ _ (@join_snd_func Terminal_cat Terminal_cat) Terminal_obj)
      (@tapp0_fapp0 _ _ _ _ _
        (@defiso_from _ _ _ (@one_cat_terminal_arrow_family_iso _ $C _ $t _ _ _)))
  ↪ @id $C $t;

// Whole normalization of an initial arrow family, with its original F and h.
injective symbol one_cat_initial_arrow_family_iso
  [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (F : τ (Functor B C)) (h : τ (@Transf B C (@Const_func B C t) F))
  : τ (@DefIso (Functor_cat B (Functor_cat WalkingArrow_cat C))
      (@transf_arrow_diagram_func B C (@Const_func B C t) F h)
      (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) F));

// initial to: the src component is the same endpoint identity.
// The walking-arrow constructor is the actual shape discriminator.
rule @tapp0_fapp0 _ _ _ _
      (@fapp0 _ _ (@join_fst_func Terminal_cat Terminal_cat) Terminal_obj)
      (@tapp0_fapp0 _ _ _ _ _
        (@defiso_to _ _ _ (@one_cat_initial_arrow_family_iso _ $C _ $t _ _ _)))
  ↪ @id $C $t;

// initial to: the tgt component is the same endpoint identity.
// The walking-arrow constructor is the actual shape discriminator.
rule @tapp0_fapp0 _ _ _ _
      (@fapp0 _ _ (@join_snd_func Terminal_cat Terminal_cat) Terminal_obj)
      (@tapp0_fapp0 _ _ _ _ $b
        (@defiso_to _ _ _ (@one_cat_initial_arrow_family_iso $B $C _ _ _ $F _)))
  ↪ @id $C (@fapp0 $B $C $F $b);

// initial from: the src component is the same endpoint identity.
// The walking-arrow constructor is the actual shape discriminator.
rule @tapp0_fapp0 _ _ _ _
      (@fapp0 _ _ (@join_fst_func Terminal_cat Terminal_cat) Terminal_obj)
      (@tapp0_fapp0 _ _ _ _ _
        (@defiso_from _ _ _ (@one_cat_initial_arrow_family_iso _ $C _ $t _ _ _)))
  ↪ @id $C $t;

// initial from: the tgt component is the same endpoint identity.
// The walking-arrow constructor is the actual shape discriminator.
rule @tapp0_fapp0 _ _ _ _
      (@fapp0 _ _ (@join_snd_func Terminal_cat Terminal_cat) Terminal_obj)
      (@tapp0_fapp0 _ _ _ _ $b
        (@defiso_from _ _ _ (@one_cat_initial_arrow_family_iso $B $C _ _ _ $F _)))
  ↪ @id $C (@fapp0 $B $C $F $b);

// Whole endpoint components of the same selected presentation.
// These retain B and its entire action before taking points. The earlier
// direct double-component clauses remain for the already-projected route;
// both typed routes are checked to meet at the same endpoint identity.
// terminal to, whole fst endpoint.
rule @sym_transf_tapp0_transf _ _ _ _ _
      (@defiso_to _ _ _ (@one_cat_terminal_arrow_family_iso $B $C _ _ _ $F _))
      (@fapp0 _ _ (@join_fst_func Terminal_cat Terminal_cat) Terminal_obj)
  ↪ @id (Functor_cat $B $C) $F;

// terminal to, whole snd endpoint.
rule @sym_transf_tapp0_transf _ _ _ _ _
      (@defiso_to _ _ _ (@one_cat_terminal_arrow_family_iso $B $C _ $t _ _ _))
      (@fapp0 _ _ (@join_snd_func Terminal_cat Terminal_cat) Terminal_obj)
  ↪ @id (Functor_cat $B $C) (@Const_func $B $C $t);

// terminal from, whole fst endpoint.
rule @sym_transf_tapp0_transf _ _ _ _ _
      (@defiso_from _ _ _ (@one_cat_terminal_arrow_family_iso $B $C _ _ _ $F _))
      (@fapp0 _ _ (@join_fst_func Terminal_cat Terminal_cat) Terminal_obj)
  ↪ @id (Functor_cat $B $C) $F;

// terminal from, whole snd endpoint.
rule @sym_transf_tapp0_transf _ _ _ _ _
      (@defiso_from _ _ _ (@one_cat_terminal_arrow_family_iso $B $C _ $t _ _ _))
      (@fapp0 _ _ (@join_snd_func Terminal_cat Terminal_cat) Terminal_obj)
  ↪ @id (Functor_cat $B $C) (@Const_func $B $C $t);

// initial to, whole fst endpoint.
rule @sym_transf_tapp0_transf _ _ _ _ _
      (@defiso_to _ _ _ (@one_cat_initial_arrow_family_iso $B $C _ $t _ _ _))
      (@fapp0 _ _ (@join_fst_func Terminal_cat Terminal_cat) Terminal_obj)
  ↪ @id (Functor_cat $B $C) (@Const_func $B $C $t);

// initial to, whole snd endpoint.
rule @sym_transf_tapp0_transf _ _ _ _ _
      (@defiso_to _ _ _ (@one_cat_initial_arrow_family_iso $B $C _ _ _ $F _))
      (@fapp0 _ _ (@join_snd_func Terminal_cat Terminal_cat) Terminal_obj)
  ↪ @id (Functor_cat $B $C) $F;

// initial from, whole fst endpoint.
rule @sym_transf_tapp0_transf _ _ _ _ _
      (@defiso_from _ _ _ (@one_cat_initial_arrow_family_iso $B $C _ $t _ _ _))
      (@fapp0 _ _ (@join_fst_func Terminal_cat Terminal_cat) Terminal_obj)
  ↪ @id (Functor_cat $B $C) (@Const_func $B $C $t);

// initial from, whole snd endpoint.
rule @sym_transf_tapp0_transf _ _ _ _ _
      (@defiso_from _ _ _ (@one_cat_initial_arrow_family_iso $B $C _ _ _ $F _))
      (@fapp0 _ _ (@join_snd_func Terminal_cat Terminal_cat) Terminal_obj)
  ↪ @id (Functor_cat $B $C) $F;
