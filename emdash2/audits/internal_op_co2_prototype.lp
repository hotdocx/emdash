/* NON-LIBRARY VARIANCE PROTOTYPE.
   Local dimension-two opposite and whole-action candidate only.
   The imported kernel still contains its original unsound op/family package.
   Do not register as a positive feature or import into the library.
   See docs/TYPESCRIPT_EMDASH_INTERNAL_OP_VARIANCE_REPAIR_PLAN.md. */
require open emdash.emdash3_2;

// Reverse 2-cells by taking the existing 1-opposite of each Hom category.
injective symbol Co2_cat : Cat → Cat;
rule Obj (Co2_cat $C) ↪ Obj $C;
rule Hom_cat (Co2_cat $C) $x $y ↪ Op_cat (Hom_cat $C $x $y);
rule Co2_cat (Co2_cat $C) ↪ $C;
rule @id (Co2_cat $C) $x ↪ @id $C $x;
rule @comp_fapp0 (Co2_cat $C) $x $y $z $g $f
  ↪ @comp_fapp0 $C $x $y $z $g $f;

// This whole functor retains the next Hom action through Op_func.
injective symbol Co2_func [A B : Cat] (F : τ (Functor A B))
  : τ (Functor (Co2_cat A) (Co2_cat B));
rule @fapp0 _ _ (@Co2_func $A $B $F) $x ↪ @fapp0 $A $B $F $x;
rule @fapp1_func _ _ (@Co2_func $A $B $F) $x $y
  ↪ @Op_func (Hom_cat $A $x $y)
      (Hom_cat $B (@fapp0 $A $B $F $x) (@fapp0 $A $B $F $y))
      (@fapp1_func $A $B $F $x $y);
rule @fapp1_fapp0 _ _ (@Co2_func $A $B $F) $x $y $f
  ↪ @fapp1_fapp0 $A $B $F $x $y $f;
rule @Co2_func _ _ (@Co2_func _ _ $F) ↪ $F;

// Correct the universe-level source, preserving whole hom action.
constant symbol op_co2 : τ (Functor (Co2_cat Cat_cat) Cat_cat);
rule @fapp0 _ _ op_co2 $C ↪ Op_cat $C;
rule @fapp1_fapp0 _ _ op_co2 $A $B $F ↪ @Op_func $A $B $F;

// eta : G ⇒ F is an arrow F → G in the source opposite functor category.
rule @fapp1_fapp0 _ _
      (@fapp1_func _ _ op_co2 $A $B) $F $G $eta
  ↪ @Op_transf $A $B $G $F $eta;

// Readable whole views, not extra primitive computation heads.
symbol op_co2_hom_func (A B : Cat)
  : τ (Functor (Op_cat (Functor_cat A B))
      (Functor_cat (Op_cat A) (Op_cat B)))
≔ @fapp1_func (Co2_cat Cat_cat) Cat_cat op_co2 A B;

symbol op_co2_transf_func [A B : Cat] (F G : τ (Functor A B))
  : τ (Functor (@Transf_cat A B F G)
      (@Transf_cat (Op_cat A) (Op_cat B)
        (@Op_func A B G) (@Op_func A B F)))
≔ @fapp1_func (Op_cat (Functor_cat A B))
    (Functor_cat (Op_cat A) (Op_cat B))
    (op_co2_hom_func A B) G F;

// Correctly based pointwise opposite. Keep the generic postcomposition owner
// selected by the whole opposite-family operator, with no new runtime fold.
symbol op_co2_catd [K : Cat] (E : τ (Catd K)) : τ (Catd (Co2_cat K))
≔ @hom_postcomp_fapp0 Cat_cat Cat_cat (@id_func Cat_cat)
    (Co2_cat K) (Co2_cat Cat_cat) Cat_cat
    op_co2 (@Co2_func K Cat_cat E);
