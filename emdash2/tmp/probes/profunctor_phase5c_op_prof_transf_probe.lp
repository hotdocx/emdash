require open emdash.emdash3_2;

// Pullback along product symmetry twice is neutral even in the canonical
// left-associated functor-composition normal form.
rule @comp_cat_fapp0
      (Product_cat $A $B)
      (Product_cat $B $A)
      $C
      (@comp_cat_fapp0
        (Product_cat $B $A)
        (Product_cat $A $B)
        $C
        $H
        (@Product_swap_func $B $A))
      (@Product_swap_func $A $B)
  ↪ $H;

injective symbol Probe_Op_prof_transf
  [A A' B B' : Cat]
  [R' : τ (Catd (Product_cat (Op_cat A') B'))]
  [R : τ (Catd (Product_cat (Op_cat A) B))]
  [F : τ (Functor A' A)]
  [G : τ (Functor B' B)]
  (r : τ (Obj (@Prof_transf_cat A A' B B' R' F R G)))
  : τ (Obj
      (@Prof_transf_cat
        (Op_cat B) (Op_cat B')
        (Op_cat A) (Op_cat A')
        (@Op_prof A' B' R')
        (@Op_func B' B G)
        (@Op_prof A B R)
        (@Op_func A' A F)));

rule @Probe_Op_prof_transf
      (Op_cat $B) (Op_cat $B')
      (Op_cat $A) (Op_cat $A')
      (@Op_prof $A' $B' $R')
      (@Op_prof $A $B $R)
      (@Op_func $B' $B $G)
      (@Op_func $A' $A $F)
      (@Probe_Op_prof_transf
        $A $A' $B $B'
        $R' $R $F $G
        $r)
  ↪ $r;

rule @Probe_Op_prof_transf
      $A $A $B $B
      $R $R
      (@id_func $A)
      (@id_func $B)
      (@Prof_id_transf $A $B $R)
  ↪ @Prof_id_transf
      (Op_cat $B)
      (Op_cat $A)
      (@Op_prof $A $B $R);

rule @Probe_Op_prof_transf
      $A2 $A0 $B2 $B0
      $R0 $R2
      (@comp_cat_fapp0 $A0 $A1 $A2 $F12 $F01)
      (@comp_cat_fapp0 $B0 $B1 $B2 $G12 $G01)
      (@Prof_comp_transf
        $A0 $A1 $A2
        $B0 $B1 $B2
        $R0 $R1 $R2
        $F01 $G01
        $F12 $G12
        $s $r)
  ↪ @Prof_comp_transf
      (Op_cat $B0) (Op_cat $B1) (Op_cat $B2)
      (Op_cat $A0) (Op_cat $A1) (Op_cat $A2)
      (@Op_prof $A0 $B0 $R0)
      (@Op_prof $A1 $B1 $R1)
      (@Op_prof $A2 $B2 $R2)
      (@Op_func $B0 $B1 $G01)
      (@Op_func $A0 $A1 $F01)
      (@Op_func $B1 $B2 $G12)
      (@Op_func $A1 $A2 $F12)
      (@Probe_Op_prof_transf
        $A2 $A1 $B2 $B1
        $R1 $R2 $F12 $G12
        $s)
      (@Probe_Op_prof_transf
        $A1 $A0 $B1 $B0
        $R0 $R1 $F01 $G01
        $r);

assert [A A' B B' : Cat]
  [R' : τ (Catd (Product_cat (Op_cat A') B'))]
  [R : τ (Catd (Product_cat (Op_cat A) B))]
  [F : τ (Functor A' A)]
  [G : τ (Functor B' B)]
  (r : τ (Obj (@Prof_transf_cat A A' B B' R' F R G))) ⊢
  @Probe_Op_prof_transf A A' B B' R' R F G r
  : τ (Obj
      (@Prof_transf_cat
        (Op_cat B) (Op_cat B')
        (Op_cat A) (Op_cat A')
        (@Op_prof A' B' R')
        (@Op_func B' B G)
        (@Op_prof A B R)
        (@Op_func A' A F)));

assert [A B : Cat]
  (R : τ (Catd (Product_cat (Op_cat A) B))) ⊢
  @Probe_Op_prof_transf
    A A B B
    R R
    (@id_func A)
    (@id_func B)
    (@Prof_id_transf A B R)
  ≡ @Prof_id_transf
      (Op_cat B)
      (Op_cat A)
      (@Op_prof A B R);

assert
  [A0 A1 A2 B0 B1 B2 : Cat]
  [R0 : τ (Catd (Product_cat (Op_cat A0) B0))]
  [R1 : τ (Catd (Product_cat (Op_cat A1) B1))]
  [R2 : τ (Catd (Product_cat (Op_cat A2) B2))]
  [F01 : τ (Functor A0 A1)]
  [G01 : τ (Functor B0 B1)]
  [F12 : τ (Functor A1 A2)]
  [G12 : τ (Functor B1 B2)]
  (s : τ (Obj (@Prof_transf_cat A2 A1 B2 B1 R1 F12 R2 G12)))
  (r : τ (Obj (@Prof_transf_cat A1 A0 B1 B0 R0 F01 R1 G01))) ⊢
  @Probe_Op_prof_transf
    A2 A0 B2 B0
    R0 R2
    (@comp_cat_fapp0 A0 A1 A2 F12 F01)
    (@comp_cat_fapp0 B0 B1 B2 G12 G01)
    (@Prof_comp_transf
      A0 A1 A2 B0 B1 B2
      R0 R1 R2
      F01 G01 F12 G12
      s r)
  ≡ @Prof_comp_transf
      (Op_cat B0) (Op_cat B1) (Op_cat B2)
      (Op_cat A0) (Op_cat A1) (Op_cat A2)
      (@Op_prof A0 B0 R0)
      (@Op_prof A1 B1 R1)
      (@Op_prof A2 B2 R2)
      (@Op_func B0 B1 G01)
      (@Op_func A0 A1 F01)
      (@Op_func B1 B2 G12)
      (@Op_func A1 A2 F12)
      (@Probe_Op_prof_transf
        A2 A1 B2 B1
        R1 R2 F12 G12
        s)
      (@Probe_Op_prof_transf
        A1 A0 B1 B0
        R0 R1 F01 G01
        r);
