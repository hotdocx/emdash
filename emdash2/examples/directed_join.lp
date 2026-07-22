/*
  Reviewer milestone: the primitive directed-inductive join.

  The two inclusions and the internally natural cross cell feed one
  nondependent recursor. Its left, right, and cross-cell betas compute, while
  the primitive join remains distinct from the ordinary product category.
*/

require open emdash.emdash3_2;

assert [A B : Cat] ⊢
  @join_cross_transf A B
  : τ (Obj
      (@Prof_transf_cat
        (@Join_cat A B) A
        (@Join_cat A B) B
        (@Terminal_prof A B)
        (@join_fst_func A B)
        (@Unit_prof (@Join_cat A B))
        (@join_snd_func A B)));

assert [A B E : Cat]
  (first : τ (Functor A E))
  (second : τ (Functor B E))
  (cross : τ (Obj
      (@Prof_transf_cat
        E A E B
        (@Terminal_prof A B)
        first
        (@Unit_prof E)
        second))) ⊢
  @comp_cat_fapp0
    A
    (@Join_cat A B)
    E
    (@join_elim_func A B E first second cross)
    (@join_fst_func A B)
  ≡ first;

assert [A B E : Cat]
  (first : τ (Functor A E))
  (second : τ (Functor B E))
  (cross : τ (Obj
      (@Prof_transf_cat
        E A E B
        (@Terminal_prof A B)
        first
        (@Unit_prof E)
        second))) ⊢
  @comp_cat_fapp0
    B
    (@Join_cat A B)
    E
    (@join_elim_func A B E first second cross)
    (@join_snd_func A B)
  ≡ second;

assert [A B I : Cat]
  (a : τ (Functor I A))
  (b : τ (Functor I B)) ⊢
  @join_cross_hom A B I a b
  ≡ @Prof_cell_eval
      I A B
      (@Join_cat A B)
      (@Join_cat A B)
      (@Unit_prof (@Join_cat A B))
      (@join_fst_func A B)
      (@join_snd_func A B)
      a b
      (@join_cross_transf A B);

assert [A B E : Cat]
  (first : τ (Functor A E))
  (second : τ (Functor B E))
  (cross : τ (Obj
      (@Prof_transf_cat
        E A E B
        (@Terminal_prof A B)
        first
        (@Unit_prof E)
        second))) ⊢
  @join_elim_cross_transf A B E first second cross
  ≡ cross;

assertnot [A B : Cat] ⊢
  @Join_cat A B
  ≡ @Product_cat A B;
