/* Whole/point join cross computation and constant-endpoint regression. */
require open emdash.emdash3_2;

// Regression: the represented hom action still computes after the target
// family has reduced from Prof_reindex to Const_catd.
assert (A B : Cat) (b : τ (Obj B))
  (ab : τ (Obj (Product_cat (Op_cat A) A)))
  ⊢ @Fibre_func (Product_cat (Op_cat A) A)
      (@Unit_prof A)
      (@Const_catd (Product_cat (Op_cat A) A) (Hom_cat B b b))
      (@Prof_func_hom A B (@Const_func A B b)) ab
    ≡ @Const_func (Hom_cat A (sigma_Fst ab) (sigma_Snd ab))
      (Hom_cat B b b) (@id B b);

// The next product-base action still reaches the original internal action
// even when its target has already normalized to the constant Hom family.
assert (A B : Cat) (b : τ (Obj B))
  (ab ab' : τ (Obj (Product_cat (Op_cat A) A)))
  (pq : τ (Hom (Product_cat (Op_cat A) A) ab ab'))
  ⊢ @tapp1_fapp0 (Product_cat (Op_cat A) A) Cat_cat
      (@Unit_prof A)
      (@Const_catd (Product_cat (Op_cat A) A) (Hom_cat B b b))
      ab ab' (@Prof_func_hom A B (@Const_func A B b)) pq
    ≡ @tapp1_fapp0 A Cat_cat
      (@hom_ A A (@id_func A) (sigma_Fst ab))
      (@hom_ B A (@Const_func A B b) b)
      (sigma_Snd ab) (sigma_Snd ab')
      (@tapp1_fapp0 (Op_cat A) (@Catd_cat A)
        (@hom_int A A (@id_func A))
        (@comp_cat_fapp0 (Op_cat A) (Op_cat B) (@Catd_cat A)
          (@hom_int B A (@Const_func A B b))
          (@Op_func A B (@Const_func A B b)))
        (sigma_Fst ab) (sigma_Fst ab')
        (@fapp1_int_transf A B (@Const_func A B b)) (sigma_Fst pq))
      (sigma_Snd pq);

// The two newly exposed syntactic naturality overlaps would require this
// reversed-type Unit_prof application. It is not a well-typed functor.
assertnot ⊢ @Unit_prof Cat_cat
  : τ (Functor Cat_cat (Product_cat (Op_cat Cat_cat) Cat_cat));

symbol probe_cross_func [A B : Cat]
  (ab : τ (Obj (Product_cat (Op_cat A) B)))
  : τ (Functor Terminal_cat
      (Hom_cat (Join_cat A B)
        (@fapp0 A (Join_cat A B) (@join_fst_func A B) (sigma_Fst ab))
        (@fapp0 B (Join_cat A B) (@join_snd_func A B) (sigma_Snd ab))))
≔ @tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat
    (@Terminal_prof A B)
    (@Prof_reindex (Join_cat A B) A (Join_cat A B) B
      (@Unit_prof (Join_cat A B)) (@join_fst_func A B) (@join_snd_func A B))
    ab (@join_cross_transf A B);

symbol probe_action_func [A B C : Cat]
  [F : τ (Functor A C)] [G : τ (Functor B C)]
  (cross : τ (Obj (@Prof_transf_cat C A C B
    (@Terminal_prof A B) F (@Unit_prof C) G)))
  (ab : τ (Obj (Product_cat (Op_cat A) B)))
  : τ (Functor Terminal_cat
      (Hom_cat C (@fapp0 A C F (sigma_Fst ab)) (@fapp0 B C G (sigma_Snd ab))))
≔ @comp_cat_fapp0 Terminal_cat _ _
    (@fapp1_func (Join_cat A B) C (@join_elim_func A B C F G cross)
      (@fapp0 A (Join_cat A B) (@join_fst_func A B) (sigma_Fst ab))
      (@fapp0 B (Join_cat A B) (@join_snd_func A B) (sigma_Snd ab)))
    (@probe_cross_func A B ab);

// Whole cross beta with arbitrary varying endpoints and arbitrary cross data.
assert (A B C : Cat) (F : τ (Functor A C)) (G : τ (Functor B C))
  (cross : τ (Obj (@Prof_transf_cat C A C B
    (@Terminal_prof A B) F (@Unit_prof C) G)))
  (ab : τ (Obj (Product_cat (Op_cat A) B)))
  ⊢ @probe_action_func A B C F G cross ab
    ≡ @Fibre_func (Product_cat (Op_cat A) B)
      (@Terminal_prof A B)
      (@Prof_reindex C A C B (@Unit_prof C) F G) cross ab;

// The point-first reduction order reaches the same original cross component.
assert (A B C : Cat) (F : τ (Functor A C)) (G : τ (Functor B C))
  (cross : τ (Obj (@Prof_transf_cat C A C B
    (@Terminal_prof A B) F (@Unit_prof C) G)))
  (ab : τ (Obj (Product_cat (Op_cat A) B)))
  ⊢ @fapp1_fapp0 (Join_cat A B) C (@join_elim_func A B C F G cross) _ _
      (@fapp0 Terminal_cat _ (@probe_cross_func A B ab) Terminal_obj)
    ≡ @fapp0 Terminal_cat _
      (@Fibre_func (Product_cat (Op_cat A) B)
        (@Terminal_prof A B)
        (@Prof_reindex C A C B (@Unit_prof C) F G) cross ab) Terminal_obj;

// Higher action of the whole reduced functor remains available.
assert (A B C : Cat) (F : τ (Functor A C)) (G : τ (Functor B C))
  (cross : τ (Obj (@Prof_transf_cat C A C B
    (@Terminal_prof A B) F (@Unit_prof C) G)))
  (ab : τ (Obj (Product_cat (Op_cat A) B)))
  ⊢ @fapp1_func Terminal_cat _ (@probe_action_func A B C F G cross ab)
      Terminal_obj Terminal_obj
    ≡ @fapp1_func Terminal_cat _
      (@Fibre_func (Product_cat (Op_cat A) B)
        (@Terminal_prof A B)
        (@Prof_reindex C A C B (@Unit_prof C) F G) cross ab)
      Terminal_obj Terminal_obj;

symbol probe_arrow_cross [C : Cat] [x y : τ (Obj C)]
  (f : τ (Hom C x y))
  : τ (Obj (@Prof_transf_cat C Terminal_cat C Terminal_cat
      (@Terminal_prof Terminal_cat Terminal_cat)
      (@Obj_func C x) (@Unit_prof C) (@Obj_func C y)))
≔ @Const_func (Product_cat (Op_cat Terminal_cat) Terminal_cat)
    (Hom_cat C x y) f;

assert (C : Cat) (x y : τ (Obj C)) (f : τ (Hom C x y))
  ⊢ @probe_action_func Terminal_cat Terminal_cat C
      (@Obj_func C x) (@Obj_func C y) (@probe_arrow_cross C x y f)
      (@Product_pair (Op_cat Terminal_cat) Terminal_cat Terminal_obj Terminal_obj)
    ≡ @Obj_func (Hom_cat C x y) f;

// Constant endpoint folding does not collapse an arbitrary endpoint map.
assertnot (A B C : Cat) (R : τ (Prof B C))
  (F : τ (Functor A B)) (b : τ (Obj B)) (c : τ (Obj C))
  ⊢ @Prof_reindex B A C Terminal_cat R F (@Obj_func C c)
    ≡ @Const_catd (Product_cat (Op_cat A) Terminal_cat)
      (@fapp0 (Product_cat (Op_cat B) C) Cat_cat R
        (@Product_pair (Op_cat B) C b c));

assertnot (C : Cat) (x y : τ (Obj C)) (f g : τ (Hom C x y))
  ⊢ @probe_action_func Terminal_cat Terminal_cat C
      (@Obj_func C x) (@Obj_func C y) (@probe_arrow_cross C x y f)
      (@Product_pair (Op_cat Terminal_cat) Terminal_cat Terminal_obj Terminal_obj)
    ≡ @Obj_func (Hom_cat C x y) g;
