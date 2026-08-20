/*
  Whole terminal-right normalization for a reindexed unit profunctor.

  The native recursive action is retained by homd_/Prof_reindex over the
  product base A^op x 1.  Restricting it along p |-> (p,id_*) leaves a whole
  Cat-valued family on Hom_A(W,X)^op.  A supplied normality witness for the
  terminal branch identifies that family propositionally with the canonical
  source-precomposition family p |-> Hom_B(g o F[p],h).

  The equality-induced displayed map and its Pi action transport whole
  sections, not isolated cells, and therefore retain another hom action.  This
  is the dimension-independent normalization used by every recursive join
  successor A |-> Join(A,1); it contains no ordinal, face, or simplex-specific
  data.  The module adds no rewrite rule or proof-time unifier.
*/

require open emdash.emdash3_2;

symbol prof_terminal_base
  [A : Cat]
  (x : τ (Obj A))
  : τ (Obj (Product_cat (Op_cat A) Terminal_cat))
≔ @Product_pair (Op_cat A) Terminal_cat x Terminal_obj;

symbol prof_terminal_reversed_base_hom_func
  [A : Cat]
  [W X : τ (Obj A)]
  : τ (Functor
      (Hom_cat A W X)
      (Hom_cat
        (Product_cat (Op_cat A) Terminal_cat)
        (@prof_terminal_base A X)
        (@prof_terminal_base A W)))
≔ @comp_cat_fapp0
    (Hom_cat A W X)
    (Functor_cat
      (Hom_cat Terminal_cat Terminal_obj Terminal_obj)
      (Product_cat
        (Hom_cat A W X)
        (Hom_cat Terminal_cat Terminal_obj Terminal_obj)))
    (Product_cat
      (Hom_cat A W X)
      (Hom_cat Terminal_cat Terminal_obj Terminal_obj))
    (@fapp0_func
      (Hom_cat Terminal_cat Terminal_obj Terminal_obj)
      (Product_cat
        (Hom_cat A W X)
        (Hom_cat Terminal_cat Terminal_obj Terminal_obj))
      Terminal_obj)
    (@Product_pair_tele_func
      (Hom_cat A W X)
      (Hom_cat Terminal_cat Terminal_obj Terminal_obj));

symbol prof_terminal_prof
  [A B : Cat]
  (F : τ (Functor A B))
  (G : τ (Functor Terminal_cat B))
  : τ (Catd (Product_cat (Op_cat A) Terminal_cat))
≔ @Prof_reindex B A B Terminal_cat (@Unit_prof B) F G;

symbol prof_terminal_terminal_action
  [B : Cat]
  (G : τ (Functor Terminal_cat B))
  : τ (Hom B
      (@fapp0 Terminal_cat B G Terminal_obj)
      (@fapp0 Terminal_cat B G Terminal_obj))
≔ @fapp1_fapp0
    Terminal_cat B G
    Terminal_obj Terminal_obj Terminal_obj;

// Canonical source action p |-> g o F[p], whole in p.
symbol prof_terminal_expected_source_func
  [A B : Cat]
  (F : τ (Functor A B))
  (G : τ (Functor Terminal_cat B))
  [W X : τ (Obj A)]
  (g : τ (Hom B
      (@fapp0 A B F X)
      (@fapp0 Terminal_cat B G Terminal_obj)))
  : τ (Functor
      (Hom_cat A W X)
      (Hom_cat B
        (@fapp0 A B F W)
        (@fapp0 Terminal_cat B G Terminal_obj)))
≔ @comp_cat_fapp0
    (Hom_cat A W X)
    (Functor_cat
      (Hom_cat B
        (@fapp0 A B F X)
        (@fapp0 Terminal_cat B G Terminal_obj))
      (Hom_cat B
        (@fapp0 A B F W)
        (@fapp0 Terminal_cat B G Terminal_obj)))
    (Hom_cat B
      (@fapp0 A B F W)
      (@fapp0 Terminal_cat B G Terminal_obj))
    (@fapp0_func
      (Hom_cat B
        (@fapp0 A B F X)
        (@fapp0 Terminal_cat B G Terminal_obj))
      (Hom_cat B
        (@fapp0 A B F W)
        (@fapp0 Terminal_cat B G Terminal_obj))
      g)
    (@hom_precomp_along_tele_func
      A B F
      (@fapp0 Terminal_cat B G Terminal_obj)
      W X);

// Native recursive family owned by homd_/Prof_reindex and restricted along
// p |-> (p,id_*).
symbol prof_terminal_native_action_catd
  [A B : Cat]
  (F : τ (Functor A B))
  (G : τ (Functor Terminal_cat B))
  [W X : τ (Obj A)]
  (g : τ (Hom B
      (@fapp0 A B F X)
      (@fapp0 Terminal_cat B G Terminal_obj)))
  (h : τ (Hom B
      (@fapp0 A B F W)
      (@fapp0 Terminal_cat B G Terminal_obj)))
  : τ (Catd (Op_cat (Hom_cat A W X)))
≔ @Pullback_catd
    (Op_cat (Hom_cat A W X))
    (Op_cat (Hom_cat
      (Product_cat (Op_cat A) Terminal_cat)
      (@prof_terminal_base A X)
      (@prof_terminal_base A W)))
    (@homd_
      (Product_cat (Op_cat A) Terminal_cat)
      (@prof_terminal_prof A B F G)
      (@prof_terminal_prof A B F G)
      (@id_funcd
        (Product_cat (Op_cat A) Terminal_cat)
        (@prof_terminal_prof A B F G))
      (@prof_terminal_base A X) g
      (@prof_terminal_base A W) h)
    (@Op_func
      (Hom_cat A W X)
      (Hom_cat
        (Product_cat (Op_cat A) Terminal_cat)
        (@prof_terminal_base A X)
        (@prof_terminal_base A W))
      (@prof_terminal_reversed_base_hom_func A W X));

// Canonical dependent-hom family with the terminal action normalized away.
symbol prof_terminal_expected_action_catd
  [A B : Cat]
  (F : τ (Functor A B))
  (G : τ (Functor Terminal_cat B))
  [W X : τ (Obj A)]
  (g : τ (Hom B
      (@fapp0 A B F X)
      (@fapp0 Terminal_cat B G Terminal_obj)))
  (h : τ (Hom B
      (@fapp0 A B F W)
      (@fapp0 Terminal_cat B G Terminal_obj)))
  : τ (Catd (Op_cat (Hom_cat A W X)))
≔ @comp_cat_fapp0
    (Op_cat (Hom_cat A W X))
    (Op_cat (Hom_cat B
      (@fapp0 A B F W)
      (@fapp0 Terminal_cat B G Terminal_obj)))
    Cat_cat
    (@hom_con
      (Hom_cat B
        (@fapp0 A B F W)
        (@fapp0 Terminal_cat B G Terminal_obj))
      h
      (Hom_cat B
        (@fapp0 A B F W)
        (@fapp0 Terminal_cat B G Terminal_obj))
      (@id_func (Hom_cat B
        (@fapp0 A B F W)
        (@fapp0 Terminal_cat B G Terminal_obj))))
    (@Op_func
      (Hom_cat A W X)
      (Hom_cat B
        (@fapp0 A B F W)
        (@fapp0 Terminal_cat B G Terminal_obj))
      (@prof_terminal_expected_source_func A B F G W X g));

/*
  Selected whole semantic comparison.  The normality witness makes the
  statement valid after the ambient Functor classifier is no longer globally
  strict.  It is a whole family path, not a component or simplex filler.
*/
constant symbol prof_terminal_native_expected_path
  [A B : Cat]
  (F : τ (Functor A B))
  (G : τ (Functor Terminal_cat B))
  [W X : τ (Obj A)]
  (g : τ (Hom B
      (@fapp0 A B F X)
      (@fapp0 Terminal_cat B G Terminal_obj)))
  (h : τ (Hom B
      (@fapp0 A B F W)
      (@fapp0 Terminal_cat B G Terminal_obj)))
  (normal : τ (@=
      (Hom B
        (@fapp0 Terminal_cat B G Terminal_obj)
        (@fapp0 Terminal_cat B G Terminal_obj))
      (@prof_terminal_terminal_action B G)
      (@id B (@fapp0 Terminal_cat B G Terminal_obj))))
  : τ (@=
      (Obj (@Catd_cat (Op_cat (Hom_cat A W X))))
      (@prof_terminal_native_action_catd A B F G W X g h)
      (@prof_terminal_expected_action_catd A B F G W X g h));

symbol prof_terminal_native_expected_funcd
  [A B : Cat]
  (F : τ (Functor A B))
  (G : τ (Functor Terminal_cat B))
  [W X : τ (Obj A)]
  (g : τ (Hom B
      (@fapp0 A B F X)
      (@fapp0 Terminal_cat B G Terminal_obj)))
  (h : τ (Hom B
      (@fapp0 A B F W)
      (@fapp0 Terminal_cat B G Terminal_obj)))
  (normal : τ (@=
      (Hom B
        (@fapp0 Terminal_cat B G Terminal_obj)
        (@fapp0 Terminal_cat B G Terminal_obj))
      (@prof_terminal_terminal_action B G)
      (@id B (@fapp0 Terminal_cat B G Terminal_obj))))
  : τ (Functord
      (@prof_terminal_native_action_catd A B F G W X g h)
      (@prof_terminal_expected_action_catd A B F G W X g h))
≔ @path_to_hom
    (@Catd_cat (Op_cat (Hom_cat A W X)))
    (@prof_terminal_native_action_catd A B F G W X g h)
    (@prof_terminal_expected_action_catd A B F G W X g h)
    (@prof_terminal_native_expected_path A B F G W X g h normal);

symbol prof_terminal_section_normalization_func
  [A B : Cat]
  (F : τ (Functor A B))
  (G : τ (Functor Terminal_cat B))
  [W X : τ (Obj A)]
  (g : τ (Hom B
      (@fapp0 A B F X)
      (@fapp0 Terminal_cat B G Terminal_obj)))
  (h : τ (Hom B
      (@fapp0 A B F W)
      (@fapp0 Terminal_cat B G Terminal_obj)))
  (normal : τ (@=
      (Hom B
        (@fapp0 Terminal_cat B G Terminal_obj)
        (@fapp0 Terminal_cat B G Terminal_obj))
      (@prof_terminal_terminal_action B G)
      (@id B (@fapp0 Terminal_cat B G Terminal_obj))))
  : τ (Functor
      (Pi_cat (@prof_terminal_native_action_catd A B F G W X g h))
      (Pi_cat (@prof_terminal_expected_action_catd A B F G W X g h)))
≔ @fapp1_fapp0
    (@Catd_cat (Op_cat (Hom_cat A W X)))
    Cat_cat
    (@Pi_func (Op_cat (Hom_cat A W X)))
    (@prof_terminal_native_action_catd A B F G W X g h)
    (@prof_terminal_expected_action_catd A B F G W X g h)
    (@prof_terminal_native_expected_funcd A B F G W X g h normal);

symbol prof_terminal_section_normalization_next_func
  [A B : Cat]
  (F : τ (Functor A B))
  (G : τ (Functor Terminal_cat B))
  [W X : τ (Obj A)]
  (g : τ (Hom B
      (@fapp0 A B F X)
      (@fapp0 Terminal_cat B G Terminal_obj)))
  (h : τ (Hom B
      (@fapp0 A B F W)
      (@fapp0 Terminal_cat B G Terminal_obj)))
  (normal : τ (@=
      (Hom B
        (@fapp0 Terminal_cat B G Terminal_obj)
        (@fapp0 Terminal_cat B G Terminal_obj))
      (@prof_terminal_terminal_action B G)
      (@id B (@fapp0 Terminal_cat B G Terminal_obj))))
  [s t : τ (Obj (Pi_cat
      (@prof_terminal_native_action_catd A B F G W X g h)))]
  : τ (Functor
      (Hom_cat
        (Pi_cat (@prof_terminal_native_action_catd A B F G W X g h)) s t)
      (Hom_cat
        (Pi_cat (@prof_terminal_expected_action_catd A B F G W X g h))
        (@fapp0
          (Pi_cat (@prof_terminal_native_action_catd A B F G W X g h))
          (Pi_cat (@prof_terminal_expected_action_catd A B F G W X g h))
          (@prof_terminal_section_normalization_func A B F G W X g h normal) s)
        (@fapp0
          (Pi_cat (@prof_terminal_native_action_catd A B F G W X g h))
          (Pi_cat (@prof_terminal_expected_action_catd A B F G W X g h))
          (@prof_terminal_section_normalization_func A B F G W X g h normal) t)))
≔ @fapp1_func
    (Pi_cat (@prof_terminal_native_action_catd A B F G W X g h))
    (Pi_cat (@prof_terminal_expected_action_catd A B F G W X g h))
    (@prof_terminal_section_normalization_func A B F G W X g h normal)
    s t;
