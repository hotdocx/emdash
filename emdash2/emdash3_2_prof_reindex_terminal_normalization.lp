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
  data. The original family comparison is rule-free; the explicit directed
  refinement below adds only three guarded component projection rules and no
  proof-time unifier.
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

// -------------------------------------------------------------------------------------------------
// Explicit componentwise terminal-right normalization
// -------------------------------------------------------------------------------------------------
/*
  The equality-only normalizer above remains the compatibility surface for
  transporting complete sections.  The following whole directed comparison
  additionally exposes the point component needed by recursive dependent-hom
  consumers.  Its component is built from the supplied terminal normality
  path and rigid two-endpoint Hom action; the whole Transf/Functord owners
  retain every next action.  These are generic in A,B,F,G and add no ordinal
  or simplex-specific conversion.
*/

symbol prof_terminal_retained_source_func
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
    (Hom_cat
      (Product_cat (Op_cat A) Terminal_cat)
      (@prof_terminal_base A X)
      (@prof_terminal_base A W))
    (Fibre_cat
      (@prof_terminal_prof A B F G)
      (@prof_terminal_base A W))
    (@fib_cov_tapp0_func
      (Product_cat (Op_cat A) Terminal_cat)
      (@prof_terminal_prof A B F G)
      (@prof_terminal_base A X)
      (@prof_terminal_base A W)
      g)
    (@prof_terminal_reversed_base_hom_func A W X);

symbol prof_terminal_identity_source
  [A B : Cat]
  (F : τ (Functor A B))
  (G : τ (Functor Terminal_cat B))
  [W X : τ (Obj A)]
  (g : τ (Hom B
      (@fapp0 A B F X)
      (@fapp0 Terminal_cat B G Terminal_obj)))
  (p : τ (Hom A W X))
  : τ (Hom B
      (@fapp0 A B F W)
      (@fapp0 Terminal_cat B G Terminal_obj))
≔ @Hom_fapp0
    B
    (@fapp0 A B F X)
    (@fapp0 A B F W)
    (@fapp0 Terminal_cat B G Terminal_obj)
    (@fapp0 Terminal_cat B G Terminal_obj)
    (@fapp1_fapp0 A B F W X p)
    (@id B (@fapp0 Terminal_cat B G Terminal_obj))
    g;

symbol prof_terminal_retained_identity_source_path
  [A B : Cat]
  (F : τ (Functor A B))
  (G : τ (Functor Terminal_cat B))
  [W X : τ (Obj A)]
  (g : τ (Hom B
      (@fapp0 A B F X)
      (@fapp0 Terminal_cat B G Terminal_obj)))
  (normal : τ (@=
      (Hom B
        (@fapp0 Terminal_cat B G Terminal_obj)
        (@fapp0 Terminal_cat B G Terminal_obj))
      (@prof_terminal_terminal_action B G)
      (@id B (@fapp0 Terminal_cat B G Terminal_obj))))
  (p : τ (Hom A W X))
  : τ (@=
      (Hom B
        (@fapp0 A B F W)
        (@fapp0 Terminal_cat B G Terminal_obj))
      (@fapp0
        (Hom_cat A W X)
        (Hom_cat B
          (@fapp0 A B F W)
          (@fapp0 Terminal_cat B G Terminal_obj))
        (@prof_terminal_retained_source_func A B F G W X g) p)
      (@prof_terminal_identity_source A B F G W X g p))
≔ @eq_ap
    (Hom B
      (@fapp0 Terminal_cat B G Terminal_obj)
      (@fapp0 Terminal_cat B G Terminal_obj))
    (Hom B
      (@fapp0 A B F W)
      (@fapp0 Terminal_cat B G Terminal_obj))
    (λ t : τ (Hom B
        (@fapp0 Terminal_cat B G Terminal_obj)
        (@fapp0 Terminal_cat B G Terminal_obj)),
      @Hom_fapp0
        B
        (@fapp0 A B F X)
        (@fapp0 A B F W)
        (@fapp0 Terminal_cat B G Terminal_obj)
        (@fapp0 Terminal_cat B G Terminal_obj)
        (@fapp1_fapp0 A B F W X p)
        t g)
    (@prof_terminal_terminal_action B G)
    (@id B (@fapp0 Terminal_cat B G Terminal_obj))
    normal;

symbol prof_terminal_raw_composite_source
  [A B : Cat]
  (F : τ (Functor A B))
  (G : τ (Functor Terminal_cat B))
  [W X : τ (Obj A)]
  (g : τ (Hom B
      (@fapp0 A B F X)
      (@fapp0 Terminal_cat B G Terminal_obj)))
  (p : τ (Hom A W X))
  : τ (Hom B
      (@fapp0 A B F W)
      (@fapp0 Terminal_cat B G Terminal_obj))
≔ @comp_fapp0
    B
    (@fapp0 A B F W)
    (@fapp0 A B F X)
    (@fapp0 Terminal_cat B G Terminal_obj)
    g
    (@fapp1_fapp0 A B F W X p);

symbol prof_terminal_identity_raw_composite_path
  [A B : Cat]
  (F : τ (Functor A B))
  (G : τ (Functor Terminal_cat B))
  [W X : τ (Obj A)]
  (g : τ (Hom B
      (@fapp0 A B F X)
      (@fapp0 Terminal_cat B G Terminal_obj)))
  (p : τ (Hom A W X))
  : τ (@=
      (Hom B
        (@fapp0 A B F W)
        (@fapp0 Terminal_cat B G Terminal_obj))
      (@prof_terminal_identity_source A B F G W X g p)
      (@prof_terminal_raw_composite_source A B F G W X g p))
≔ @eq_refl
    (Hom B
      (@fapp0 A B F W)
      (@fapp0 Terminal_cat B G Terminal_obj))
    (@prof_terminal_identity_source A B F G W X g p);

symbol prof_terminal_expected_raw_composite_path
  [A B : Cat]
  (F : τ (Functor A B))
  (G : τ (Functor Terminal_cat B))
  [W X : τ (Obj A)]
  (g : τ (Hom B
      (@fapp0 A B F X)
      (@fapp0 Terminal_cat B G Terminal_obj)))
  (p : τ (Hom A W X))
  : τ (@=
      (Hom B
        (@fapp0 A B F W)
        (@fapp0 Terminal_cat B G Terminal_obj))
      (@fapp0
        (Hom_cat A W X)
        (Hom_cat B
          (@fapp0 A B F W)
          (@fapp0 Terminal_cat B G Terminal_obj))
        (@prof_terminal_expected_source_func A B F G W X g) p)
      (@prof_terminal_raw_composite_source A B F G W X g p))
≔ @eq_refl
    (Hom B
      (@fapp0 A B F W)
      (@fapp0 Terminal_cat B G Terminal_obj))
    (@fapp0
      (Hom_cat A W X)
      (Hom_cat B
        (@fapp0 A B F W)
        (@fapp0 Terminal_cat B G Terminal_obj))
      (@prof_terminal_expected_source_func A B F G W X g) p);

symbol prof_terminal_identity_expected_source_path
  [A B : Cat]
  (F : τ (Functor A B))
  (G : τ (Functor Terminal_cat B))
  [W X : τ (Obj A)]
  (g : τ (Hom B
      (@fapp0 A B F X)
      (@fapp0 Terminal_cat B G Terminal_obj)))
  (p : τ (Hom A W X))
  : τ (@=
      (Hom B
        (@fapp0 A B F W)
        (@fapp0 Terminal_cat B G Terminal_obj))
      (@prof_terminal_identity_source A B F G W X g p)
      (@fapp0
        (Hom_cat A W X)
        (Hom_cat B
          (@fapp0 A B F W)
          (@fapp0 Terminal_cat B G Terminal_obj))
        (@prof_terminal_expected_source_func A B F G W X g) p))
≔ @eq_trans
    (Hom B
      (@fapp0 A B F W)
      (@fapp0 Terminal_cat B G Terminal_obj))
    (@prof_terminal_identity_source A B F G W X g p)
    (@prof_terminal_raw_composite_source A B F G W X g p)
    (@fapp0
      (Hom_cat A W X)
      (Hom_cat B
        (@fapp0 A B F W)
        (@fapp0 Terminal_cat B G Terminal_obj))
      (@prof_terminal_expected_source_func A B F G W X g) p)
    (@prof_terminal_identity_raw_composite_path A B F G W X g p)
    (@eq_sym
      (Hom B
        (@fapp0 A B F W)
        (@fapp0 Terminal_cat B G Terminal_obj))
      (@fapp0
        (Hom_cat A W X)
        (Hom_cat B
          (@fapp0 A B F W)
          (@fapp0 Terminal_cat B G Terminal_obj))
        (@prof_terminal_expected_source_func A B F G W X g) p)
      (@prof_terminal_raw_composite_source A B F G W X g p)
      (@prof_terminal_expected_raw_composite_path A B F G W X g p));

symbol prof_terminal_retained_expected_source_fapp0_path
  [A B : Cat]
  (F : τ (Functor A B))
  (G : τ (Functor Terminal_cat B))
  [W X : τ (Obj A)]
  (g : τ (Hom B
      (@fapp0 A B F X)
      (@fapp0 Terminal_cat B G Terminal_obj)))
  (normal : τ (@=
      (Hom B
        (@fapp0 Terminal_cat B G Terminal_obj)
        (@fapp0 Terminal_cat B G Terminal_obj))
      (@prof_terminal_terminal_action B G)
      (@id B (@fapp0 Terminal_cat B G Terminal_obj))))
  (p : τ (Hom A W X))
  : τ (@=
      (Hom B
        (@fapp0 A B F W)
        (@fapp0 Terminal_cat B G Terminal_obj))
      (@fapp0
        (Hom_cat A W X)
        (Hom_cat B
          (@fapp0 A B F W)
          (@fapp0 Terminal_cat B G Terminal_obj))
        (@prof_terminal_retained_source_func A B F G W X g) p)
      (@fapp0
        (Hom_cat A W X)
        (Hom_cat B
          (@fapp0 A B F W)
          (@fapp0 Terminal_cat B G Terminal_obj))
        (@prof_terminal_expected_source_func A B F G W X g) p))
≔ @eq_trans
    (Hom B
      (@fapp0 A B F W)
      (@fapp0 Terminal_cat B G Terminal_obj))
    (@fapp0
      (Hom_cat A W X)
      (Hom_cat B
        (@fapp0 A B F W)
        (@fapp0 Terminal_cat B G Terminal_obj))
      (@prof_terminal_retained_source_func A B F G W X g) p)
    (@prof_terminal_identity_source A B F G W X g p)
    (@fapp0
      (Hom_cat A W X)
      (Hom_cat B
        (@fapp0 A B F W)
        (@fapp0 Terminal_cat B G Terminal_obj))
      (@prof_terminal_expected_source_func A B F G W X g) p)
    (@prof_terminal_retained_identity_source_path
      A B F G W X g normal p)
    (@prof_terminal_identity_expected_source_path
      A B F G W X g p);

// Whole directed source comparison.  Its component beta below is the
// generic version of the join-cross endpoint conjugation; tapp1 retains the
// next coherence without postulating a commuting square.
injective symbol prof_terminal_expected_retained_source_transf
  [A B : Cat]
  (F : τ (Functor A B))
  (G : τ (Functor Terminal_cat B))
  [W X : τ (Obj A)]
  (g : τ (Hom B
      (@fapp0 A B F X)
      (@fapp0 Terminal_cat B G Terminal_obj)))
  (normal : τ (@=
      (Hom B
        (@fapp0 Terminal_cat B G Terminal_obj)
        (@fapp0 Terminal_cat B G Terminal_obj))
      (@prof_terminal_terminal_action B G)
      (@id B (@fapp0 Terminal_cat B G Terminal_obj))))
  : τ (Transf
      (@prof_terminal_expected_source_func A B F G W X g)
      (@prof_terminal_retained_source_func A B F G W X g));

// lhs-audit: keep 1,2 -- exact hom source/codomain guard this component.
rule @tapp0_fapp0
      (Hom_cat $A $W $X)
      (Hom_cat $B
        (@fapp0 $A $B $F $W)
        (@fapp0 Terminal_cat $B $G Terminal_obj))
      _ _ $p
      (@prof_terminal_expected_retained_source_transf
        $A $B $F $G $W $X $g $normal)
  ↪ @path_to_hom
      (Hom_cat $B
        (@fapp0 $A $B $F $W)
        (@fapp0 Terminal_cat $B $G Terminal_obj))
      (@fapp0
        (Hom_cat $A $W $X)
        (Hom_cat $B
          (@fapp0 $A $B $F $W)
          (@fapp0 Terminal_cat $B $G Terminal_obj))
        (@prof_terminal_expected_source_func $A $B $F $G $W $X $g) $p)
      (@fapp0
        (Hom_cat $A $W $X)
        (Hom_cat $B
          (@fapp0 $A $B $F $W)
          (@fapp0 Terminal_cat $B $G Terminal_obj))
        (@prof_terminal_retained_source_func $A $B $F $G $W $X $g) $p)
      (@eq_sym
        (Hom $B
          (@fapp0 $A $B $F $W)
          (@fapp0 Terminal_cat $B $G Terminal_obj))
        (@fapp0
          (Hom_cat $A $W $X)
          (Hom_cat $B
            (@fapp0 $A $B $F $W)
            (@fapp0 Terminal_cat $B $G Terminal_obj))
          (@prof_terminal_retained_source_func $A $B $F $G $W $X $g) $p)
        (@fapp0
          (Hom_cat $A $W $X)
          (Hom_cat $B
            (@fapp0 $A $B $F $W)
            (@fapp0 Terminal_cat $B $G Terminal_obj))
          (@prof_terminal_expected_source_func $A $B $F $G $W $X $g) $p)
        (@prof_terminal_retained_expected_source_fapp0_path
          $A $B $F $G $W $X $g $normal $p));

symbol prof_terminal_fibre_normalization_func
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
  (p : τ (Hom A W X))
  : τ (Functor
      (Fibre_cat
        (@prof_terminal_native_action_catd A B F G W X g h) p)
      (Fibre_cat
        (@prof_terminal_expected_action_catd A B F G W X g h) p))
≔ @Hom_func
    (Hom_cat B
      (@fapp0 A B F W)
      (@fapp0 Terminal_cat B G Terminal_obj))
    (@fapp0
      (Hom_cat A W X)
      (Hom_cat B
        (@fapp0 A B F W)
        (@fapp0 Terminal_cat B G Terminal_obj))
      (@prof_terminal_retained_source_func A B F G W X g) p)
    (@fapp0
      (Hom_cat A W X)
      (Hom_cat B
        (@fapp0 A B F W)
        (@fapp0 Terminal_cat B G Terminal_obj))
      (@prof_terminal_expected_source_func A B F G W X g) p)
    h h
    (@tapp0_fapp0
      (Hom_cat A W X)
      (Hom_cat B
        (@fapp0 A B F W)
        (@fapp0 Terminal_cat B G Terminal_obj))
      (@prof_terminal_expected_source_func A B F G W X g)
      (@prof_terminal_retained_source_func A B F G W X g)
      p
      (@prof_terminal_expected_retained_source_transf
        A B F G W X g normal))
    (@id
      (Hom_cat B
        (@fapp0 A B F W)
        (@fapp0 Terminal_cat B G Terminal_obj))
      h);

// Whole coherent normalizer.  Only its fibre component is exposed below;
// generic Functord action retains every higher cell.
injective symbol prof_terminal_explicit_normalization_funcd
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
      (@prof_terminal_expected_action_catd A B F G W X g h));

// Fibre-component beta for the explicit whole normalizer.
// lhs-audit: keep 1,2 -- the exact opposite-hom base and Cat codomain are the
// subject-reduction guards for this displayed component projection.
rule @tapp0_fapp0
      (Op_cat (Hom_cat $A $W $X))
      Cat_cat
      _
      _
      $p
      (@prof_terminal_explicit_normalization_funcd
        $A $B $F $G $W $X $g $h $normal)
  ↪ @prof_terminal_fibre_normalization_func
      $A $B $F $G $W $X $g $h $normal $p;

// -------------------------------------------------------------------------------------------------
// Whole constructor-visible source normalization
// -------------------------------------------------------------------------------------------------
/*
  The expected source above presents p |-> g o F[p] by precomposition.  The
  constructor-visible presentation first applies the whole hom action of F
  and then postcomposes by g.  These are intentionally distinct whole functor
  owners: only their object actions are propositionally equal.  The stable
  displayed reflag below uses that component path and retains its higher
  naturality through the ordinary Functord action.

  This is the reusable bridge from a computational Pi section to literal
  dependent-triangle endpoints.  It contains no simplex dimension, face code,
  broad source collapse, whole-functor equality, or proof-time unifier.
*/

// Whole constructor-visible source p |-> g o F[p].
symbol prof_terminal_visible_source_func
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
    (Hom_cat B (@fapp0 A B F W) (@fapp0 A B F X))
    (Hom_cat B
      (@fapp0 A B F W)
      (@fapp0 Terminal_cat B G Terminal_obj))
    (@hom_postcomp_func
      B B (@id_func B)
      (@fapp0 A B F W)
      (@fapp0 A B F X)
      (@fapp0 Terminal_cat B G Terminal_obj)
      g)
    (@fapp1_func A B F W X);

// Constructor-visible component of the whole source functor.
symbol prof_terminal_visible_source_obj
  [A B : Cat]
  (F : τ (Functor A B))
  (G : τ (Functor Terminal_cat B))
  [W X : τ (Obj A)]
  (g : τ (Hom B
      (@fapp0 A B F X)
      (@fapp0 Terminal_cat B G Terminal_obj)))
  (p : τ (Hom A W X))
  : τ (Hom B
      (@fapp0 A B F W)
      (@fapp0 Terminal_cat B G Terminal_obj))
≔ @fapp0
    (Hom_cat A W X)
    (Hom_cat B
      (@fapp0 A B F W)
      (@fapp0 Terminal_cat B G Terminal_obj))
    (@prof_terminal_visible_source_func A B F G W X g) p;

// Pointwise equality between expected and constructor-visible source views.
symbol prof_terminal_expected_visible_source_fapp0_path
  [A B : Cat]
  (F : τ (Functor A B))
  (G : τ (Functor Terminal_cat B))
  [W X : τ (Obj A)]
  (g : τ (Hom B
      (@fapp0 A B F X)
      (@fapp0 Terminal_cat B G Terminal_obj)))
  (p : τ (Hom A W X))
  : τ (@=
      (Hom B
        (@fapp0 A B F W)
        (@fapp0 Terminal_cat B G Terminal_obj))
      (@fapp0
        (Hom_cat A W X)
        (Hom_cat B
          (@fapp0 A B F W)
          (@fapp0 Terminal_cat B G Terminal_obj))
        (@prof_terminal_expected_source_func A B F G W X g) p)
      (@prof_terminal_visible_source_obj A B F G W X g p))
≔ @eq_trans
    (Hom B
      (@fapp0 A B F W)
      (@fapp0 Terminal_cat B G Terminal_obj))
    (@fapp0
      (Hom_cat A W X)
      (Hom_cat B
        (@fapp0 A B F W)
        (@fapp0 Terminal_cat B G Terminal_obj))
      (@prof_terminal_expected_source_func A B F G W X g) p)
    (@prof_terminal_raw_composite_source A B F G W X g p)
    (@prof_terminal_visible_source_obj A B F G W X g p)
    (@prof_terminal_expected_raw_composite_path A B F G W X g p)
    (@eq_sym
      (Hom B
        (@fapp0 A B F W)
        (@fapp0 Terminal_cat B G Terminal_obj))
      (@prof_terminal_visible_source_obj A B F G W X g p)
      (@prof_terminal_raw_composite_source A B F G W X g p)
      (@eq_refl
        (Hom B
          (@fapp0 A B F W)
          (@fapp0 Terminal_cat B G Terminal_obj))
        (@prof_terminal_visible_source_obj A B F G W X g p)));

// Constructor-visible dependent-hom family with fixed target h.
symbol prof_terminal_visible_action_catd
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
      (@prof_terminal_visible_source_func A B F G W X g));

// Equality-induced rigid Hom action at one visible source component.
symbol prof_terminal_expected_visible_fibre_func
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
  (p : τ (Hom A W X))
  : τ (Functor
      (Fibre_cat
        (@prof_terminal_expected_action_catd A B F G W X g h) p)
      (Fibre_cat
        (@prof_terminal_visible_action_catd A B F G W X g h) p))
≔ @Hom_func
    (Hom_cat B
      (@fapp0 A B F W)
      (@fapp0 Terminal_cat B G Terminal_obj))
    (@fapp0
      (Hom_cat A W X)
      (Hom_cat B
        (@fapp0 A B F W)
        (@fapp0 Terminal_cat B G Terminal_obj))
      (@prof_terminal_expected_source_func A B F G W X g)
      p)
    (@prof_terminal_visible_source_obj A B F G W X g p)
    h h
    (@path_to_hom
      (Hom_cat B
        (@fapp0 A B F W)
        (@fapp0 Terminal_cat B G Terminal_obj))
      (@prof_terminal_visible_source_obj A B F G W X g p)
      (@fapp0
        (Hom_cat A W X)
        (Hom_cat B
          (@fapp0 A B F W)
          (@fapp0 Terminal_cat B G Terminal_obj))
        (@prof_terminal_expected_source_func A B F G W X g)
        p)
      (@eq_sym
        (Hom B
          (@fapp0 A B F W)
          (@fapp0 Terminal_cat B G Terminal_obj))
        (@fapp0
          (Hom_cat A W X)
          (Hom_cat B
            (@fapp0 A B F W)
            (@fapp0 Terminal_cat B G Terminal_obj))
          (@prof_terminal_expected_source_func A B F G W X g)
          p)
        (@prof_terminal_visible_source_obj A B F G W X g p)
        (@prof_terminal_expected_visible_source_fapp0_path
          A B F G W X g p)))
    (@id
      (Hom_cat B
        (@fapp0 A B F W)
        (@fapp0 Terminal_cat B G Terminal_obj))
      h);

// Whole expected-to-visible reflag.  Its stable head, not a whole equality,
// owns naturality between the two source presentations.
injective symbol prof_terminal_expected_visible_funcd
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
  : τ (Functord
      (@prof_terminal_expected_action_catd A B F G W X g h)
      (@prof_terminal_visible_action_catd A B F G W X g h));

// Fibre component is the equality-induced rigid Hom reflag.  Generic
// Functord action supplies its base-arrow and higher-cell coherence.
// lhs-audit: keep 1,2 -- exact opposite-hom base and Cat codomain are the
// subject-reduction guards for this displayed component projection.
rule @tapp0_fapp0
      (Op_cat (Hom_cat $A $W $X))
      Cat_cat
      _ _
      $p
      (@prof_terminal_expected_visible_funcd
        $A $B $F $G $W $X $g $h)
  ↪ @prof_terminal_expected_visible_fibre_func
      $A $B $F $G $W $X $g $h $p;
