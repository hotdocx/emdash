require open emdash.emdash3_2;

// Semantic representable embedding:
//   G |-> uncurry (b |-> Hom_B(b,G-)).
symbol Probe_Hom_prof_func_body [J B : Cat]
  : τ (Functor
      (Functor_cat J B)
      (Prof_cat B J))
≔ @comp_cat_fapp0
    (Functor_cat J B)
    (Functor_cat
      (Op_cat B)
      (Functor_cat J Cat_cat))
    (@Catd_cat (Product_cat (Op_cat B) J))
    (@uncurry_func_func (Op_cat B) J Cat_cat)
    (@comp_cat_fapp0
      (Functor_cat J B)
      (Functor_cat
        (Functor_cat B Cat_cat)
        (Functor_cat J Cat_cat))
      (Functor_cat
        (Op_cat B)
        (Functor_cat J Cat_cat))
      (@comp_cat_con_func
        (Op_cat B)
        (Functor_cat B Cat_cat)
        (Functor_cat J Cat_cat)
        (@hom_int B B (@id_func B)))
      (@comp_cat_con_func_func J B Cat_cat));

// Keep the semantic definition as provenance while exposing a stable object
// normal form. Generic fapp1 rules remain the sole functoriality owner.
opaque Probe_Hom_prof_func_body;

rule fapp0 (@Probe_Hom_prof_func_body $J $B) $G
  ↪ @Hom_prof $J $B $G;

// Canonical Catd specialization of the global strict-functor composition cut.
rule @comp_catd_fapp0
      $K
      _ _ _
      (@fapp1_fapp0
        $A (@Catd_cat $K) $F $Y $Z $g)
      (@fapp1_fapp0
        $A (@Catd_cat $K) $F $X $Y $f)
  ↪ @fapp1_fapp0
      $A
      (@Catd_cat $K)
      $F
      $X
      $Z
      (@comp_fapp0 $A $X $Y $Z $g $f);

// Fibre component of the representable embedding's arrow action. This routes
// through ordinary postcomposition of eta by Hom_B(b,-); its local arrow
// action is already owned by hom_postcomp_tele_func.
rule @tapp0_fapp0
      (Product_cat (Op_cat $B) $J)
      Cat_cat
      _
      _
      $bj
      (@fapp1_fapp0
        (Functor_cat $J $B)
        (@Catd_cat (Product_cat (Op_cat $B) $J))
        (@Probe_Hom_prof_func_body $J $B)
        $G $H $eta)
  ↪ @tapp0_fapp0
      $J
      Cat_cat
      (@comp_cat_fapp0
        $J $B Cat_cat
        (@hom_ $B $B (@id_func $B) (sigma_Fst $bj))
        $G)
      (@comp_cat_fapp0
        $J $B Cat_cat
        (@hom_ $B $B (@id_func $B) (sigma_Fst $bj))
        $H)
      (sigma_Snd $bj)
      (@comp_cat_cov_transf
        $J $B Cat_cat
        (@hom_ $B $B (@id_func $B) (sigma_Fst $bj))
        $G $H $eta);

assert [A K : Cat]
  (F : τ (Functor A (@Catd_cat K)))
  [X Y Z : τ (Obj A)]
  (f : τ (Hom A X Y))
  (g : τ (Hom A Y Z)) ⊢
  @comp_catd_fapp0
    K
    (@fapp0 A (@Catd_cat K) F X)
    (@fapp0 A (@Catd_cat K) F Y)
    (@fapp0 A (@Catd_cat K) F Z)
    (@fapp1_fapp0 A (@Catd_cat K) F Y Z g)
    (@fapp1_fapp0 A (@Catd_cat K) F X Y f)
  ≡ @fapp1_fapp0
      A (@Catd_cat K) F X Z
      (@comp_fapp0 A X Y Z g f);

assert [J B : Cat] ⊢
  @Probe_Hom_prof_func_body J B
  : τ (Functor
      (Functor_cat J B)
      (Prof_cat B J));

assert [J B : Cat]
  (G : τ (Functor J B)) ⊢
  fapp0 (@Probe_Hom_prof_func_body J B) G
  ≡ @Hom_prof J B G;

// Strict identity is inherited from the global functor rule.
assert [J B : Cat]
  (G : τ (Functor J B)) ⊢
  @fapp1_fapp0
    (Functor_cat J B)
    (Prof_cat B J)
    (@Probe_Hom_prof_func_body J B)
    G G
    (@id (Functor_cat J B) G)
  ≡ @id
      (Prof_cat B J)
      (@Hom_prof J B G);

assert [J B : Cat]
  [G H : τ (Functor J B)]
  (eta : τ (Transf G H))
  (b : τ (Obj B))
  (j : τ (Obj J)) ⊢
  @tapp0_fapp0
    (Product_cat (Op_cat B) J)
    Cat_cat
    (@Hom_prof J B G)
    (@Hom_prof J B H)
    (Struct_sigma b j)
    (@fapp1_fapp0
      (Functor_cat J B)
      (@Catd_cat (Product_cat (Op_cat B) J))
      (@Probe_Hom_prof_func_body J B)
      G H eta)
  ≡ @hom_postcomp_func
      B B (@id_func B) b
      (@fapp0 J B G j)
      (@fapp0 J B H j)
      (@tapp0_fapp0 J B G H j eta);

// Strict composition is inherited from the global functor rule.
assert [J B : Cat]
  [G H K : τ (Functor J B)]
  (eta : τ (Transf H K))
  (epsilon : τ (Transf G H)) ⊢
  @comp_fapp0
    (Prof_cat B J)
    (fapp0 (@Probe_Hom_prof_func_body J B) G)
    (fapp0 (@Probe_Hom_prof_func_body J B) H)
    (fapp0 (@Probe_Hom_prof_func_body J B) K)
    (@fapp1_fapp0
      (Functor_cat J B)
      (@Catd_cat (Product_cat (Op_cat B) J))
      (@Probe_Hom_prof_func_body J B)
      H K eta)
    (@fapp1_fapp0
      (Functor_cat J B)
      (@Catd_cat (Product_cat (Op_cat B) J))
      (@Probe_Hom_prof_func_body J B)
      G H epsilon)
  ≡ @fapp1_fapp0
      (Functor_cat J B)
      (@Catd_cat (Product_cat (Op_cat B) J))
      (@Probe_Hom_prof_func_body J B)
      G K
      (@comp_fapp0
        (Functor_cat J B)
        G H K eta epsilon);
