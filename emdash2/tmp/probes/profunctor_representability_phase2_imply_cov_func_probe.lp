require open emdash.emdash3_2;

// Fixed-weight covariant implication as a functor in its first argument.
symbol Probe_Prof_imply_cov_func [A B X : Cat]
  (Q : τ (Prof B X))
  : τ (Functor
      (Prof_cat A X)
      (Prof_cat A B));

rule fapp0
      (@Probe_Prof_imply_cov_func $A $B $X $Q)
      $O
  ↪ @Prof_imply_cov $A $B $X $O $Q;

// Full hom-action of the fixed-weight implication functor.
symbol Probe_Prof_imply_cov_func_fapp1_func
  [A B X : Cat]
  (Q : τ (Prof B X))
  [O O' : τ (Prof A X)]
  : τ (Functor
      (@Functord_cat
        (Product_cat (Op_cat A) X)
        O O')
      (@Functord_cat
        (Product_cat (Op_cat A) B)
        (@Prof_imply_cov A B X O Q)
        (@Prof_imply_cov A B X O' Q)));

symbol Probe_Prof_imply_cov_func_transf
  [A B X : Cat]
  (Q : τ (Prof B X))
  [O O' : τ (Prof A X)]
  (o : τ (Functord O O'))
  : τ (Functord
      (@Prof_imply_cov A B X O Q)
      (@Prof_imply_cov A B X O' Q));

// Rewrite-capable mirror of the active mixed-variance constructor. This tests
// changing the active declaration from `constant symbol` to `symbol`.
symbol Probe_Prof_imply_cov_transf
  [A A' B B' X : Cat]
  [O : τ (Prof A X)]
  [O' : τ (Prof A' X)]
  [Q : τ (Prof B X)]
  [Q' : τ (Prof B' X)]
  [F : τ (Functor A A')]
  [M : τ (Functor B' B)]
  (o : τ (Obj (@Prof_transf_cat A' A X X O F O' (@id_func X))))
  (q : τ (Obj (@Prof_transf_cat B B' X X Q' M Q (@id_func X))))
  : τ (Obj
      (@Prof_transf_cat
        A' A B' B'
        (@Prof_reindex
          A A B B'
          (@Prof_imply_cov A B X O Q)
          (@id_func A)
          M)
        F
        (@Prof_imply_cov A' B' X O' Q')
        (@id_func B')));

rule fapp1_func
      (@Probe_Prof_imply_cov_func $A $B $X $Q)
      [$O] [$O']
  ↪ @Probe_Prof_imply_cov_func_fapp1_func
      $A $B $X $Q $O $O';

rule fapp0
      (@Probe_Prof_imply_cov_func_fapp1_func
        $A $B $X $Q $O $O')
      $o
  ↪ @Probe_Prof_imply_cov_func_transf
      $A $B $X $Q $O $O' $o;

rule fapp1_fapp0
      (@Probe_Prof_imply_cov_func $A $B $X $Q)
      [$O] [$O'] $o
  ↪ @Probe_Prof_imply_cov_func_transf
      $A $B $X $Q $O $O' $o;

// Unary functor laws.
rule @Probe_Prof_imply_cov_func_transf
      $A $B $X $Q
      $O $O
      (@id_funcd _ $O)
  ↪ @id_funcd
      (Product_cat (Op_cat $A) $B)
      (@Prof_imply_cov $A $B $X $O $Q);

rule @Probe_Prof_imply_cov_func_transf
      $A $B $X $Q
      $O $O''
      (@comp_catd_fapp0
        _
        $O $O' $O''
        $o' $o)
  ↪ @comp_catd_fapp0
      (Product_cat (Op_cat $A) $B)
      (@Prof_imply_cov $A $B $X $O $Q)
      (@Prof_imply_cov $A $B $X $O' $Q)
      (@Prof_imply_cov $A $B $X $O'' $Q)
      (@Probe_Prof_imply_cov_func_transf
        $A $B $X $Q $O' $O'' $o')
      (@Probe_Prof_imply_cov_func_transf
        $A $B $X $Q $O $O' $o);

// Reindexing a unary implication map reindexes both its varying input and its
// fixed weight, matching object-level implication reindexing.
rule @Prof_reindex_transf
      $A $A'
      $B $B'
      (@Prof_imply_cov $A $B $X $O $Q)
      (@Prof_imply_cov $A $B $X $O' $Q)
      (@Probe_Prof_imply_cov_func_transf
        $A $B $X $Q $O $O' $o)
      $F $M
  ↪ @Probe_Prof_imply_cov_func_transf
      $A' $B' $X
      (@Prof_reindex
        $B $B' $X $X
        $Q $M (@id_func $X))
      (@Prof_reindex
        $A $A' $X $X
        $O $F (@id_func $X))
      (@Prof_reindex
        $A $A' $X $X
        $O' $F (@id_func $X))
      (@Prof_reindex_transf
        $A $A' $X $X
        $O $O' $o
        $F (@id_func $X));

// The identity-endpoint specialization of the mixed-variance action is the
// unary fixed-weight action.
rule @Probe_Prof_imply_cov_transf
      $A $A $B $B $X
      $O $O' $Q $Q
      (@id_func $A)
      (@id_func $B)
      $o
      (@Prof_id_transf $B $X $Q)
  ↪ @Probe_Prof_imply_cov_func_transf
      $A $B $X $Q $O $O' $o;

assert [A B X : Cat]
  (Q : τ (Prof B X))
  (O : τ (Prof A X)) ⊢
  @fapp0
    (@Prof_cat A X)
    (@Prof_cat A B)
    (@Probe_Prof_imply_cov_func A B X Q)
    O
  ≡ @Prof_imply_cov A B X O Q;

assert [A B X : Cat]
  (Q : τ (Prof B X))
  [O O' : τ (Prof A X)]
  (o : τ (Functord O O')) ⊢
  @fapp1_fapp0
    (@Prof_cat A X)
    (@Prof_cat A B)
    (@Probe_Prof_imply_cov_func A B X Q)
    O O' o
  ≡ @Probe_Prof_imply_cov_func_transf
      A B X Q O O' o;

assert [A B X : Cat]
  (Q : τ (Prof B X))
  (O : τ (Prof A X)) ⊢
  @Probe_Prof_imply_cov_func_transf
    A B X Q O O
    (@id_funcd (Product_cat (Op_cat A) X) O)
  ≡ @id_funcd
      (Product_cat (Op_cat A) B)
      (@Prof_imply_cov A B X O Q);

assert [A B X : Cat]
  (Q : τ (Prof B X))
  [O O' O'' : τ (Prof A X)]
  (o : τ (Functord O O'))
  (o' : τ (Functord O' O'')) ⊢
  @Probe_Prof_imply_cov_func_transf
    A B X Q O O''
    (@comp_catd_fapp0
      (Product_cat (Op_cat A) X)
      O O' O'' o' o)
  ≡ @comp_catd_fapp0
      (Product_cat (Op_cat A) B)
      (@Prof_imply_cov A B X O Q)
      (@Prof_imply_cov A B X O' Q)
      (@Prof_imply_cov A B X O'' Q)
      (@Probe_Prof_imply_cov_func_transf
        A B X Q O' O'' o')
      (@Probe_Prof_imply_cov_func_transf
        A B X Q O O' o);

assert [A A' B B' X : Cat]
  (Q : τ (Prof B X))
  [O O' : τ (Prof A X)]
  (o : τ (Functord O O'))
  (F : τ (Functor A' A))
  (M : τ (Functor B' B)) ⊢
  @Prof_reindex_transf
    A A' B B'
    (@Prof_imply_cov A B X O Q)
    (@Prof_imply_cov A B X O' Q)
    (@Probe_Prof_imply_cov_func_transf
      A B X Q O O' o)
    F M
  ≡ @Probe_Prof_imply_cov_func_transf
      A' B' X
      (@Prof_reindex
        B B' X X
        Q M (@id_func X))
      (@Prof_reindex
        A A' X X
        O F (@id_func X))
      (@Prof_reindex
        A A' X X
        O' F (@id_func X))
      (@Prof_reindex_transf
        A A' X X
        O O' o
        F (@id_func X));

assert [A B X : Cat]
  (Q : τ (Prof B X))
  [O O' : τ (Prof A X)]
  (o : τ (Functord O O')) ⊢
  @Probe_Prof_imply_cov_transf
    A A B B X
    O O' Q Q
    (@id_func A)
    (@id_func B)
    o
    (@Prof_id_transf B X Q)
  ≡ @Probe_Prof_imply_cov_func_transf
      A B X Q O O' o;
