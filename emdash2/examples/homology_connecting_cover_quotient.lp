/* Actual epicity and cancellation at the retained cover and quotient. */
require open emdash.emdash3_2_homology_connecting_cover_quotient;

assert [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X Y Z : τ (Obj C)]
  (row : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A B Y))
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) X Y Z))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X
    Y Z pair)) ⊢
  @homology_connecting_cover_quotient_epic C P t Ab A B X Y Z row pair H
  : τ (@IsEpic C (@homology_connecting_cover_object C P t Ab A B X Y Z row pair H) (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z pair H)
    (@comp_fapp0 C (@homology_connecting_cover_object C P t Ab A B X Y Z row pair H) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z pair H)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) X Y Z pair H) (@homology_record_projection C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) X Y Z pair H) (@homology_connecting_cover_projection C P t Ab A B X
    Y Z row pair H)));

assert [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X Y Z : τ (Obj C)]
  (row : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A B Y))
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) X Y Z))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X
    Y Z pair)) (D : τ (Obj C)) (u v : τ (Hom C (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) X Y Z pair H) D)) (p : τ (@= (Hom C
    (@homology_connecting_cover_object C P t Ab A B X Y Z row pair H) D) (@comp_fapp0 C
    (@homology_connecting_cover_object C P t Ab A B X Y Z row pair H) (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z pair H) D u
    (@comp_fapp0 C (@homology_connecting_cover_object C P t Ab A B X Y Z row pair H) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z pair H)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) X Y Z pair H) (@homology_record_projection C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) X Y Z pair H) (@homology_connecting_cover_projection C P t Ab A B X
    Y Z row pair H))) (@comp_fapp0 C (@homology_connecting_cover_object C P t Ab A B X Y Z row pair H)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) X Y Z pair H) D v (@comp_fapp0 C (@homology_connecting_cover_object C P t Ab A B X Y Z row pair H)
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) X Y Z pair H) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) X Y Z pair H) (@homology_record_projection C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z pair H)
    (@homology_connecting_cover_projection C P t Ab A B X Y Z row pair H))))) ⊢
  @homology_connecting_cover_quotient_extensionality C P t Ab A B X Y Z row pair H D u v p
  : τ (@= (Hom C (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) X Y Z pair H) D) u v);

// The equality of the covered maps is a necessary input to this theorem.
assertnot [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X Y Z : τ (Obj C)]
  (row : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A B Y))
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) X Y Z))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X
    Y Z pair)) (D : τ (Obj C)) (u v : τ (Hom C (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) X Y Z pair H) D)) ⊢
  @homology_connecting_cover_quotient_extensionality C P t Ab A B X Y Z row pair H D u v
  : τ (@= (Hom C (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) X Y Z pair H) D) u v);
