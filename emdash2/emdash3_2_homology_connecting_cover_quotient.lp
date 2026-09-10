/*
  The original connecting cover followed by the retained homology quotient
  is epic. This shared proof supplies cancellation, not an inverse or a
  new choice of cover/quotient.
*/
require open emdash.emdash3_2_homology_connecting_cover;
require open emdash.emdash3_2_homology_record_cancellation;

symbol homology_connecting_cover_quotient_epic [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X Y Z : τ (Obj C)]
  (row : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A B Y))
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) X Y Z))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X
    Y Z pair))
  : τ (@IsEpic C (@homology_connecting_cover_object C P t Ab A B X Y Z row pair H) (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z pair H)
    (@comp_fapp0 C (@homology_connecting_cover_object C P t Ab A B X Y Z row pair H) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z pair H)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) X Y Z pair H) (@homology_record_projection C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) X Y Z pair H) (@homology_connecting_cover_projection C P t Ab A B X
    Y Z row pair H)))
≔ @is_epic_comp C (@homology_connecting_cover_object C P t Ab A B X Y Z row pair H) (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z pair H)
  (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  X Y Z pair H) (@homology_connecting_cover_projection C P t Ab A B X Y Z row pair H) (@homology_record_projection C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z pair H)
    (@homology_connecting_cover_epic C P t Ab A B X Y Z row pair H)
    (@homology_record_projection_epic C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
      C P t Ab)) X Y Z pair H);

symbol homology_connecting_cover_quotient_extensionality [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj
  C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X Y Z : τ (Obj C)]
  (row : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A B Y))
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) X Y Z))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X
    Y Z pair))
  (D : τ (Obj C)) (u v : τ (Hom C (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) X Y Z pair H) D))
  (p : τ (@= (Hom C (@homology_connecting_cover_object C P t Ab A B X Y Z row pair H) D)
    (@comp_fapp0 C (@homology_connecting_cover_object C P t Ab A B X Y Z row pair H) (@homology_record_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z pair H) D u
      (@comp_fapp0 C (@homology_connecting_cover_object C P t Ab A B X Y Z row pair H) (@homology_record_cycle_object
      C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z pair H)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
      Ab)) X Y Z pair H) (@homology_record_projection C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) X Y Z pair H) (@homology_connecting_cover_projection C P t Ab A B
      X Y Z row pair H)))
    (@comp_fapp0 C (@homology_connecting_cover_object C P t Ab A B X Y Z row pair H) (@homology_record_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z pair H) D v
      (@comp_fapp0 C (@homology_connecting_cover_object C P t Ab A B X Y Z row pair H) (@homology_record_cycle_object
      C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z pair H)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
      Ab)) X Y Z pair H) (@homology_record_projection C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) X Y Z pair H) (@homology_connecting_cover_projection C P t Ab A B
      X Y Z row pair H)))))
  : τ (@= (Hom C (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) X Y Z pair H) D) u v)
≔ (@homology_connecting_cover_quotient_epic C P t Ab A B X Y Z row pair H) D u v p;
