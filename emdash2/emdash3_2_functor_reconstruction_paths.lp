/* Derived ordinary map reflection from a whole natural isomorphism.
   The given isomorphism compares one endofunctor with the identity.
   No mapwise injectivity or component naturality is supplied separately.
   Ordinary-target naturality uses the explicit A1 hypothesis. Component
   inverses retain the original whole DefIso through stable evaluation. */
require open emdash.emdash3_2_one_cat_action_paths;
require open emdash.emdash3_2_defiso_evaluation_ordinary_paths;

symbol functor_reconstruction_iso_at [A : Cat] (R : τ (Functor A A))
  (I : τ (@DefIso (Functor_cat A A) R (@id_func A)))
  (x : τ (Obj A))
  : τ (@DefIso A (@fapp0 A A R x) x)
≔ @defiso_at A A R (@id_func A) I x;

// Conjugating the image of p by the actual comparison returns p.
symbol functor_reconstruction_map_path [A : Cat]
  (A1 : τ (IsNCat (cat_succ cat_zero) A)) (R : τ (Functor A A))
  (I : τ (@DefIso (Functor_cat A A) R (@id_func A)))
  [x y : τ (Obj A)] (p : τ (Hom A x y))
  : τ (@= (Hom A x y) p (@comp_fapp0 A x (@fapp0 A A R x) y (@comp_fapp0 A (@fapp0 A A R x) (@fapp0 A A R y) y (@defiso_to A (@fapp0 A A R y) y (@functor_reconstruction_iso_at A R I y)) (@fapp1_fapp0 A A R x y p)) (@defiso_from A (@fapp0 A A R x) x (@functor_reconstruction_iso_at A R I x))))
≔ @eq_trans (Hom A x y) _ _ _
    (@eq_sym _ _ _ (@eq_ap (Hom A x x) (Hom A x y)
      (λ v : τ (Hom A x x), @comp_fapp0 A x x y p v) _ _
      (@iso_evidence_right A (@fapp0 A A R x) x
        (@defiso_iso_evidence A (@fapp0 A A R x) x (@functor_reconstruction_iso_at A R I x)))))
    (@eq_trans (Hom A x y) _ _ _
      (@comp_assoc A x (@fapp0 A A R x) x y p (@defiso_to A (@fapp0 A A R x) x (@functor_reconstruction_iso_at A R I x)) (@defiso_from A (@fapp0 A A R x) x (@functor_reconstruction_iso_at A R I x)))
      (@eq_ap (Hom A (@fapp0 A A R x) y) (Hom A x y)
        (λ v : τ (Hom A (@fapp0 A A R x) y), @comp_fapp0 A x (@fapp0 A A R x) y v (@defiso_from A (@fapp0 A A R x) x (@functor_reconstruction_iso_at A R I x))) _ _
        (@defiso_at_to_naturality_path A A A1 R (@id_func A) I x y p)));

// Apply the same whole comparison to both images; naturality reflects equality.
symbol functor_reconstruction_reflect_path [A : Cat]
  (A1 : τ (IsNCat (cat_succ cat_zero) A)) (R : τ (Functor A A))
  (I : τ (@DefIso (Functor_cat A A) R (@id_func A)))
  [x y : τ (Obj A)] (p q : τ (Hom A x y))
  (e : τ (@= (Hom A (@fapp0 A A R x) (@fapp0 A A R y)) (@fapp1_fapp0 A A R x y p) (@fapp1_fapp0 A A R x y q)))
  : τ (@= (Hom A x y) p q)
≔ @eq_trans (Hom A x y) _ _ _
    (@functor_reconstruction_map_path A A1 R I x y p)
    (@eq_trans (Hom A x y) _ _ _
      (@eq_ap (Hom A (@fapp0 A A R x) (@fapp0 A A R y)) (Hom A x y)
        (λ v : τ (Hom A (@fapp0 A A R x) (@fapp0 A A R y)), (@comp_fapp0 A x (@fapp0 A A R x) y (@comp_fapp0 A (@fapp0 A A R x) (@fapp0 A A R y) y (@defiso_to A (@fapp0 A A R y) y (@functor_reconstruction_iso_at A R I y)) v) (@defiso_from A (@fapp0 A A R x) x (@functor_reconstruction_iso_at A R I x)))) _ _ e)
      (@eq_sym _ _ _ (@functor_reconstruction_map_path A A1 R I x y q)));

// A left inverse up to a whole natural isomorphism makes F faithful.
symbol functor_reconstruction_along_reflect_path
  [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
  (F : τ (Functor A B)) (G : τ (Functor B A))
  (I : τ (@DefIso (Functor_cat A A)
    (@comp_cat_fapp0 A B A G F) (@id_func A)))
  [x y : τ (Obj A)] (p q : τ (Hom A x y))
  (e : τ (@= (Hom B (@fapp0 A B F x) (@fapp0 A B F y))
    (@fapp1_fapp0 A B F x y p) (@fapp1_fapp0 A B F x y q)))
  : τ (@= (Hom A x y) p q)
≔ @functor_reconstruction_reflect_path A A1 (@comp_cat_fapp0 A B A G F) I x y p q
    (@eq_ap (Hom B (@fapp0 A B F x) (@fapp0 A B F y))
      (Hom A (@fapp0 B A G (@fapp0 A B F x)) (@fapp0 B A G (@fapp0 A B F y)))
      (λ v : τ (Hom B (@fapp0 A B F x) (@fapp0 A B F y)),
        @fapp1_fapp0 B A G (@fapp0 A B F x) (@fapp0 A B F y) v) _ _ e);
