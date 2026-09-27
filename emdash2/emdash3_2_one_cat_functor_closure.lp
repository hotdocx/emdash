/* Existing main structural closure, relocated here for the temporary
   dependency-ready ordinary profile layer; not a new model obligation. */
require open emdash.emdash3_2;

constant symbol one_cat_functor_category [B C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  : τ (IsNCat (cat_succ cat_zero) (Functor_cat B C));
