/* The profile belongs to the actual codomain composition, not every facade
   with convertible Hom types. The existing Psh composition path stays explicit. */
require open emdash.emdash3_2_gray_profiles;
require open emdash.emdash3_2_presheaves;

assertnot [A K : Cat] [F G H : τ (Functor A (@Psh_cat K))]
  (epsilon : τ (@Transf A (@Psh_cat K) F G))
  (V : τ (@LaxTransfor A (@Psh_cat K) G H))
  [X Y : τ (Obj A)] (f : τ (Hom A X Y)) ⊢
  (@comp_fapp0 (@Catd_cat (Op_cat K))
    (@fapp0 A (@Psh_cat K) F X) (@fapp0 A (@Psh_cat K) G Y) (@fapp0 A (@Psh_cat K) H Y)
    (@tapp0_fapp0 A (@Psh_cat K) G H Y (@lax_transfor A (@Psh_cat K) G H V))
    (@tapp1_fapp0 A (@Psh_cat K) F G X Y epsilon f))
  ≡ @tapp1_fapp0 A (@Psh_cat K) F H X Y
      (@comp_fapp0 (Functor_cat A (@Psh_cat K)) F G H
        (@lax_transfor A (@Psh_cat K) G H V) epsilon) f;
