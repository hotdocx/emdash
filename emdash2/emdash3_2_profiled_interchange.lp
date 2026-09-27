/* The old interchange/EH derivations now expose actual action profiles.
   Core EH objects, operations and unit observations are unchanged. */
require open emdash.emdash3_2_profiled_vertical_paths;

symbol hom_postcomp_representable_interchange_eq
  [B : Cat]
  [M N L : τ (Obj B)]
  [f g h : τ (Hom B N L)]
  (e_fg : τ (Hom (Hom_cat B N L) f g))
  (e_gh : τ (Hom (Hom_cat B N L) g h))
  (PE : τ (@IsStrictTransfor (Hom_cat B M N) (Hom_cat B M L) (@hom_postcomp_func B B (@id_func B) M N L f) (@hom_postcomp_func B B (@id_func B) M N L g) (@hom_postcomp_tele_fapp1_fapp0 B B (@id_func B) M N L f g e_fg)))
  (PN : τ (@IsPreStrictTransfor (Hom_cat B M N) (Hom_cat B M L) (@hom_postcomp_func B B (@id_func B) M N L g) (@hom_postcomp_func B B (@id_func B) M N L h) (@hom_postcomp_tele_fapp1_fapp0 B B (@id_func B) M N L g h e_gh)))
  [X Y Z : τ (Hom B M N)]
  (alpha : τ (Hom (Hom_cat B M N) X Y))
  (beta : τ (Hom (Hom_cat B M N) Y Z))
  : τ (
      @comp_fapp0
        (Hom_cat B M L)
        (@hom_postcomp_fapp0 B B (@id_func B) M N L f X)
        (@hom_postcomp_fapp0 B B (@id_func B) M N L g Y)
        (@hom_postcomp_fapp0 B B (@id_func B) M N L h Z)
        (@tapp1_fapp0
          (Hom_cat B M N)
          (Hom_cat B M L)
          (@hom_postcomp_func B B (@id_func B) M N L g)
          (@hom_postcomp_func B B (@id_func B) M N L h)
          Y
          Z
          (@hom_postcomp_tele_fapp1_fapp0 B B (@id_func B) M N L g h e_gh)
          beta)
        (@tapp1_fapp0
          (Hom_cat B M N)
          (Hom_cat B M L)
          (@hom_postcomp_func B B (@id_func B) M N L f)
          (@hom_postcomp_func B B (@id_func B) M N L g)
          X
          Y
          (@hom_postcomp_tele_fapp1_fapp0 B B (@id_func B) M N L f g e_fg)
          alpha)
      =
      @tapp1_fapp0
        (Hom_cat B M N)
        (Hom_cat B M L)
        (@hom_postcomp_func B B (@id_func B) M N L f)
        (@hom_postcomp_func B B (@id_func B) M N L h)
        X
        Z
        (@hom_postcomp_tele_fapp1_fapp0
          B
          B
          (@id_func B)
          M
          N
          L
          f
          h
          (@comp_fapp0 (Hom_cat B N L) f g h e_gh e_fg))
        (@comp_fapp0 (Hom_cat B M N) X Y Z beta alpha))
≔ @profiled_vertical_both_raw_path (Hom_cat B M N) (Hom_cat B M L) (@hom_postcomp_func B B (@id_func B) M N L f) (@hom_postcomp_func B B (@id_func B) M N L g) (@hom_postcomp_func B B (@id_func B) M N L h)
    (@hom_postcomp_tele_fapp1_fapp0 B B (@id_func B) M N L f g e_fg) (@hom_postcomp_tele_fapp1_fapp0 B B (@id_func B) M N L g h e_gh) PE PN X Y Z alpha beta;

symbol EH_vcomp_to_shared_middle
  [B : Cat]
  (x : τ (Obj B))
  (alpha beta : τ (Obj (@EH_2End B x)))
  (PB : τ (@IsStrictTransfor (Hom_cat B x x) (Hom_cat B x x) (@id_func (Hom_cat B x x)) (@id_func (Hom_cat B x x)) (@hom_postcomp_tele_fapp1_fapp0 B B (@id_func B) x x x (@id B x) (@id B x) beta)))
  : τ (
      @EH_vcomp B x beta alpha
      =
      @EH_hcomp B x beta alpha)
≔ @profiled_vertical_post_raw_path (Hom_cat B x x) (Hom_cat B x x) (@id_func (Hom_cat B x x)) (@id_func (Hom_cat B x x)) (@id_func (Hom_cat B x x)) (@id (Functor_cat (Hom_cat B x x) (Hom_cat B x x)) (@id_func (Hom_cat B x x))) (@hom_postcomp_tele_fapp1_fapp0 B B (@id_func B) x x x (@id B x) (@id B x) beta) (@strict_transfor_pre_evidence (Hom_cat B x x) (Hom_cat B x x) (@id_func (Hom_cat B x x)) (@id_func (Hom_cat B x x)) (@hom_postcomp_tele_fapp1_fapp0 B B (@id_func B) x x x (@id B x) (@id B x) beta) PB) (@id B x) (@id B x) alpha;

symbol EH_swapped_vcomp_to_shared_middle
  [B : Cat]
  (x : τ (Obj B))
  (alpha beta : τ (Obj (@EH_2End B x)))
  (PB : τ (@IsStrictTransfor (Hom_cat B x x) (Hom_cat B x x) (@id_func (Hom_cat B x x)) (@id_func (Hom_cat B x x)) (@hom_postcomp_tele_fapp1_fapp0 B B (@id_func B) x x x (@id B x) (@id B x) beta)))
  : τ (
      @EH_vcomp B x alpha beta
      =
      @EH_hcomp B x beta alpha)
≔ @profiled_vertical_pre_raw_path (Hom_cat B x x) (Hom_cat B x x) (@id_func (Hom_cat B x x)) (@id_func (Hom_cat B x x)) (@id_func (Hom_cat B x x)) (@hom_postcomp_tele_fapp1_fapp0 B B (@id_func B) x x x (@id B x) (@id B x) beta) (@id (Functor_cat (Hom_cat B x x) (Hom_cat B x x)) (@id_func (Hom_cat B x x))) PB (@id B x) (@id B x) alpha;

symbol EH_comm
  [B : Cat]
  (x : τ (Obj B))
  (alpha beta : τ (Obj (@EH_2End B x)))
  (PB : τ (@IsStrictTransfor (Hom_cat B x x) (Hom_cat B x x) (@id_func (Hom_cat B x x)) (@id_func (Hom_cat B x x)) (@hom_postcomp_tele_fapp1_fapp0 B B (@id_func B) x x x (@id B x) (@id B x) beta)))
  : τ (
      @EH_vcomp B x beta alpha
      =
      @EH_vcomp B x alpha beta)
≔ @eq_trans
    (Hom (Hom_cat B x x) (@id B x) (@id B x))
    (@EH_vcomp B x beta alpha)
    (@EH_hcomp B x beta alpha)
    (@EH_vcomp B x alpha beta)
    (@EH_vcomp_to_shared_middle B x alpha beta PB)
    (eq_sym (@EH_swapped_vcomp_to_shared_middle B x alpha beta PB));
