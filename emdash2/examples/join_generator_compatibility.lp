/* Reviewer for whole walking-generator compatibility of directed join maps. */

require open emdash.emdash3_2_join_generator_compatibility;

// Observation through the profunctor calculus and ordinary hom action remain
// distinct runtime owners.
assertnot [C : Cat] (H : τ (Functor WalkingArrow_cat C)) ⊢
  @join_map_observe_walking_generator_func C H
  ≡ @walking_generator_fapp1_func C H;

// Their comparison is one whole Terminal-indexed path; the point equation is
// obtained only by evaluation.
type λ C : Cat, λ H : τ (Functor WalkingArrow_cat C),
  @join_map_observe_walking_generator_path C H;

type λ C : Cat, λ H : τ (Functor WalkingArrow_cat C),
  @join_map_observe_walking_generator_at_path C H;

// Reindexed profunctor action likewise retains its whole component functor.
type λ A : Cat, λ A' : Cat, λ B : Cat, λ B' : Cat,
  λ R : τ (Prof A B), λ S : τ (Prof A B),
  λ r : τ (ProfMap R S),
  λ F : τ (Functor A' A), λ G : τ (Functor B' B),
  λ a : τ (Obj (Op_cat A')), λ b : τ (Obj B'),
    @prof_reindex_transf_component_path A A' B B' R S r F G a b;

// The equality-induced component cell retains another hom action.
type λ A : Cat, λ A' : Cat, λ B : Cat, λ B' : Cat,
  λ R : τ (Prof A B), λ S : τ (Prof A B),
  λ r : τ (ProfMap R S),
  λ F : τ (Functor A' A), λ G : τ (Functor B' B),
  λ a : τ (Obj (Op_cat A')), λ b : τ (Obj B'),
  λ u : τ (Obj (Fibre_cat R
    (@prof_reindex_mapped_pair A A' B B' F G a b))),
  λ v : τ (Obj (Fibre_cat R
    (@prof_reindex_mapped_pair A A' B B' F G a b))),
    @tapp1_func
      (Fibre_cat R (@prof_reindex_mapped_pair A A' B B' F G a b))
      (Fibre_cat S (@prof_reindex_mapped_pair A A' B B' F G a b))
      (@Fibre_func
        (Product_cat (Op_cat A') B')
        (@Prof_reindex A A' B B' R F G)
        (@Prof_reindex A A' B B' S F G)
        (@Prof_reindex_transf A A' B B' R S r F G)
        (@Product_pair (Op_cat A') B' a b))
      (@Fibre_func
        (Product_cat (Op_cat A) B)
        R S r
        (@prof_reindex_mapped_pair A A' B B' F G a b))
      u v
      (@prof_reindex_transf_component_cell
        A A' B B' R S r F G a b);

// The join-map generator beta is derived at the whole owner and does not make
// its endpoints runtime-convertible.
assertnot [A B : Cat]
  (F : τ (Functor Terminal_cat A))
  (G : τ (Functor Terminal_cat B)) ⊢
  @join_map_source_generator_func A B F G
  ≡ @join_map_target_generator_func A B F G;

type λ A : Cat, λ B : Cat,
  λ F : τ (Functor Terminal_cat A),
  λ G : τ (Functor Terminal_cat B),
    @join_map_generator_beta A B F G;

type λ A : Cat, λ B : Cat,
  λ F : τ (Functor Terminal_cat A),
  λ G : τ (Functor Terminal_cat B),
    @join_map_generator_at_beta A B F G;
