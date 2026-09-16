/* The outgoing diagram of an original raw chain pair.
   This observation performs no universal selection. */
require open emdash.emdash3_2_chain_pair_data;
require open emdash.emdash3_2_walking_arrow_introduction;

// The original outgoing differential, introduced through the existing shape.
symbol chain_pair_outgoing_diagram [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  : τ (Functor WalkingArrow_cat C)
≔ @walking_arrow_func C B D (@computational_chain_pair_d C S A B D pair);
