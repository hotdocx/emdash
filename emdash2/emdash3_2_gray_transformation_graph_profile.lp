/*
  Emdash v3.2: selected strict-profile closure of transformation graphs.

  If F and G already have StrictFunctorData codes, then a transformation
  epsilon:F=>G has a selected strict graph code

    B -> LaxArrow_cat(C).

  The stable strict decoder computes directly to the public graph from the
  preceding module. The graph-specific strictness rules still recognize that
  public head and reduce only its already-extracted identity filler and binary
  compositor. This is the profile closure needed by recursive Gray currying;
  it does not classify arbitrary ambient graphs as strict or add a second
  graph semantics. The existing ReadablePseudoFunctorProfile is a separate
  fixed-forward OmegaEquivAlong capability indexed by an already-formed
  carrier.
*/

require open emdash.emdash3_2_gray_cubes;

// Transformation graphs preserve the selected strict endpoint profile.
injective symbol strict_gray_transf_graph_data
  [B C : Cat]
  (SF SG : τ (@StrictFunctorData B C))
  (epsilon : τ (Transf
    (@strict_functor_carrier B C SF)
    (@strict_functor_carrier B C SG)))
  : τ (@StrictFunctorData B (@LaxArrow_cat C));

// Whole computational decoder at the true strict-code owner.
rule @strict_functor_carrier _ _
      (@strict_gray_transf_graph_data $B $C $SF $SG $epsilon)
  ↪ @gray_transf_graph_func
      $B $C
      (@strict_functor_carrier $B $C $SF)
      (@strict_functor_carrier $B $C $SG)
      $epsilon;

/*
  Selected unit/normality computation at the existing internal-action cell.
  For a transformation between strict-coded endpoint diagrams, the identity
  component of its post/left laxity is the identity on epsilon[x]. This is the
  filler already used by `gray_transf_standard_square(epsilon,id_x)`; no graph
  unit or second naturality cell is introduced.
*/
rule @fdapp1_int_cell
      $B
      _
      _
      (@tapp1_at_transf
        $B $C
        (@strict_functor_carrier $B $C $SF)
        (@strict_functor_carrier $B $C $SG)
        $x $epsilon)
      $x $x (@id $B $x) (@id $B $x)
  ↪ @id
      (Hom_cat
        $C
        (@fapp0 $B $C (@strict_functor_carrier $B $C $SF) $x)
        (@fapp0 $B $C (@strict_functor_carrier $B $C $SG) $x))
      (@tapp0_fapp0
        $B $C
        (@strict_functor_carrier $B $C $SF)
        (@strict_functor_carrier $B $C $SG)
        $x $epsilon);

/*
  Selected strict compositor computation after whole carrier decoding.
  This is the existing `fdapp1_int_cell`/`fapp1_compositor` owner specialized
  to the graph of a transformation between strict-coded endpoint diagrams; it
  does not introduce a second graph compositor.

  The source/target displayed families are inferred from the visible graph
  action. Keeping them as `_` prevents reducible `LaxArrow_cat` and hom-family
  aliases from hiding the actual discriminator.
*/
rule @fdapp1_int_cell
      $B
      _
      _
      (@fapp1_at_transf
        $B _
        (@gray_transf_graph_func
          $B $C
          (@strict_functor_carrier $B $C $SF)
          (@strict_functor_carrier $B $C $SG)
          $epsilon)
        $X)
      $Y $Z $g $f
  ↪ @id
      (Hom_cat
        (@LaxArrow_cat $C)
        (@fapp0
          $B (@LaxArrow_cat $C)
          (@gray_transf_graph_func
            $B $C
            (@strict_functor_carrier $B $C $SF)
            (@strict_functor_carrier $B $C $SG)
            $epsilon)
          $X)
        (@fapp0
          $B (@LaxArrow_cat $C)
          (@gray_transf_graph_func
            $B $C
            (@strict_functor_carrier $B $C $SF)
            (@strict_functor_carrier $B $C $SG)
            $epsilon)
          $Z))
      (@strict_functor_compositor_lhs
        $B
        (@LaxArrow_cat $C)
        (@gray_transf_graph_func
          $B $C
          (@strict_functor_carrier $B $C $SF)
          (@strict_functor_carrier $B $C $SG)
          $epsilon)
        $X $Y $Z $g $f);
