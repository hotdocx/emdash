/* Recovered consumer-specific candidate. Only a composite led by Eval
   opens under displayed Hom action; no unrestricted Op_funcd-composition
   bridge or covariant-universe op action is introduced. NON-LIBRARY: this is an append-only
   recovery candidate, not a promoted kernel rule set. Owner-position warning
   and inferred-slot qualification remain required before promotion. */
require open emdash.emdash3_2;

/* Only a known leading evaluation operator opens a displayed composite.
   Arbitrary composition and mapped-arrow accumulation remain untouched. */

rule @fdapp1_int_hom_func _ _ _ (@comp_fapp0 (Catd_cat $K) $R $P $E (@Eval_funcd $K $I $E) $FF)
      $x $y $p $u $v
  ↪ @comp_cat_fapp0 (@fapp0 (Op_cat (Hom_cat $K $x $y)) Cat_cat
        (@homd_ $K $R $R (@id_funcd $K $R) $x $u $y $v) $p) (@fapp0 (Op_cat (Hom_cat $K $x $y)) Cat_cat
        (@homd_ $K $R $P $FF $x (@fapp0 (Fibre_cat $R $x) (Fibre_cat $P $x)
        (@Fibre_func $K $R $P $FF $x) $u) $y $v) $p) (@fapp0 (Op_cat (Hom_cat $K $x $y)) Cat_cat
        (@homd_ $K $P $E (@Eval_funcd $K $I $E) $x
          (@fapp0 (Fibre_cat $P $x) (Fibre_cat $E $x)
            (@Fibre_func $K $P $E (@Eval_funcd $K $I $E) $x) (@fapp0 (Fibre_cat $R $x) (Fibre_cat $P $x)
        (@Fibre_func $K $R $P $FF $x) $u)) $y (@fapp0 (Fibre_cat $R $y) (Fibre_cat $P $y)
        (@Fibre_func $K $R $P $FF $y) $v)) $p)
      (@fdapp1_int_hom_func $K $P $E (@Eval_funcd $K $I $E) $x $y $p (@fapp0 (Fibre_cat $R $x) (Fibre_cat $P $x)
        (@Fibre_func $K $R $P $FF $x) $u) (@fapp0 (Fibre_cat $R $y) (Fibre_cat $P $y)
        (@Fibre_func $K $R $P $FF $y) $v))
      (@fdapp1_int_hom_func $K $R $P $FF $x $y $p $u $v);

rule @fdapp1_int_hom_fapp0 _ _ _ (@comp_fapp0 (Catd_cat $K) $R $P $E (@Eval_funcd $K $I $E) $FF)
      $x $y $p $u $v $alpha
  ↪ @fdapp1_int_hom_fapp0 $K $P $E (@Eval_funcd $K $I $E) $x $y $p (@fapp0 (Fibre_cat $R $x) (Fibre_cat $P $x)
        (@Fibre_func $K $R $P $FF $x) $u) (@fapp0 (Fibre_cat $R $y) (Fibre_cat $P $y)
        (@Fibre_func $K $R $P $FF $y) $v)
      (@fdapp1_int_hom_fapp0 $K $R $P $FF $x $y $p $u $v $alpha);

rule @fdapp1_int_hom_func _ _ _ (@Op_funcd _ _ _ (@comp_fapp0 (Catd_cat $K) $R $P $E (@Eval_funcd $K $I $E) $FF))
      $x $y $p $u $v
  ↪ @comp_cat_fapp0 (@fapp0 (Op_cat (Hom_cat $K $x $y)) Cat_cat
        (@homd_ $K (@Op_catd $K $R) (@Op_catd $K $R) (@id_funcd $K (@Op_catd $K $R)) $x $u $y $v) $p) (@fapp0 (Op_cat (Hom_cat $K $x $y)) Cat_cat
        (@homd_ $K (@Op_catd $K $R) (@Op_catd $K $P) (@Op_funcd $K $R $P $FF) $x (@fapp0 (Fibre_cat $R $x) (Fibre_cat $P $x)
        (@Fibre_func $K $R $P $FF $x) $u) $y $v) $p) (@fapp0 (Op_cat (Hom_cat $K $x $y)) Cat_cat
        (@homd_ $K (@Op_catd $K $P) (@Op_catd $K $E) (@Op_funcd $K $P $E (@Eval_funcd $K $I $E)) $x
          (@fapp0 (Fibre_cat (@Op_catd $K $P) $x) (Fibre_cat (@Op_catd $K $E) $x)
            (@Fibre_func $K (@Op_catd $K $P) (@Op_catd $K $E) (@Op_funcd $K $P $E (@Eval_funcd $K $I $E)) $x) (@fapp0 (Fibre_cat $R $x) (Fibre_cat $P $x)
        (@Fibre_func $K $R $P $FF $x) $u)) $y (@fapp0 (Fibre_cat $R $y) (Fibre_cat $P $y)
        (@Fibre_func $K $R $P $FF $y) $v)) $p)
      (@fdapp1_int_hom_func $K (@Op_catd $K $P) (@Op_catd $K $E) (@Op_funcd $K $P $E (@Eval_funcd $K $I $E)) $x $y $p (@fapp0 (Fibre_cat $R $x) (Fibre_cat $P $x)
        (@Fibre_func $K $R $P $FF $x) $u) (@fapp0 (Fibre_cat $R $y) (Fibre_cat $P $y)
        (@Fibre_func $K $R $P $FF $y) $v))
      (@fdapp1_int_hom_func $K (@Op_catd $K $R) (@Op_catd $K $P) (@Op_funcd $K $R $P $FF) $x $y $p $u $v);

rule @fdapp1_int_hom_fapp0 _ _ _ (@Op_funcd _ _ _ (@comp_fapp0 (Catd_cat $K) $R $P $E (@Eval_funcd $K $I $E) $FF))
      $x $y $p $u $v $alpha
  ↪ @fdapp1_int_hom_fapp0 $K (@Op_catd $K $P) (@Op_catd $K $E) (@Op_funcd $K $P $E (@Eval_funcd $K $I $E)) $x $y $p (@fapp0 (Fibre_cat $R $x) (Fibre_cat $P $x)
        (@Fibre_func $K $R $P $FF $x) $u) (@fapp0 (Fibre_cat $R $y) (Fibre_cat $P $y)
        (@Fibre_func $K $R $P $FF $y) $v)
      (@fdapp1_int_hom_fapp0 $K (@Op_catd $K $R) (@Op_catd $K $P) (@Op_funcd $K $R $P $FF) $x $y $p $u $v $alpha);

/* Evaluation's projected hom action, in both ordinary and pointwise-opposite
   presentations. The whole result remains the existing mixed Eval action. */

rule @fdapp1_int_hom_func $K _ _ (@Eval_funcd $K $I $E)
      $x $y $p (Struct_sigma $U $i) (Struct_sigma $V $j)
  ↪ @Eval_fapp1_func $I (Fibre_cat $E $y)
      (@comp_cat_fapp0 $I (Fibre_cat $E $x) (Fibre_cat $E $y)
        (@catd_transport_func $K $E $x $y $p) $U) $V $i $j;

rule @fdapp1_int_hom_fapp0 $K _ _ (@Eval_funcd $K $I $E)
      $x $y $p (Struct_sigma $U $i) (Struct_sigma $V $j)
      (Struct_sigma $eta $q)
  ↪ @tapp1_fapp0 $I (Fibre_cat $E $y)
      (@comp_cat_fapp0 $I (Fibre_cat $E $x) (Fibre_cat $E $y)
        (@catd_transport_func $K $E $x $y $p) $U) $V $i $j $eta $q;

/* Preserve the canonical opposite Hom endpoints while inferring the RHS.
   Runtime then uses ordinary Op_func and Eval hom-action projection. */

rule @fdapp1_int_hom_func $K _ _
      (@Op_funcd $K _ _ (@Eval_funcd $K $I $E))
      $x $y $p (Struct_sigma $U $i) (Struct_sigma $V $j)
  ↪ @fapp1_func (Op_cat (Product_cat (Functor_cat $I (Fibre_cat $E $y)) $I)) (Op_cat (Fibre_cat $E $y))
      (@Op_func (Product_cat (Functor_cat $I (Fibre_cat $E $y)) $I) (Fibre_cat $E $y) (@Eval_func $I (Fibre_cat $E $y)))
      (@Product_pair (Op_cat (Functor_cat $I (Fibre_cat $E $y))) (Op_cat $I)
        (@Hom_fapp0 Cat_cat $I $I (Fibre_cat $E $x) (Fibre_cat $E $y)
        (@id Cat_cat $I) (@catd_transport_func $K $E $x $y $p) $U) $i)
      (@Product_pair (Op_cat (Functor_cat $I (Fibre_cat $E $y))) (Op_cat $I) $V $j);

rule @fdapp1_int_hom_fapp0 $K _ _
      (@Op_funcd $K _ _ (@Eval_funcd $K $I $E))
      $x $y $p (Struct_sigma $U $i) (Struct_sigma $V $j) $alpha
  ↪ @fapp1_fapp0 (Op_cat (Product_cat (Functor_cat $I (Fibre_cat $E $y)) $I)) (Op_cat (Fibre_cat $E $y))
      (@Op_func (Product_cat (Functor_cat $I (Fibre_cat $E $y)) $I) (Fibre_cat $E $y) (@Eval_func $I (Fibre_cat $E $y)))
      (@Product_pair (Op_cat (Functor_cat $I (Fibre_cat $E $y))) (Op_cat $I)
        (@Hom_fapp0 Cat_cat $I $I (Fibre_cat $E $x) (Fibre_cat $E $y)
        (@id Cat_cat $I) (@catd_transport_func $K $E $x $y $p) $U) $i)
      (@Product_pair (Op_cat (Functor_cat $I (Fibre_cat $E $y))) (Op_cat $I) $V $j) $alpha;

/* Product pairing exposes its two displayed hom actions, preserving Op. */

rule @fdapp1_int_hom_func $K _ _ (@Product_pair_funcd $K $E $B $C $FF $GG)
      $x $y $p $u $v
  ↪ Struct_sigma
      (@fdapp1_int_hom_func $K $E $B $FF
        $x $y $p $u $v)
      (@fdapp1_int_hom_func $K $E $C $GG
        $x $y $p $u $v);

rule @fdapp1_int_hom_fapp0 $K _ _ (@Product_pair_funcd $K $E $B $C $FF $GG)
      $x $y $p $u $v $alpha
  ↪ Struct_sigma
      (@fdapp1_int_hom_fapp0 $K $E $B $FF
        $x $y $p $u $v $alpha)
      (@fdapp1_int_hom_fapp0 $K $E $C $GG
        $x $y $p $u $v $alpha);

rule @fdapp1_int_hom_func $K _ _ (@Op_funcd $K _ _ (@Product_pair_funcd $K $E $B $C $FF $GG))
      $x $y $p $u $v
  ↪ Struct_sigma
      (@fdapp1_int_hom_func $K (@Op_catd $K $E) (@Op_catd $K $B) (@Op_funcd $K $E $B $FF)
        $x $y $p $u $v)
      (@fdapp1_int_hom_func $K (@Op_catd $K $E) (@Op_catd $K $C) (@Op_funcd $K $E $C $GG)
        $x $y $p $u $v);

rule @fdapp1_int_hom_fapp0 $K _ _ (@Op_funcd $K _ _ (@Product_pair_funcd $K $E $B $C $FF $GG))
      $x $y $p $u $v $alpha
  ↪ Struct_sigma
      (@fdapp1_int_hom_fapp0 $K (@Op_catd $K $E) (@Op_catd $K $B) (@Op_funcd $K $E $B $FF)
        $x $y $p $u $v $alpha)
      (@fdapp1_int_hom_fapp0 $K (@Op_catd $K $E) (@Op_catd $K $C) (@Op_funcd $K $E $C $GG)
        $x $y $p $u $v $alpha);

/* Identity and the existing weakened constant section, at whole and point
   displayed-hom projections. No arbitrary section or laxity is collapsed. */

// This identity category is a measured component-projection guard: without
// it, existing tapp0/tapp1 identity rules do not establish type preservation.
rule @fdapp1_int_hom_func $K $E $E (@id (Catd_cat $K) $E)
      $x $y $p $u $v
  ↪ @id Cat_cat
      (@fapp0 (Op_cat (Hom_cat $K $x $y)) Cat_cat
        (@homd_ $K $E $E (@id_funcd $K $E) $x $u $y $v) $p);

rule @fdapp1_int_hom_fapp0 $K $E $E (@id (Catd_cat $K) $E)
      $x $y $p $u $v $alpha
  ↪ $alpha;

rule @fdapp1_int_cell $K $E $E (@id (Catd_cat $K) $E) $x $y $p $u
  ↪ @id (Fibre_cat $E $y)
      (@fapp0 (Fibre_cat $E $x) (Fibre_cat $E $y)
        (@catd_transport_func $K $E $x $y $p) $u);

rule @fdapp1_int_hom_func $K _ _ (@section_weaken_funcd $K $R (@Const_catd $K $I) (@Const_func $K $I $i))
      $x $y $p $u $v
  ↪ @Const_func
      (@fapp0 (Op_cat (Hom_cat $K $x $y)) Cat_cat
        (@homd_ $K $R $R (@id_funcd $K $R) $x $u $y $v) $p)
      (Hom_cat $I $i $i) (@id $I $i);

rule @fdapp1_int_hom_fapp0 $K _ _ (@section_weaken_funcd $K $R (@Const_catd $K $I) (@Const_func $K $I $i))
      $x $y $p $u $v $alpha
  ↪ @id $I $i;

rule @fdapp1_int_cell $K _ _ (@section_weaken_funcd $K $R (@Const_catd $K $I) (@Const_func $K $I $i)) $x $y $p $u
  ↪ @id $I $i;

rule @fdapp1_int_hom_func $K _ _ (@Op_funcd $K _ _ (@section_weaken_funcd $K $R (@Const_catd $K $I) (@Const_func $K $I $i)))
      $x $y $p $u $v
  ↪ @Const_func
      (@fapp0 (Op_cat (Hom_cat $K $x $y)) Cat_cat
        (@homd_ $K (@Op_catd $K $R) (@Op_catd $K $R) (@id_funcd $K (@Op_catd $K $R)) $x $u $y $v) $p)
      (Hom_cat (Op_cat $I) $i $i) (@id (Op_cat $I) $i);

rule @fdapp1_int_hom_fapp0 $K _ _ (@Op_funcd $K _ _ (@section_weaken_funcd $K $R (@Const_catd $K $I) (@Const_func $K $I $i)))
      $x $y $p $u $v $alpha
  ↪ @id (Op_cat $I) $i;

rule @fdapp1_int_cell $K _ _ (@Op_funcd $K _ _ (@section_weaken_funcd $K $R (@Const_catd $K $I) (@Const_func $K $I $i))) $x $y $p $u
  ↪ @id (Op_cat $I) $i;
