 There is no Lambdapi reason for most of that vertical style. It was mostly useful while debugging: one argument per
  line makes hidden arity, stable-head discriminators, and failing conversion goals easier to inspect.

  I think a cleanup pass is worth doing, but not as a blind formatter.

  Recommended style:

  rule @tdapp1_int_cell $K $E $D $FF $FF (@id_transfd $K $E $D $FF) $x $y $p $u
    ↪ @fdapp1_int_cell $K $E $D $FF $x $y $p $u;

  Prefer mostly horizontal for:

  - simple rewrite rules with only variables and one stable head;
  - identity/specialization fold rules;
  - short symbol declarations;
  - projection rules where the head is obvious.

  Keep vertical for:

  - nested Hom_cat, Functor_cat, Fibre_cat, Sigma_cat, Product_cat endpoints;
  - long dependent symbol types;
  - rules where source/target categories are deliberately explicit;
  - RHSs with nested composition or transport where vertical structure reflects the proof/computation path;
  - any diagnostic assertion where readability of canonical endpoints matters more than compactness.

  So yes: a presentation cleanup pass is reasonable. I would do it section-by-section, probably starting with
  sections 15-17 where many rules are vertically expanded, and run EMDASH_TYPECHECK_TIMEOUT=60s make check after each
  batch.