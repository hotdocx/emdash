# EMDASH v3.2 DefIso, Hom-Action, And ProfComparison Migration Plan

Date: 2026-06-28
Last reviewed: 2026-06-28
Plan-ID: EMDASH-V3.2-DEFISO-HOM-ACTION-PROFCOMP-MIGRATION-2026-06-28
Depends-On: EMDASH-V3-2-GROUPOID-COMPUTATIONAL-UNIVALENCE-2026-06-23
Supersedes: none
Side-Task-Ledger: none
Infinity-Codex-Origin: infinity-codex:019ef47a-919d-77b3-93f9-7af7a7848c73:019f0838-53c1-79a0-832c-654983859441
Infinity-Codex-Decision-Responses: infinity-codex:019ef47a-919d-77b3-93f9-7af7a7848c73:019f0838-53c1-79a0-832c-654983859441
Status: active incremental migration plan; Phases 1-3, Phase 5, and the
adjunction-mate DefIso owner correction promoted

Parent plan:
`REPORT_EMDASH_V3_2_GROUPOID_COMPUTATIONAL_UNIVALENCE_IMPLEMENTATION_PLAN_2026-06-23.md`,
especially the `UNI-DEFISO` / Phase 5 task that replaces the old generic
`HomComparison` direction by `DefIso` and eventually factors
`ProfComparison` through it.

Related plans:

- `REPORT_EMDASH_V3_2_PROFUNCTOR_REPRESENTABILITY_REDESIGN_PRELIM_PLAN_2026-06-19.md`
- `REPORT_EMDASH_V3_2_PROFUNCTOR_WEIGHTED_LIMITS_PRELIM_PLAN_2026-06-17.md`
- `REPORT_EMDASH_V3_2_EQUIPMENT_SHADOW_TENSOR_JOIN_REDESIGN_PLAN_2026-06-28.md`
- `REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`

The normalized Infinity Codex header fields record the immediate predecessor
decision context used when this report was written from the active code and
active plan state on 2026-06-28.

## Purpose

This report isolates a subtask that grew out of the groupoid/computational
univalence plan:

```text
ProfComparison / prof_comparison_* migration
  -> DefIso(Prof_cat(A,B),P,Q)
  -> stable hom-action cut-elimination
```

The immediate problem is not just profunctors. The current implementation is
mixing several layers:

1. runtime cut-elimination heads such as `hom_postcomp_fapp0` and
   `hom_precomp_along_fapp0`;
2. proof-time semantic comparison with ordinary composition through
   `comp_fapp0` and `comp_cat_fapp0`;
3. identity-specialized readable heads such as `Rep_transport_func`;
4. Cat-specialized heads such as `comp_cat_cov_transf` and
   `comp_cat_con_transf` that expose transfor structure unavailable in a
   generic category.

The goal is a globally coherent design that can be implemented in phases
without destabilizing the active profunctor and path-induction consumers.

## Current File Map

The relevant active source areas are:

```text
emdash3_2.lp

section 4:
  hom_
  hom_postcomp_tele_func
  hom_postcomp_func
  hom_postcomp_fapp0
  hom_precomp_along_tele_func
  hom_precomp_along_func
  hom_precomp_along_fapp0
  hom_con
  hom_int

Cat composition layer:
  comp_cat_fapp0
  comp_cat_cov_func
  comp_cat_cov_func_func
  comp_cat_con_func
  comp_cat_con_func_func
  comp_cat_cov_transf
  comp_cat_con_transf
  comp_cat_cov_func_func_transf
  comp_cat_con_func_func_transf

representable layer:
  Rep_catd_func
  Rep_catd
  Rep_transport_func
  CompTarget_catd
  path_comp_func

profunctor comparison layer:
  ProfComparison
  prof_comparison_to/from
  prof_comparison_push/pull
  prof_comparison_push_func/pull_func
```

Observed current facts:

- `hom_(F,W)` has both a direct object-action rule and a stable projection
  ladder:

  ```text
  fapp1_func(hom_(F,W))    -> hom_postcomp_tele_func(F,W)
  fapp1_fapp0(hom_(F,W),f) -> hom_postcomp_func(F,W,f)
  fapp0(hom_postcomp_func(F,W,f),g)
    -> hom_postcomp_fapp0(F,W,f,g)
  ```

- `hom_int(F)` currently has only:

  ```text
  fapp0(hom_int(F),W) -> hom_(F,W)
  tapp0_fapp0(fapp1_fapp0(hom_int(F),p),b)
    -> hom_precomp_along_func(id_A,F[b],p)
  ```

  and an identity-specialized fold:

  ```text
  fapp1_fapp0(hom_int(id_Z),p) -> Rep_transport_func(p).
  ```

- `Rep_transport_func` is currently primitive/stable and is used on rewrite
  LHSs by strict/cartesian representable computations.

- `prof_comparison_push_func` and `prof_comparison_pull_func` have already
  been routed through `hom_postcomp_func(id, prof_comparison_to/from)`, but
  the old `ProfComparison` pointwise push/pull API remains active.

## Design Principles

### 1. Runtime owners and proof-time semantic views are different

Runtime/cut-elimination heads should preserve the computational owner that a
later cancellation rule needs:

```text
hom_postcomp_fapp0(F,W,h,g)
hom_precomp_along_fapp0(F,Z,h,g)
hom_int_precomp_func(F,p)          // proposed
DefIso cancellation under hom_postcomp_fapp0
```

Ordinary composition remains the semantic view:

```text
comp_fapp0(h,g)
comp_cat_fapp0(G,F)
```

When both presentations are intended to elaborate against one another but no
runtime orientation is intended, use a narrow `unif_rule`, validated by typed
`eq_refl` checks rather than by conversion-only assertions.

### 2. Stable hom-action heads must carry their functoriality joins

Once a generic functor action is routed through a stable head, the stable head
must not hide functoriality of the original functor. For example,
`hom_(F,W)` still has to behave functorially in the base arrow.

Therefore the stable postcomposition package needs at least the identity and
composition joins:

```text
hom_postcomp_func(F,W,id_X) -> id_func
hom_postcomp_fapp0(F,W,id_X,g) -> g

hom_postcomp_func(F,W,q ∘ p)
  -> hom_postcomp_func(F,W,q) ∘ hom_postcomp_func(F,W,p)

hom_postcomp_fapp0(F,W,q ∘ p,g)
  -> hom_postcomp_fapp0(F,W,q, hom_postcomp_fapp0(F,W,p,g)).
```

The precomposition package has the dual obligations:

```text
hom_precomp_along_func(F,Z,id_X) -> id_func
hom_precomp_along_fapp0(F,Z,id_X,g) -> g

hom_precomp_along_func(F,Z,q ∘ p)
  -> hom_precomp_along_func(F,Z,p) ∘ hom_precomp_along_func(F,Z,q)

hom_precomp_along_fapp0(F,Z,q ∘ p,g)
  -> hom_precomp_along_fapp0(F,Z,p, hom_precomp_along_fapp0(F,Z,q,g)).
```

These should be probed as a coherent package. Adding only one identity rule or
one composition rule can create asymmetric normal forms.

### 3. General `hom_postcomp_fapp0` proof-time bridge

The current identity-functor bridge is too narrow:

```text
hom_postcomp_fapp0(id_A,h,g) ≡ comp_fapp0(h,g).
```

The intended proof-time bridge is general in the functor argument:

```text
unif_rule @hom_postcomp_fapp0 $A $B $F $W $X $Y $h $g
  ≡ @comp_fapp0
      $A
      $W
      (@fapp0 $B $A $F $X)
      (@fapp0 $B $A $F $Y)
      (@fapp1_fapp0 $B $A $F $X $Y $h)
      $g
  ↪ [ tt ≡ tt ];
```

This matches the already-correct precomposition bridge:

```text
hom_precomp_along_fapp0(F,Z,h,g)
  ≡ comp_fapp0(g,F[h]).
```

### 4. `hom_int` needs a generic action owner

`Rep_transport_func` should not be the generic name for the action of
`hom_int`. The generic owner should be something like:

```text
hom_int_precomp_func(A,B,F,x,y,p)
  : Functord(hom_(F,y), hom_(F,x)).
```

Expected projection ladder:

```text
fapp1_func(hom_int(F))
  -> hom_int_precomp_tele_func(F)

fapp1_fapp0(hom_int(F),p)
  -> hom_int_precomp_func(F,p)

tapp0_fapp0(hom_int_precomp_func(F,p),b)
  -> hom_precomp_along_func(id_A,F[b],p).
```

Then `Rep_transport_func` becomes a compatibility/readability alias:

```text
Rep_transport_func(Z,x,y,p)
  := hom_int_precomp_func(Z,Z,id_Z,x,y,p).
```

Important migration rule: once this alias is introduced, rewrite rules whose
LHS currently discriminates on `Rep_transport_func` should be migrated to
discriminate on:

```text
hom_int_precomp_func(Z,Z,id_Z,x,y,p).
```

This avoids using a transparent alias as a runtime discriminator and follows
the SOP preference to put rules at the real semantic owner.

### 5. Cat-specialized symbols should be justified by extra Cat structure

Final design should avoid duplicating every generic `hom_*` and `comp_*`
operation under explicit `Cat_cat` names.

The current Cat-specialized names fall into two classes.

Class A: object-action packaging only.

```text
comp_cat_cov_func
comp_cat_cov_func_func
comp_cat_con_func
comp_cat_con_func_func
```

These primarily curry/uncurry ordinary Cat composition. Long-term they should
be candidates for transparent definitions/aliases around generic
`comp_cat_fapp0`/generic functor action, unless a concrete LHS needs them as
stable heads. If they become aliases, rules should use their unfolded semantic
owner on the LHS.

Class B: Cat-specific higher structure.

```text
comp_cat_cov_transf
comp_cat_con_transf
comp_cat_cov_func_func_transf
comp_cat_con_func_func_transf
comp_cat_cov_func_func_tapp1_func
comp_cat_cov_func_func_tapp1_fapp0
```

These expose `tapp0_fapp0`, `tapp1_func`, and `tapp1_fapp0` structure that is
not available for an arbitrary category. They are legitimate stable heads
when they are the owner of transfor components or horizontal composites.

The long-term criterion is:

```text
Keep a Cat-specialized primitive head only if it owns Cat-only structure.
Demote pure object-action/currying convenience heads to aliases where feasible.
```

### 6. Symmetry of covariant/contravariant Cat object-action heads

The current implementation should not add `comp_cat_cov_fapp0` and
`comp_cat_con_fapp0` as extra runtime heads just to mirror
`hom_postcomp_fapp0` and `hom_precomp_along_fapp0`. A previous probe showed
that separate cov/con object-action heads immediately need a join because
both denote the same `G ∘ F`.

However, this is an incremental implementation constraint, not a final
mathematical asymmetry. A final uniform redesign has two coherent options:

1. Keep `comp_cat_fapp0` as the single Cat object-action owner and treat
   cov/con object-action forms as aliases/views.
2. Introduce cov/con object-action heads only together with a canonical
   orientation and explicit joins, after auditing all consumers.

Current recommendation: choose option 1 for the v3.2 migration. It preserves a
single runtime normal form for Cat composition while still allowing
Cat-specific transfor heads where additional structure exists.

## DefIso Layer

`DefIso(C,x,y)` is a Lambdapi-specific strict/computational isomorphism
notion. It is stronger than `IsoEvidence`: `IsoEvidence` contains arrows and
propositional/path inverse proofs, while `DefIso` is meant to provide
judgmental cancellation under stable hom-action owners.

The active core should remain:

```text
DefIso(C,x,y)
defiso_to(i)   : Hom_C(x,y)
defiso_from(i) : Hom_C(y,x)
```

Runtime cancellation is owned by postcomposition:

```text
hom_postcomp_fapp0(F,defiso_from(i),
  hom_postcomp_fapp0(F,defiso_to(i),f))
↪ f

hom_postcomp_fapp0(F,defiso_to(i),
  hom_postcomp_fapp0(F,defiso_from(i),g))
↪ g.
```

Selected-arrow cancellation is also part of the strict certificate:

```text
hom_postcomp_fapp0(id_C,defiso_from(i),defiso_to(i)) ↪ id_x
hom_postcomp_fapp0(id_C,defiso_to(i),defiso_from(i)) ↪ id_y.
```

These DefIso-specific rules should not be confused with ordinary category
identity/functoriality rules. They are the computational content of the
strict isomorphism certificate.

## ProfComparison Migration Target

Current `ProfComparison(A,B,P,Q)` owns:

```text
prof_comparison_to
prof_comparison_from
prof_comparison_push
prof_comparison_pull
prof_comparison_push_func
prof_comparison_pull_func
prof_comparison_evidence
```

The target architecture is:

```text
ProfComparison(A,B,P,Q)
  becomes a wrapper/alias/compatibility layer over
DefIso(Prof_cat(A,B),P,Q).
```

The eventual selected arrows should be:

```text
prof_comparison_to(i)   := defiso_to(i')
prof_comparison_from(i) := defiso_from(i')
```

and the functorial push/pull wrappers should be ordinary postcomposition by
those selected arrows:

```text
prof_comparison_push_func(i,R)
  := hom_postcomp_func(id_(Prof_cat(A,B)),R,P,Q,defiso_to(i'))

prof_comparison_pull_func(i,R)
  := hom_postcomp_func(id_(Prof_cat(A,B)),R,Q,P,defiso_from(i')).
```

Pointwise push/pull can remain temporarily for legacy weighted-limit
consumers. They should eventually become compatibility wrappers, not a
competing computational owner.

## Migration Phases

### Phase 0: Document and isolate

Status: this report.

Tasks:

1. Keep the existing groupoid/univalence report as the parent plan.
2. Use this report for the DefIso/hom-action/ProfComparison subtask.
3. Do not migrate staged implementation changes blindly; probe every normal
   form change.

### Phase 1: Correct proof-time bridges and remove diagnostic noise

Tasks:

1. Add the generalized `hom_postcomp_fapp0` bridge over `F`.
   Keep the narrow identity-only bridge temporarily; a focused probe showed
   that replacing it immediately weakens a dependent `PathOut` Sigma endpoint
   check that still elaborates through the identity-specialized view.
2. Keep the existing generalized `hom_precomp_along_fapp0` bridge.
3. Remove noisy duplicated full-transitivity `eq_refl` checks. Keep at most
   one small proof-time bridge check for the generic postcomp/precomp
   semantic view.
4. Probe removal of the focused transitivity rewrite:

   ```text
   hom_postcomp_fapp0(double-op hom_int route, id_funcd)
     -> Rep_transport_func.
   ```

   If runtime transitivity weakens, do not reintroduce a theorem-specific
   bridge as final architecture. Move to Phase 2.

Validation:

```bash
EMDASH_TYPECHECK_TIMEOUT=60s make check
```

Phase 1 implementation note, 2026-06-28:

- The additive generalized postcomposition bridge was probed successfully in
  `tmp/probes/defiso_phase1_add_general_source_probe.lp` and
  `tmp/probes/defiso_phase1_add_general_checks_probe.lp`.
- Removing the ordinary identity postcomposition rewrite rules is not Phase-1
  safe: existing `DefIso` cancellation subject-reduction still relies on those
  endpoint collapses. Revisit this only as part of the coherent Phase 3
  hom-action functoriality package.
- Replacing the identity-only `hom_postcomp_fapp0(id, h, g) ≡ comp_fapp0(h,g)`
  bridge by the generalized bridge alone is not a drop-in change. A dependent
  `PathOut` Sigma diagnostic still needs the identity-specialized bridge to
  type a pair whose first component is the ordinary `comp_fapp0` view while the
  endpoint is the stable `hom_postcomp_fapp0` view.
- The focused transitivity rewrite
  `hom_postcomp_fapp0(double-op hom_int route, id_funcd) -> Rep_transport_func`
  remains active for now. Its architectural replacement should be Phase 2's
  generic `hom_int_precomp_func` owner, not another theorem-specific bridge.
- Active validation after promotion:
  `EMDASH_TYPECHECK_TIMEOUT=60s make check` passed; `make catalog` refreshed
  the check catalog after removing five diagnostic-only assertions; `make
  warning-summary` completed with 1162 warnings, with the expected
  `hom_postcomp_fapp0` family visible in the warning inventory.

### Phase 2: Introduce generic `hom_int` precomposition owner

Tasks:

1. Add:

   ```text
   hom_int_precomp_tele_func
   hom_int_precomp_func
   ```

2. Route:

   ```text
   fapp1_func(hom_int(F))      -> hom_int_precomp_tele_func(F)
   fapp1_fapp0(hom_int(F),p)   -> hom_int_precomp_func(F,p)
   tapp0_fapp0(hom_int_precomp_func(F,p),b)
     -> hom_precomp_along_func(id_A,F[b],p)
   ```

3. Convert `Rep_transport_func` into a transparent alias:

   ```text
   Rep_transport_func(Z,x,y,p)
     := hom_int_precomp_func(Z,Z,id_Z,y,x,p).
   ```

4. Migrate LHSs currently keyed on `Rep_transport_func` to the real owner:

   ```text
   hom_int_precomp_func(Z,Z,id_Z,y,x,p).
   ```

5. Re-evaluate `path_comp_func` and transitivity checks against this generic
   owner.

Validation:

- current path-induction/transitivity checks;
- strict/cartesian representable computations currently keyed on
  `Rep_transport_func`;
- warning-enabled probe if any new overlap appears.

Phase 2 implementation note, 2026-06-28:

- Added the generic represented-object action owner:

  ```text
  hom_int_precomp_tele_func(F;Y,X)
  hom_int_precomp_func(F;Y,X,p)
  ```

  with projection rules from `fapp1_func(hom_int(F))`,
  `fapp1_fapp0(hom_int(F),p)`, and the `tapp0_fapp0` component rule.
- Converted `Rep_transport_func(Z,x,y,p)` into the transparent alias
  `hom_int_precomp_func(Z,Z,id_Z,y,x,p)`.
- Removed the old identity-specialized `fapp1_fapp0(hom_int(id),p) ->
  Rep_transport_func(p)` rule and the old `tapp0_fapp0(Rep_transport_func)`
  component rule; both are now covered by the generic owner.
- Migrated the strict/cartesian representable rules from
  `Rep_transport_func` LHSs to
  `hom_int_precomp_func(Z,Z,id_Z,y,x,p)` LHSs.
- The former focused transitivity join:

  ```text
  hom_postcomp_fapp0(Op_cat(Catd_cat Z), Z, Op_func(hom_int(id)), ..., id_funcd)
    -> hom_int_precomp_func(id,p)
  ```

  has now been removed. Its computation is recovered by the generic
  `Op_func` postcomposition-to-precomposition bridge plus precomposition
  identity normal-form rules from Phase 3.
- Added diagnostics for `fapp1_func(hom_int)`,
  `fapp1_fapp0(hom_int,p)`, the `tapp0_fapp0` component of the new owner, and
  the `Rep_transport_func` alias. A standalone
  `fapp0(hom_int_precomp_tele_func,p)` assertion was intentionally not kept:
  although the source rewrite typechecks, that diagnostic shape triggers broad
  elaboration ambiguity and adds no extra consumer coverage.
- Active validation after promotion:
  `EMDASH_TYPECHECK_TIMEOUT=60s make check` passed; `make catalog` refreshed
  the check catalog after adding the focused diagnostics; `make
  warning-summary` completed with 1159 warnings.

### Phase 3: Add coherent hom-action functoriality joins

Tasks:

1. Add postcomposition identity and composition joins as a package.
2. Add precomposition identity and composition joins as the dual package.
3. Confirm that generic `fapp1_func`/`fapp1_fapp0` functoriality and stable
   heads converge.
4. Do not add broad `comp_fapp0` accumulation unless a concrete DefIso or
   profunctor consumer requires it.

Validation:

- focused probes for identity and composition paths;
- warning-enabled comparison before promotion;
- active `make check`.

Phase 3 implementation note, 2026-06-28:

- The `hom_postcomp_*` opposite bridge family was generalized from the visible
  fully-opposite form:

  ```text
  hom_postcomp_*(Op_cat B, Op_cat A, Op_func(A,B,F), ...)
    -> hom_precomp_along_*(A,B,F,...)
  ```

  to the normal-form-sensitive `Op_func` bridge family:

  ```text
  hom_postcomp_*(B,A,Op_func(_,_,F), ...)
    -> hom_precomp_along_*(Op_cat A, Op_cat B, F, ...)
  ```

  This family covers the old fully-opposite surface and the double-op
  normalized surface where `Op_cat(Op_cat A)` has already reduced. The true
  discriminee is the `Op_func` argument; the surrounding `Op_cat` source and
  target categories are presentation wrappers, not the semantic case split.
  The promoted family covers `hom_postcomp_tele_func`,
  `hom_postcomp_func`, `hom_postcomp_fapp0`,
  `hom_postcomp_fapp1_func`, `hom_postcomp_fapp1_fapp0`,
  `hom_postcomp_tele_fapp1_func`, and
  `hom_postcomp_tele_fapp1_fapp0`.
- Precomposition by an identity arrow now has a three-rule runtime package:

  ```text
  hom_precomp_along_fapp0(F, h, id)       -> F[h]
  hom_precomp_along_fapp0(F, h, id_func)  -> F[h]
  hom_precomp_along_fapp0(F, h, id_funcd) -> F[h]
  ```

  The generic `@id` rule does not subsume the `Cat_cat/id_func` or
  `Catd_cat/id_funcd` normal forms, because those identity heads may already
  be normalized before the precomposition rule is considered.
- Diagnostics now include visible-opposite bridge checks for the telescope,
  capped functor, object action, and capped 2-cell action; a double-op
  normalized bridge check; all three precomposition identity heads; and a
  typed canonical-context check showing that the old hom-int transitivity
  shortcut computes by `eq_refl` after the expected `Catd_cat` hom type is
  fixed.
- Probe evidence:
  `tmp/probes/hom_postcomp_opfunc_general_bridge_probe.lp`,
  `tmp/probes/hom_postcomp_opfunc_general_no_precomp_id_probe.lp`, and
  `tmp/probes/hom_precomp_identity_three_rule_probe.lp`. The full-family
  generalization was validated by
  `tmp/probes/hom_postcomp_opfunc_general_full_family_probe.lp`.

### Phase 4: Cat-specialized cleanup plan

This phase is mostly architectural and can be delayed until after the DefIso
and ProfComparison migration is stable.

Tasks:

1. Classify every Cat-specialized symbol into:

   - pure object-action/currying convenience;
   - Cat-only transfor/higher-structure owner.

2. For pure object-action/currying convenience heads, probe demotion to
   transparent alias.
3. Keep stable heads that expose `tapp0_fapp0`, `tapp1_func`, or
   `tapp1_fapp0`.
4. Avoid adding `comp_cat_cov_fapp0` and `comp_cat_con_fapp0` unless the final
   design chooses a canonical cov/con object-action matrix.

Feasibility from the current scan:

- `comp_cat_cov_func` and `comp_cat_con_func` are heavily referenced, but
  their object action already reduces to `comp_cat_fapp0`. Demotion may be
  feasible only after replacing LHSs that discriminate on them.
- `comp_cat_cov_transf`, `comp_cat_con_transf`, and the `*_func_func_transf`
  family own real transfor projections and should remain stable for now.
- The large Cat-specialized hom/precomp unification rules are a symptom of
  missing or overly duplicated Cat-specialized telescope ownership; they are
  not an immediate blocker for the DefIso migration.

### Phase 5: Migrate ProfComparison to DefIso compatibility

Status as of 2026-06-28:

- Promoted in `emdash3_2.lp`.
- `ProfComparison(A,B,P,Q)` is now a transparent compatibility alias for
  `DefIso(Prof_cat(A,B),P,Q)`.
- `prof_comparison_push/pull` remain as public compatibility names, but they
  are defined wrappers through `hom_postcomp_fapp0(id,defiso_to/from,_)`.
  They no longer own primitive cancellation, incoming-map accumulation, or
  evidence rewrite rules.
- `prof_comparison_refl/sym/comp/fmap` are transparent aliases for
  `defiso_refl/sym/comp/fmap`.
- `prof_comparison_evidence` is a defined alias for `defiso_iso_evidence`.
  Whole-evidence computation for `DefIso` constructors is now owned
  generically by `defiso_iso_evidence`.
- Existing weighted-limit and right-adjoint preservation diagnostics still
  pass after migration.

Architectural correction, 2026-06-28:

- The Phase 5 promotion should be read narrowly: the public
  `ProfComparison` compatibility surface is now routed through `DefIso`, but
  the lower adjunction-mate/equipment layer is not yet fully DefIso-owned.
- In the active code before this correction,
  `defiso_to(Adjunction_hom_prof_comparison)` and
  `defiso_from(Adjunction_hom_prof_comparison)` reduced by runtime rewrite to
  the legacy primitive heads `Adjunction_prof_transpose` and
  `Adjunction_prof_untranspose`. This weakens the intended ownership: once a
  selected DefIso arrow reduces to a legacy primitive head, generic DefIso
  cancellation no longer controls the runtime normal form, and direct
  cancellation rules for the legacy heads under `Prof_comp_transf` or
  `comp_catd_fapp0` become necessary again.
- The corrected target is that `Adjunction_hom_prof_comparison` remains the
  atomic strict/DefIso certificate, while the old
  `Adjunction_prof_transpose` and `Adjunction_prof_untranspose` names are
  transparent compatibility views of the selected `defiso_to` and
  `defiso_from` arrows. If a legacy primitive name must temporarily be
  connected to a selected DefIso arrow, use proof-time compatibility
  (`unif_rule` validated by typed `eq_refl`) rather than a runtime rewrite that
  steals the normal form.
- `Prof_comp_transf` was relevant historically because the legacy mate heads
  were equipment-cell objects. It should not be the final owner of adjunction
  mate cancellation for right-adjoint weighted-limit preservation. Final
  cancellation should be inherited from DefIso/hom-action owners, with
  ordinary `IsoEvidence` obtained by `defiso_iso_evidence`.
- There are two preservation APIs for a real reason. The strict theorem
  `right_adjoint_preserves_weighted_limit_cov_comp` consumes
  `IsWeightedLimit_cov_comp` / `ProfComparison` / `DefIso`. The ordinary
  theorem `right_adjoint_preserves_weighted_limit_cov_iso` consumes only
  `IsWeightedLimit_cov_iso` / `IsoEvidence`; it cannot be derived from the
  strict theorem for an arbitrary ordinary input because there is no general
  `IsoEvidence -> DefIso`. For a strict input `isl`, however, the ordinary
  result should be exactly the evidence projection of the strict result:
  `prof_comparison_evidence(right_adjoint_preserves_weighted_limit_cov_comp
  isl adj)`.

Promoted implementation note, 2026-06-28:

- `Adjunction_hom_prof_comparison` is now declared before the legacy mate
  views and remains the atomic strict `ProfComparison` / `DefIso` owner.
- `Adjunction_hom_prof_comparison_along` is obtained by
  `prof_comparison_fmap` along `Prof_reindex_func`.
- `Adjunction_prof_transpose` and `Adjunction_prof_untranspose` are now
  transparent compatibility views of `defiso_to` and `defiso_from` applied to
  `Adjunction_hom_prof_comparison_along`.
- The runtime selected-arrow rules
  `defiso_to/from(Adjunction_hom_prof_comparison) -> Adjunction_prof_*` were
  removed.
- The adjunction-specific cancellation rules under `Prof_comp_transf` and
  direct `comp_catd_fapp0` were removed. Diagnostics now check cancellation
  through `prof_comparison_push/pull` and check ordinary inverse evidence
  through `iso_evidence_left/right`.
- `Adjunction_hom_prof_iso_evidence` and
  `Adjunction_hom_prof_iso_evidence_along` are now transparent projections of
  `defiso_iso_evidence`, so ordinary evidence follows from the strict
  certificate rather than being independently assembled from legacy mate
  heads.

Runtime universal-property note, 2026-06-28:

- The nested hom-action cancellation shape
  `from . (to . f) -> f` and `to . (from . g) -> g` is the intended runtime
  owner for weighted-limit beta/eta. Weighted-limit universal properties act
  on arbitrary incoming maps into the represented classifier, not only on the
  selected inverse arrows.
- Direct selected-arrow cancellation such as `from . to -> id` remains useful
  for ordinary `IsoEvidence`, but it is not enough as the primary runtime
  formulation without broad reassociation and identity cleanup rules. That
  broad composition surface is intentionally avoided.
- The remaining `Prof_comp_transf` users in tensor/co-Yoneda and primitive
  join are now tracked by
  `REPORT_EMDASH_V3_2_EQUIPMENT_SHADOW_TENSOR_JOIN_REDESIGN_PLAN_2026-06-28.md`.
  They are separate redesign tasks and are not prerequisites for the
  adjunction-mate DefIso owner correction already promoted here.

Implementation notes:

- `Prof_cat` is a transparent readability alias for
  `Catd_cat(Product_cat(Op_cat A) B)`. New rewrite rules must not use
  `Prof_cat` as a semantic discriminator. Where a category argument is a real
  guard, use the canonical expanded `Catd_cat(Product_cat(...))` form or avoid
  category-head discrimination entirely.
- The successful migration needed `defiso_iso_evidence` to become a stable
  evidence owner with projection rules. Keeping it as a transparent Sigma
  definition did not leave a stable head for constructor-specific evidence
  computation.
- `defiso_fmap` selected-arrow rules now keep endpoint arguments as `_ _`;
  the endpoints are reconstructible and often reduce through stable functor
  projections before the DefIso rule sees them.
- The atomic adjunction mate comparison should own the selected arrows. Legacy
  mate names may remain as transparent compatibility views, but selected-arrow
  runtime rules from `defiso_to/from` to those names are not the intended final
  architecture.
- The weighted-limit beta checks require a stable-projection join for
  `Prof_reindex_transf` applied to `defiso_to/from`. This is the
  projection-specialized counterpart of functor-image DefIso cancellation:
  `fapp1_fapp0(Prof_reindex_func,defiso_to/from)` immediately specializes to
  `Prof_reindex_transf`, so the abstract `fapp1_fapp0` cancellation rule is
  not enough.
- A probe confirmed that adding a rule discriminating on `Prof_cat` was the
  wrong direction: it is a defined alias, and the actual fix is generic DefIso
  evidence/selected-arrow computation plus canonical Catd projection joins.

Tasks:

1. Define a bridge from `ProfComparison` to `DefIso(Prof_cat(A,B),P,Q)`, or
   redefine `ProfComparison` as a compatibility wrapper if the current
   consumers allow it.
2. Route selected arrows through `defiso_to/from`.
3. Re-express `prof_comparison_push_func/pull_func` through
   `hom_postcomp_func`.
4. Keep pointwise `prof_comparison_push/pull` temporarily if weighted-limit
   consumers still inspect those exact heads.
5. Once all consumers use hom-action/DefIso owners, demote or delete the old
   pointwise computational owner.

Task status:

- Items 1, 2, 3, and 5 are complete in the active kernel.
- Item 4 remains only as compatibility aliases: the names still exist because
  downstream code uses them, but their computation is inherited from DefIso
  and hom-action owners.
- Future cleanup can migrate consumers away from the `prof_comparison_*`
  surface and eventually delete the aliases, but this is no longer required
  for correctness of the DefIso migration.

Validation:

- existing profunctor weighted-limit checks;
- right-adjoint preservation checks;
- `ProfComparison` beta/eta checks;
- `make check`, then `make examples` if reviewer-facing examples are touched.

Promoted validation:

- `EMDASH_TYPECHECK_TIMEOUT=60s scripts/probe.sh
  tmp/probes/defiso_phase5_profcomparison_alias_source_probe.lp` passed.
- `EMDASH_TYPECHECK_TIMEOUT=60s scripts/probe.sh
  tmp/probes/defiso_phase5_profcomparison_alias_checks_probe.lp` passed.
- `EMDASH_TYPECHECK_TIMEOUT=60s make check` passed after promotion and after
  the later hom-action cleanup.
- `EMDASH_TYPECHECK_TIMEOUT=60s make ci` passed after the hom-action cleanup.
- `python3 scripts/audit_rule_lhs.py --show-kept` reports zero unreviewed
  reconstructible compound LHS slots after replacing the new
  `comp_fapp0(..., hom_postcomp_fapp0(...), ...)` target slot by `_`.
- `make warning-summary` completed after the full `Op_func` bridge cleanup
  with 1470 warnings: 1300 unjoinable critical pairs and 170 replaceable
  pattern-variable warnings. This is a net decrease from the immediately
  preceding 1501-warning state. The remaining warning families are expected
  stable-head/DefIso/hom-action confluence inventory: `defiso_iso_evidence`
  is now a stable projection owner, `hom_postcomp_fapp0` owns more DefIso
  cancellation/accumulation joins, and the hom-action identity package includes
  the `Cat_cat/id_func` and `Catd_cat/id_funcd` normal-form heads. The quiet
  kernel and diagnostics pass; the warning families should be treated as
  follow-up confluence inventory, not as a veto on the promoted runtime normal
  forms.
- `examples/path_induction_transitivity.lp` was updated to match the active
  transitivity benchmark: runtime computation now targets
  `hom_postcomp_fapp0(id,q,p)`, while a typed `eq_refl` witness records the
  proof-time ordinary-composition view against `comp_fapp0(q,p)`.

## Open Questions

1. Should ordinary hom-action identity/composition joins be runtime rewrites
   or proof-time unification rules?

   Current leaning: runtime for stable hom-action functoriality, because the
   stable heads replaced generic `fapp1_*` reductions and therefore own
   runtime cut-elimination.

2. Should `Rep_transport_func` be deleted after becoming an alias?

   Current leaning: keep the public name as a transparent readability alias
   for a while, but do not use it as a rewrite discriminator after Phase 2.

3. Should final Cat object-action symmetry introduce cov/con fapp0 heads?

   Current leaning for v3.2: no. Keep `comp_cat_fapp0` as the unique runtime
   object-action owner. Revisit only after the Cat-specialized cleanup audit.

4. How much of `ProfComparison` should remain after DefIso migration?

   Current leaning: keep it as a compatibility surface until all
   weighted-limit and representability consumers are rewritten against
   `DefIso` or generic hom-action owners.

## Success Criteria

The migration is complete when:

```text
hom_postcomp_fapp0 / hom_precomp_along_fapp0 have coherent semantic bridges;
hom_int has a generic precomposition action owner;
Rep_transport_func is a compatibility alias, not a primitive discriminator;
hom-action functoriality joins are stable and checked;
ProfComparison push/pull is factored through DefIso and hom_postcomp_func;
old ProfComparison pointwise computation is retained only as compatibility or removed;
Cat-specialized stable heads are limited to Cat-only higher/transfor structure;
make check passes.
```
