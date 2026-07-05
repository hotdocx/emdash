# EMDASH v3.2 Cat/Catd Specialization Alias Migration Plan

Date: 2026-07-04
Last reviewed: 2026-07-05

Plan-ID: EMDASH-V3-2-CAT-CATD-SPECIALIZATION-ALIAS-MIGRATION-2026-07-04
Depends-On: EMDASH-V3.2-DEFISO-HOM-ACTION-PROFCOMP-MIGRATION-2026-06-28; EMDASH-V3-2-ECKMANN-HILTON-APPLICATION-2026-07-03; REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26
Supersedes: no whole report; refines and corrects the Cat-specialized cleanup target in section 5 of REPORT_EMDASH_V3_2_DEFISO_HOM_ACTION_PROFCOMPARISON_MIGRATION_PLAN_2026-06-28.md
Side-Task-Ledger: #side-task-ledger
Infinity-Codex-Origin: current-session-analysis-2026-07-04
Infinity-Codex-Decision-Responses: infinity-codex:019f248f-4d5f-7a71-95a2-7eb8106d6225:019f270d-b800-7611-be54-abf9ff3106de
Status: Phases 1-5 identity/composition/pure-curried-helper alias migrations,
identity-family Cat-only transfor inbound bridges, functor-level
`*_fapp1_func` wrapper demotions, and the 2026-07-05 postcomposition capped
Cat bridge/runtime cleanup promoted.  Phase 6 generalized arbitrary-base
fixed capped Cat transfor bridges and linked tele Cat projection heads are
promoted.  A 2026-07-05 follow-up generalized the fixed
`comp_cat_cov_transf` / `comp_cat_con_transf` heads themselves to the stronger
as-general-as-feasible `K,E` form with raw Cat-composition endpoints.  The
`hom_precomp_along_cat_tele_transf` off-diagonal projection ladder is now
promoted through a small dual horizontal-composite helper.

## Purpose

This report isolates the Cat/Catd specialization cleanup from the broader
DefIso, hom-action, and ProfComparison migration plan.

The corrected goal is stronger than the older "keep `comp_cat_fapp0` as the
single Cat object-action owner" wording.  The final rewrite-facing owners
should be the general, non-specialized identity/composition/hom-action heads:

```text
id
comp_fapp0
hom_postcomp_*
hom_precomp_along_*
hom_int*
homd_int*
```

The `Cat_cat` / `Catd_cat` convenience heads should remain primitive only
when the specialization exposes structure not available in a generic
category, such as ordinary transfor or displayed-transfor projection ladders.
Pure identity, composition, object-action, and currying helpers should become
transparent aliases/views over the generic owners.

## Relationship To Parent Plans

The immediate parent context is
`REPORT_EMDASH_V3_2_DEFISO_HOM_ACTION_PROFCOMPARISON_MIGRATION_PLAN_2026-06-28.md`,
especially its Section 5:

```text
Cat-specialized symbols should be justified by extra Cat structure.
```

That section correctly identifies the principle but is now too weak in one
important place: it treats `comp_cat_fapp0` as the likely single Cat
object-action owner for v3.2.  The corrected target is that
`comp_cat_fapp0` itself is a Cat-specialized presentation of generic
composition:

```text
comp_cat_fapp0(F,G)  =  comp_fapp0(Cat_cat,F,G).
```

The Eckmann-Hilton plan is orthogonal but reinforces the same direction.  Its
current promoted slices rely on generic `hom_*` accumulation and ordinary
`comp_fapp0` normal forms.  This cleanup should not be mixed into the
Eckmann-Hilton application work, but it should preserve that generic-owner
orientation.

## Current Baseline

The current active files, after the orthogonal Eckmann-Hilton work, still use
primitive Cat/Catd specialization heads:

```text
id_func
id_funcd
comp_cat_fapp0
comp_catd_fapp0
comp_cat_cov_func
comp_cat_cov_func_func
comp_cat_con_func
comp_cat_con_func_func
comp_cat_cov_fapp1_func
comp_cat_con_fapp1_func
comp_cat_cov_func_func_fapp1_func
comp_cat_con_func_func_fapp1_func
```

The source also has Cat-only higher heads that should not be demoted merely
because their names begin with `comp_cat`:

```text
comp_cat_cov_transf
comp_cat_con_transf
comp_cat_cov_func_func_transf
comp_cat_con_func_func_transf
comp_cat_cov_func_func_tapp1_func
comp_cat_func_func_tapp1_fapp0
```

The baseline check on 2026-07-04 passed:

```text
EMDASH_TYPECHECK_TIMEOUT=60s make check
```

## Architectural Decision

### 1. Treat specialized identity heads as aliases

The current primitive identity heads:

```text
id_func A
id_funcd K E
```

are convenience names for generic identity at visible specialized
categories:

```text
id_func A     := @id Cat_cat A
id_funcd K E  := @id (@Catd_cat K) E
```

The migration should delete or replace rewrite LHSs that key on
`id_func` or `id_funcd`.  Rules that are still semantically necessary should
key on the generic identity head specialized to `Cat_cat` or `Catd_cat`:

```text
@id Cat_cat A
@id (@Catd_cat K) E
```

This does not mean all identity-specific rules disappear.  Some projections
are still Cat/Catd-specific because generic categories do not have object
application or displayed components.  For example, the following kinds of
rules remain meaningful after migration, but should be written against the
generic specialized head:

```text
fapp0 (@id Cat_cat A) x
fapp1_fapp0 (@id Cat_cat A) p
tapp0_fapp0 ... (@id (@Catd_cat K) E)
```

### 2. Treat specialized composition heads as aliases

The current primitive composition heads:

```text
comp_cat_fapp0 A B C F G
comp_catd_fapp0 K E D C FF GG
```

are convenience names for generic composition at visible specialized
categories:

```text
comp_cat_fapp0 A B C F G
  := @comp_fapp0 Cat_cat A B C F G

comp_catd_fapp0 K E D C FF GG
  := @comp_fapp0 (@Catd_cat K) E D C FF GG
```

The fold rules from generic composition to specialized heads should not
survive this alias migration:

```text
@comp_fapp0 Cat_cat ...       -> comp_cat_fapp0 ...
@comp_fapp0 (Catd_cat K) ...  -> comp_catd_fapp0 ...
```

Keeping both a transparent alias and the reverse fold would create a bad
fold/unfold family.  Instead, every necessary specialized rule should be
rewritten to the generic LHS.

Examples of rules to migrate, not simply delete:

```text
fapp0 (@comp_fapp0 Cat_cat A B C F G) x
fapp1_fapp0 (@comp_fapp0 Cat_cat A B C F G) p
tapp0_fapp0 ... (@comp_fapp0 (@Catd_cat K) E D C FF GG)
```

Examples of rules to delete if the generic owner already covers them after
the alias migration:

```text
specialized identity-composition rules whose only role was
  comp_cat_fapp0(...,id_func,...) -> ...

specialized displayed identity-composition rules whose only role was
  comp_catd_fapp0(...,id_funcd,...) -> ...
```

These deletions must be probe-confirmed.  Generic identity composition may
cover more cases once `id_func` and `id_funcd` are transparent aliases for
`id`.

### 3. Treat pure curried Cat composition helpers as aliases

The current pure object/functor-action helpers:

```text
comp_cat_cov_func
comp_cat_cov_func_func
comp_cat_con_func
comp_cat_con_func_func
```

are the identity-family cases of the generic hom-action hierarchy.  The first
stage should keep exactly that specialization:

```text
comp_cat_cov_func X Y Z G
  := @hom_postcomp_func
       Cat_cat Cat_cat
       (@id Cat_cat Cat_cat)
       X Y Z G

comp_cat_cov_func_func X Y Z
  := @hom_postcomp_tele_func
       Cat_cat Cat_cat
       (@id Cat_cat Cat_cat)
       X Y Z

comp_cat_con_func X Y Z F
  := @hom_precomp_along_func
       Cat_cat Cat_cat
       (@id Cat_cat Cat_cat)
       Z X Y F

comp_cat_con_func_func X Y Z
  := @hom_precomp_along_tele_func
       Cat_cat Cat_cat
       (@id Cat_cat Cat_cat)
       Z X Y
```

Rules whose LHS currently mentions these helpers should be migrated to the
corresponding `hom_postcomp_*` or `hom_precomp_along_*` head.  Some old rules
then become direct duplicates of existing generic projection rules and should
be deleted rather than restated.

### 4. Do not introduce generalized `comp_cat*` counterparts for `hom_*`

There is a natural question whether a later stage should generalize the
`comp_cat_cov/con_*` names by adding the same functor argument that the
generic `hom_*` hierarchy already has.

For postcomposition, the useful general type is already:

```text
hom_postcomp_func Cat_cat K E W x y p
```

where:

```text
E : Functor K Cat_cat
p : Hom_K(x,y)
```

It maps:

```text
Functor(W,E[x]) -> Functor(W,E[y]).
```

For precomposition, the useful general type is already:

```text
hom_precomp_along_func K Cat_cat E Z x y p
```

where:

```text
E : Functor K Cat_cat
p : Hom_K(x,y)
```

It maps:

```text
Functor(E[y],Z) -> Functor(E[x],Z).
```

Therefore a generalized `comp_cat*` with an extra functor argument would
mostly rename the generic `hom_*` API.  The default decision is:

```text
Do not add generalized comp_cat* counterparts to hom_*.
Use hom_* directly for arbitrary Cat-valued families.
Keep first-stage comp_cat* aliases only as the identity-family readability
views.
```

The candidate type `F : Functor Cat_cat A` is not a Cat-composition helper in
this sense.  It lands in an arbitrary category `A`, so it belongs to the
generic hom-action API rather than the Cat-specific composition surface.

### 5. Keep primitive heads only for extra Cat/Catd structure

The following heads expose ordinary transfor or horizontal-composite
structure that is not available from an arbitrary category:

```text
comp_cat_cov_transf
comp_cat_con_transf
comp_cat_cov_func_func_transf
comp_cat_con_func_func_transf
comp_cat_cov_func_func_tapp1_func
comp_cat_func_func_tapp1_fapp0
```

They may remain stable heads, but their generic owners must be documented.
For example:

```text
comp_cat_cov_transf
  is the Cat-specialized component normal form of
  hom_postcomp_fapp1_fapp0
  at Cat_cat, id_Cat.

comp_cat_con_transf
  is the Cat-specialized component normal form of
  hom_precomp_along_fapp1_fapp0
  at Cat_cat, id_Cat.
```

The migration should prefer rules of the form:

```text
hom_postcomp_fapp1_fapp0(Cat_cat,Cat_cat,id_Cat,...)
  -> comp_cat_cov_transf(...)

hom_precomp_along_fapp1_fapp0(Cat_cat,Cat_cat,id_Cat,...)
  -> comp_cat_con_transf(...)
```

rather than rules whose LHS first goes through a pure `comp_cat_*` alias.

## Current Rule Families To Audit

The first implementation pass should classify existing rules into four
buckets.

### Bucket A: delete reverse folds and alias-headed duplicates

Delete or replace reverse folds from generic heads to specialized aliases:

```text
@id Cat_cat A                         -> id_func A
@id (Catd_cat K) E                    -> id_funcd K E
@comp_fapp0 Cat_cat ...               -> comp_cat_fapp0 ...
@comp_fapp0 (Catd_cat K) ...          -> comp_catd_fapp0 ...
```

Also delete or replace pure alias-headed projection rules once their generic
`hom_*` owner covers the same computation:

```text
fapp0 (comp_cat_cov_func ...) ...     -> ...
fapp0 (comp_cat_con_func ...) ...     -> ...
```

After alias migration, the reverse folds become fold/unfold hazards, and the
pure alias-headed projection rules duplicate generic projection rules.

### Bucket B: keep specialized projections on generic heads

Keep rules that express structure available only once the generic head is
specialized to `Cat_cat` or `Catd_cat`, but rewrite their LHSs to the generic
head:

```text
fapp0 (@id Cat_cat A) x
fapp1_fapp0 (@id Cat_cat A) p

fapp0 (@comp_fapp0 Cat_cat A B C F G) x
fapp1_fapp0 (@comp_fapp0 Cat_cat A B C F G) p
fapp1_func (@comp_fapp0 Cat_cat A B C F G) x y

tapp0_fapp0 ... (@id (@Catd_cat K) E)
tapp0_fapp0 ... (@comp_fapp0 (@Catd_cat K) E D C FF GG)
```

These are not duplicated generic category laws.  They are projections from a
generic category-level arrow after the ambient category is known to be
`Cat_cat` or `Catd_cat`.

### Bucket C: retain Cat-only transfor owners

Keep stable heads that own component and off-diagonal transfor structure:

```text
comp_cat_cov_transf
comp_cat_con_transf
comp_cat_cov_func_func_transf
comp_cat_con_func_func_transf
comp_cat_cov_func_func_tapp1_func
comp_cat_func_func_tapp1_fapp0
```

Migrate their inbound owner rules from `comp_cat_*` aliases to specialized
`hom_*` heads.  Their own projection rules such as `tapp0_fapp0`,
`tapp1_func`, and `tapp1_fapp0` may remain headed by the stable transfor
owner.

### Bucket D: compatibility aliases and public readability names

Keep public names as transparent aliases for readability when they are still
used in comments, examples, or downstream theorem statements:

```text
id_func
id_funcd
comp_cat_fapp0
comp_catd_fapp0
comp_cat_cov_func
comp_cat_cov_func_func
comp_cat_con_func
comp_cat_con_func_func
```

The rule is:

```text
Readable aliases may appear in declarations and RHSs.
They must not be rewrite discriminators.
```

When a downstream check is meant to assert the alias spelling itself, use a
typed `eq_refl` or an explicit compatibility theorem rather than a runtime
rewrite rule keyed on the alias.

## Proposed Implementation Phases

### Phase 0: inventory and baseline probes

1. Capture current quiet baseline:

   ```text
   EMDASH_TYPECHECK_TIMEOUT=60s make check
   ```

2. Capture warning baseline:

   ```text
   make warning-summary
   ```

3. Inventory all rewrite LHSs headed by:

   ```text
   id_func
   id_funcd
   comp_cat_fapp0
   comp_catd_fapp0
   comp_cat_cov_func
   comp_cat_cov_func_func
   comp_cat_con_func
   comp_cat_con_func_func
   comp_cat_cov_fapp1_func
   comp_cat_con_fapp1_func
   comp_cat_cov_func_func_fapp1_func
   comp_cat_con_func_func_fapp1_func
   ```

4. For each LHS, mark one of:

   ```text
   delete as duplicate
   migrate to id/comp_fapp0
   migrate to hom_postcomp_*
   migrate to hom_precomp_along_*
   retain as Cat-only transfor projection owner
   ```

### Phase 1: identity alias probe

Probe in a temporary full-file copy:

```text
id_func A     := @id Cat_cat A
id_funcd K E  := @id (@Catd_cat K) E
```

Remove reverse folds:

```text
@id Cat_cat A -> id_func A
@id (Catd_cat K) E -> id_funcd K E
```

Migrate essential LHSs to generic specialized identity heads.

Regression checks should include:

```text
fapp0 (@id Cat_cat A) x
fapp1_fapp0 (@id Cat_cat A) p
tapp0_fapp0 ... (@id (@Catd_cat K) E)
hom_precomp_along_fapp0(..., @id Cat_cat ...)
hom_precomp_along_fapp0(..., @id (@Catd_cat K) ...)
```

### Phase 2: raw Cat/Catd composition alias probe

Probe:

```text
comp_cat_fapp0 A B C F G
  := @comp_fapp0 Cat_cat A B C F G

comp_catd_fapp0 K E D C FF GG
  := @comp_fapp0 (@Catd_cat K) E D C FF GG
```

Remove reverse folds and migrate essential rules to generic LHSs.

Regression checks should include:

```text
fapp0 (@comp_fapp0 Cat_cat A B C F G) x
fapp1_fapp0 (@comp_fapp0 Cat_cat A B C F G) p
fapp1_func (@comp_fapp0 Cat_cat A B C F G) x y
tapp0_fapp0 ... (@comp_fapp0 (@Catd_cat K) E D C FF GG)
```

The existing Cat-specific left-associated composition normal form should be
audited.  If it is still semantically intended as runtime computation, keep
it as a rule on `@comp_fapp0 Cat_cat ...`, not on `comp_cat_fapp0`.

### Phase 3: pure curried Cat helper alias probe

Probe transparent aliases for:

```text
comp_cat_cov_func
comp_cat_cov_func_func
comp_cat_con_func
comp_cat_con_func_func
```

through the identity-family `hom_postcomp_*` and `hom_precomp_along_*`
specializations described above.

Delete object-action rules that merely duplicate:

```text
fapp0 (hom_postcomp_tele_func ...)
fapp0 (hom_postcomp_func ...)
fapp0 (hom_precomp_along_tele_func ...)
fapp0 (hom_precomp_along_func ...)
```

Keep checks that prove the old public names remain readable aliases, but do
not keep alias-headed runtime rules.

### Phase 4: higher Cat transfor owner bridge probe

Migrate inbound rules for:

```text
comp_cat_cov_transf
comp_cat_con_transf
comp_cat_cov_func_func_transf
comp_cat_con_func_func_transf
```

so that the LHS is the generic specialized `hom_*` owner:

```text
hom_postcomp_fapp1_fapp0(Cat_cat,Cat_cat,id_Cat,...)
hom_precomp_along_fapp1_fapp0(Cat_cat,Cat_cat,id_Cat,...)
hom_postcomp_tele_fapp1_fapp0(Cat_cat,Cat_cat,id_Cat,...)
hom_precomp_along_tele_fapp1_fapp0(Cat_cat,Cat_cat,id_Cat,...)
```

The stable RHS may remain the Cat-only transfor head.  Its component
projection rules remain the real reason the head exists.

### Phase 5: diagnostics, catalog, and status updates

After active-file promotion:

1. Update `emdash3_2_checks.lp` to check generic-owner normal forms and public
   alias compatibility separately.
2. Run:

   ```text
   EMDASH_TYPECHECK_TIMEOUT=60s make check
   make warning-summary
   make catalog
   ```

3. For substantial source changes, run:

   ```text
   make ci
   ```

4. Update:

   ```text
   REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md
   REPORT_EMDASH_V3_2_DEFISO_HOM_ACTION_PROFCOMPARISON_MIGRATION_PLAN_2026-06-28.md
   ```

   only after the implementation has landed.  This dedicated report is the
   authority for the proposed direction until then.

## Probe And Warning Requirements

This migration changes kernel normal forms.  It must be probe-first.

For each phase:

1. Use a temporary full-file copy or focused appended probe.
2. Include a small assertion exercising the intended normal form.
3. Run the quiet check with a timeout.
4. Run warning-enabled comparison when a rewrite family is changed.
5. Inspect any new nonjoinable critical pair whose top heads include:

   ```text
   id
   comp_fapp0
   fapp0
   fapp1_func
   fapp1_fapp0
   tapp0_fapp0
   tapp1_func
   tapp1_fapp0
   hom_postcomp_fapp0
   hom_precomp_along_fapp0
   ```

Warning count is diagnostic, not a veto.  The intended gate is whether the
new owner is semantically correct, subject-reduction safe, and needed by
concrete consumers.

## Implementation Checkpoint 2026-07-04

Phase 1 has been promoted to the active files.

Implemented decisions:

- `id_func A` is now a transparent alias for `@id Cat_cat A`.
- `id_funcd K E` is now a transparent alias for `@id (@Catd_cat K) E`.
- The reverse identity folds into `id_func` and `id_funcd` have been removed.
- Essential Cat/Catd identity projection rules now key on the generic
  specialized identity head, for example `@id Cat_cat A` and
  `@id (@Catd_cat K) E`.
- Existing compatibility checks using the public alias spellings remain, and
  new diagnostics separately check generic-owner normal forms.
- The check catalog classifier now recognizes the new generic Cat identity
  object-action check.

The promoted source migration covered the currently active identity-alias LHS
families, including:

```text
fapp0 / fapp1_fapp0 / fapp1_func identity functor projections
comp_cat_fapp0 and comp_catd_fapp0 identity-unit rules
Catd generic fapp1_fapp0 identity action
Op_func and Op_funcd identity bridges
hom_postcomp_fapp0 / hom_precomp_along_fapp0 identity bridges
DefIso cancellation rules using identity-family hom-action
tapp0_fapp0 displayed identity components
Prof_reindex and Prof_reindex_transf identity reindexing
Prof_func_hom identity and component guards
fixed co-Yoneda unit beta/naturality guards
Prof_imply_cov_transf fixed-endpoint identity guard
Product identity projection guards
Pullback_catd identity rules
Product_map_func proof-time identity comparisons
Path-induction representable guards using hom_(id)
```

Post-promotion audit:

```text
No rule/with/unif_rule pre-arrow pattern in emdash3_2.lp contains
@id_func or @id_funcd.
```

Validation commands run after promotion:

```text
EMDASH_TYPECHECK_TIMEOUT=60s make check
make catalog
make warning-summary
git diff --check
```

Results:

```text
make check: passed
make catalog: passed, 743 checks, 0 unclassified
git diff --check: passed
warning-summary: 1569 total warnings
  1398 unjoinable critical pair
   171 replaceable pattern variable
```

The warning inventory improved relative to the 2026-07-04 pre-migration
baseline of 1600 total warnings.  The main heads remain the known
composition/hom-action families (`comp_fapp0`, `hom_postcomp_fapp0`,
`comp_cat_fapp0`, `fapp1_fapp0`, `tapp0_fapp0`).  This is consistent with
Phase 1 being an identity-owner normalization, not yet the raw composition
alias migration.

## Implementation Checkpoint 2026-07-04, Phase 2

Phase 2 has been promoted to the active files.

Implemented decisions:

- `comp_cat_fapp0 A B C F G` is now a transparent alias for
  `@comp_fapp0 Cat_cat A B C F G`.
- `comp_catd_fapp0 K E D C FF GG` is now a transparent alias for
  `@comp_fapp0 (@Catd_cat K) E D C FF GG`.
- The reverse folds from generic composition into `comp_cat_fapp0` and
  `comp_catd_fapp0` have been removed.
- Specialized identity-unit rules for those aliases have been deleted;
  the generic `comp_fapp0` identity-unit rules now own those reductions.
- Cat/Catd projection and bridge rules that still require specialized
  structure now key on generic specialized composition, for example
  `@comp_fapp0 Cat_cat ...` and `@comp_fapp0 (@Catd_cat K) ...`.
- The Cat left-associated functor-composition runtime rule remains active,
  but its LHS/RHS now use `@comp_fapp0 Cat_cat ...`.
- Public alias spellings remain usable in definitions, theorem statements,
  compatibility diagnostics, and RHS readability positions.

The promoted source migration covered the currently active raw-composition
LHS families, including:

```text
Cat object and arrow projections of composed functors
Cat full hom-action projection of composed functors
Catd displayed-functor composition action
Op_func and constant functor composition bridges
hom_postcomp and hom_precomp composition accumulation
hom_postcomp_fapp0 proof-time comparison with Cat/Catd composition
DefIso cancellation over displayed-family composition
strict naturality accumulation over hom-action projections
Product_swap, Product_map_func, Eval_at_func, Pullback_catd, Sigma_proj1
  and join-elim composition cuts
Prof_reindex_transf composition
```

One source-side repair was required after the initial probe.  The
`Prof_reindex_transf` composition rule must keep the target displayed base
explicit:

```text
@comp_fapp0 (@Catd_cat (Product_cat (Op_cat A2) B2)) ...
```

but it must leave the three source/middle/target profunctor endpoint slots
inferred.  Reindexing can reduce those endpoints before the composition rule
fires, and explicit unreduced `Prof_reindex(...)` endpoint patterns miss the
weighted-limit pull-after-push normal form.  The earlier fully underscored
displayed base was too weak and failed subject reduction.

Post-promotion audit:

```text
No rule/with/unif_rule pre-arrow pattern in emdash3_2.lp contains
comp_cat_fapp0 or comp_catd_fapp0.
```

Diagnostics now include generic-owner checks for:

```text
@comp_cat_fapp0 ... ≡ @comp_fapp0 Cat_cat ...
fapp0 (@comp_fapp0 Cat_cat ...)
fapp1_fapp0 (@comp_fapp0 Cat_cat ...)
fapp1_func (@comp_fapp0 Cat_cat ...)
@comp_catd_fapp0 ... ≡ @comp_fapp0 (@Catd_cat K) ...
```

Probe and validation commands run during promotion:

```text
EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/catalias_phase2_comp.lp
EMDASH_LAMBDAPI_WARNINGS=1 EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/catalias_phase2_comp.lp
EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/catalias_phase2_prof_reindex_endpoint_probe.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
make catalog
python3 scripts/generate_check_catalog.py --strict
make warning-summary
```

Warning-enabled results:

```text
catalias_phase2_comp probe: 1398 total warnings
  1231 unjoinable critical pair
   167 replaceable pattern variable

active make warning-summary: 1382 total warnings
  1215 unjoinable critical pair
   167 replaceable pattern variable
```

This is lower than the Phase 1 active baseline of 1569 total warnings.  The
remaining top critical-pair heads are still the known composition/hom-action
families headed by `comp_fapp0`, `hom_postcomp_fapp0`, `tapp0_fapp0`,
`fapp1_fapp0`, and related projection heads.

## Implementation Checkpoint 2026-07-04, Phase 3

Phase 3 has been promoted to the active files.

Implemented decisions:

- `comp_cat_cov_func(G)` is now a transparent identity-family alias for
  `@hom_postcomp_func Cat_cat Cat_cat (@id Cat_cat Cat_cat) ... G`.
- `comp_cat_cov_func_func` is now a transparent identity-family alias for
  `@hom_postcomp_tele_func Cat_cat Cat_cat (@id Cat_cat Cat_cat) ...`.
- `comp_cat_con_func(F)` is now a transparent identity-family alias for
  `@hom_precomp_along_func Cat_cat Cat_cat (@id Cat_cat Cat_cat) ... F`.
- `comp_cat_con_func_func` is now a transparent identity-family alias for
  `@hom_precomp_along_tele_func Cat_cat Cat_cat (@id Cat_cat Cat_cat) ...`.
- The old reverse folds from Cat-valued generic `hom_postcomp_*` and
  `hom_precomp_along_*` heads into these pure helper names have been removed.
- Alias-headed `fapp1_func` / `fapp1_fapp0` projection rules for these pure
  helpers have been removed. The generic `hom_*_fapp1_*` heads now own those
  functor-level actions.
- Existing Cat-only transfor heads such as `comp_cat_cov_transf`,
  `comp_cat_con_transf`, `comp_cat_cov_func_func_transf`, and
  `comp_cat_con_func_func_transf` remain explicit semantic heads because they
  expose `tapp0_fapp0`, `tapp1_func`, and `tapp1_fapp0` structure. At this
  checkpoint their inbound bridge cleanup was still Phase 4; the next
  checkpoint below promotes the capped identity-family bridges.
- `Op_catd_func` is still a named semantic package, but its special
  postcomposition bridge now keys on the generic identity-family
  `hom_postcomp_func` head instead of the `comp_cat_cov_func` alias.

The check updates intentionally retargeted several curry/uncurry diagnostics.
After Phase 3, semantic curry and uncurry normal forms stop at generic
`hom_postcomp_*` / `hom_precomp_along_*` stable heads instead of expanding all
the way to the older Cat-specialized `comp_cat_*` presentations. This is the
intended Phase 3 behavior: the generic hom-action owner is the runtime normal
form, while Cat-only transfor heads are reserved for extra projection
structure.

Post-promotion audit:

```text
No rule/with/unif_rule pre-arrow pattern in emdash3_2.lp discriminates on the
exact helper aliases comp_cat_cov_func, comp_cat_cov_func_func,
comp_cat_con_func, or comp_cat_con_func_func. Derived Cat-only transfor heads
with longer names remain intentionally available.
```

Probe and validation commands run during promotion:

```text
EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/catalias_phase3_curried_helpers.lp
EMDASH_LAMBDAPI_WARNINGS=1 EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/catalias_phase3_curried_helpers.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
make catalog
python3 scripts/generate_check_catalog.py --strict
make warning-summary
python3 scripts/audit_rule_lhs.py --strict
git diff --check
make ci
```

Warning-enabled results:

```text
active make warning-summary: 1303 total warnings
  1139 unjoinable critical pair
   164 replaceable pattern variable
```

This is lower than the Phase 2 active baseline of 1382 total warnings. The
remaining top critical-pair heads are still the known composition/hom-action
families headed by `comp_fapp0`, `hom_postcomp_fapp0`, `tapp0_fapp0`,
`fapp1_fapp0`, `fapp1_func`, and `hom_precomp_along_fapp0`.

## Implementation Checkpoint 2026-07-05, Phase 4

Phase 4 has been promoted to the active files.

Implemented decisions:

- The identity-family capped postcomposition action now normalizes from the
  generic owner to the Cat-only transfor head:

  ```text
  @hom_postcomp_fapp1_fapp0 Cat_cat Cat_cat (@id Cat_cat Cat_cat) ...
    -> comp_cat_cov_transf(...)
  ```

- The identity-family capped tele-postcomposition action now normalizes to:

  ```text
  @hom_postcomp_tele_fapp1_fapp0 Cat_cat Cat_cat (@id Cat_cat Cat_cat) ...
    -> comp_cat_cov_func_func_transf(...)
  ```

- The identity-family capped precomposition action now normalizes to:

  ```text
  @hom_precomp_along_fapp1_fapp0 Cat_cat Cat_cat (@id Cat_cat Cat_cat) ...
    -> comp_cat_con_transf(...)
  ```

- The identity-family capped tele-precomposition action now normalizes to:

  ```text
  @hom_precomp_along_tele_fapp1_fapp0 Cat_cat Cat_cat (@id Cat_cat Cat_cat) ...
    -> comp_cat_con_func_func_transf(...)
  ```

- Broad arbitrary-family precomposition folds remain deferred.  The promoted
  precomposition bridge is deliberately restricted to the identity family so
  it does not reintroduce the endpoint-normal-form mismatch that motivated the
  earlier deferred comment.
- The `fapp1_func` diagnostics remain generic-owner checks.  This phase only
  migrates capped `fapp1_fapp0` paths to the Cat-only transfor heads, where
  the extra `tapp0_fapp0`, `tapp1_func`, and `tapp1_fapp0` projections are
  available.

Diagnostics now check the public alias paths:

```text
fapp1_fapp0(comp_cat_cov_func(G), eta)
  -> comp_cat_cov_transf(G,eta)

fapp1_fapp0(comp_cat_cov_func_func, eta)
  -> comp_cat_cov_func_func_transf(eta)

fapp1_fapp0(comp_cat_con_func(F), eta)
  -> comp_cat_con_transf(F,eta)

fapp1_fapp0(comp_cat_con_func_func, alpha)
  -> comp_cat_con_func_func_transf(alpha)
```

The generic arbitrary-family diagnostics still assert the `hom_*_fapp1_fapp0`
normal forms when the family argument is not visibly `@id Cat_cat Cat_cat`.

Probe and validation commands run during promotion:

```text
EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/catalias_phase4_transfor_bridges.lp
EMDASH_LAMBDAPI_WARNINGS=1 EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/catalias_phase4_transfor_bridges.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
make catalog
python3 scripts/generate_check_catalog.py --strict
make warning-summary
python3 scripts/audit_rule_lhs.py --strict
git diff --check
make ci
```

Warning-enabled results after active promotion:

```text
active make warning-summary: 1314 total warnings
  1150 unjoinable critical pair
   164 replaceable pattern variable
```

This is an increase of 11 warnings over the Phase 3 active baseline of 1303.
The increase is localized to the newly promoted bridge family; the summary now
lists `hom_postcomp_tele_fapp1_fapp0` among the top critical-pair term heads.
That is expected because the new identity-family bridge intentionally overlaps
the existing generic higher-action/functoriality paths and joins them at the
Cat-only transfor projection normal form.

## Corrected Assessment 2026-07-05: Phase 5 Is Required

The Phase 4 checkpoint left one architectural gap.  The following
functor-level wrappers still existed as primitive presentation heads:

```text
comp_cat_cov_fapp1_func
comp_cat_con_fapp1_func
comp_cat_cov_func_func_fapp1_func
comp_cat_con_func_func_fapp1_func
```

These heads do not themselves expose Cat-only `tapp0_fapp0`, `tapp1_func`, or
`tapp1_fapp0` structure.  They are functor-level wrappers around the generic
`hom_*_fapp1_func` hierarchy, so leaving them primitive is not complete with
respect to the original plan's owner principle.

The corrected target is to keep the public names only as transparent
identity-family aliases:

```text
comp_cat_cov_fapp1_func(G,F,H)
  := @hom_postcomp_fapp1_func
       Cat_cat Cat_cat (@id Cat_cat Cat_cat)
       X Y Z G F H

comp_cat_cov_func_func_fapp1_func(G,H)
  := @hom_postcomp_tele_fapp1_func
       Cat_cat Cat_cat (@id Cat_cat Cat_cat)
       X Y Z G H

comp_cat_con_fapp1_func(F,G,H)
  := @hom_precomp_along_fapp1_func
       Cat_cat Cat_cat (@id Cat_cat Cat_cat)
       Z X Y F G H

comp_cat_con_func_func_fapp1_func(F,K)
  := @hom_precomp_along_tele_fapp1_func
       Cat_cat Cat_cat (@id Cat_cat Cat_cat)
       Z X Y F K
```

The direct `fapp0` rules headed by those wrapper aliases should then be
deleted.  Their old public paths compute by:

```text
public alias
  -> generic hom_*_fapp1_func
  -> generic hom_*_fapp1_fapp0
  -> Phase 4 Cat-only transfor bridge
```

This preserves the real Cat-only primitive heads:

```text
comp_cat_cov_transf
comp_cat_con_transf
comp_cat_cov_func_func_transf
comp_cat_con_func_func_transf
```

Those capped heads remain justified because they expose the ordinary transfor
projection ladder.  The arbitrary-family `E : Functor K Cat_cat` API should
continue to use `hom_*` directly rather than introducing generalized
`comp_cat*` names that merely rename the generic API.

Focused probe result before active promotion:

```text
EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/catalias_phase5_func_wrappers_alias_probe.lp
EMDASH_LAMBDAPI_WARNINGS=1 EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/catalias_phase5_func_wrappers_alias_probe.lp
```

Both probes passed.  The warning-enabled probe reported the same unjoinable
count as the active Phase 4 baseline (`1150`), so the alias demotion is
mechanically feasible and does not add a new warning family in the focused
probe.

## Implementation Checkpoint 2026-07-05, Phase 5

Phase 5 has been promoted to the active files.

Implemented decisions:

- `comp_cat_cov_fapp1_func` is now a transparent identity-family alias for
  `@hom_postcomp_fapp1_func Cat_cat Cat_cat (@id Cat_cat Cat_cat) ...`.
- `comp_cat_cov_func_func_fapp1_func` is now a transparent identity-family
  alias for `@hom_postcomp_tele_fapp1_func Cat_cat Cat_cat
  (@id Cat_cat Cat_cat) ...`.
- `comp_cat_con_fapp1_func` is now a transparent identity-family alias for
  `@hom_precomp_along_fapp1_func Cat_cat Cat_cat
  (@id Cat_cat Cat_cat) ...`.
- `comp_cat_con_func_func_fapp1_func` is now a transparent identity-family
  alias for `@hom_precomp_along_tele_fapp1_func Cat_cat Cat_cat
  (@id Cat_cat Cat_cat) ...`.
- The direct `fapp0` rewrite rules headed by those four wrapper aliases have
  been deleted.  Their public compatibility paths now compute through the
  generic `hom_*_fapp1_func` projection rules and the Phase 4 capped bridges.
- The broad proof-time comparison between arbitrary-family
  `hom_postcomp_fapp1_func` and `comp_cat_cov_fapp1_func` has been removed.
  Arbitrary-family consumers should use `hom_postcomp_fapp1_func` directly.

Diagnostics now include explicit public-path checks for:

```text
fapp0(comp_cat_cov_fapp1_func(G), eta)
  -> comp_cat_cov_transf(G,eta)

fapp0(comp_cat_cov_func_func_fapp1_func, eta)
  -> comp_cat_cov_func_func_transf(eta)

fapp0(comp_cat_con_fapp1_func(F), eta)
  -> comp_cat_con_transf(F,eta)

fapp0(comp_cat_con_func_func_fapp1_func, alpha)
  -> comp_cat_con_func_func_transf(alpha)
```

Post-promotion audit:

```text
No rule/with/unif_rule pre-arrow pattern in emdash3_2.lp discriminates on
comp_cat_cov_fapp1_func, comp_cat_con_fapp1_func,
comp_cat_cov_func_func_fapp1_func, or comp_cat_con_func_func_fapp1_func.
```

Validation commands run during promotion:

```text
EMDASH_TYPECHECK_TIMEOUT=60s make check
make catalog
make warning-summary
python3 scripts/audit_rule_lhs.py --strict
git diff --check
make ci
```

Warning-enabled results after active promotion:

```text
active make warning-summary: 1314 total warnings
  1150 unjoinable critical pair
   164 replaceable pattern variable
```

This is unchanged from the Phase 4 active baseline.  The remaining top
critical-pair heads are still the known composition/hom-action families headed
by `comp_fapp0`, `hom_postcomp_fapp0`, `tapp0_fapp0`, `fapp1_fapp0`,
`fapp1_func`, and `hom_precomp_along_fapp0`.

## Corrected Assessment 2026-07-05: Postcomposition Bridge Promotion

The Cat_cat-indexed Cat-valued capped postcomposition comparison:

```text
@hom_postcomp_fapp1_fapp0 Cat_cat Cat_cat E W X Y f G H eta
  == comp_cat_cov_transf(W,E[X],E[Y],E[f],G,H,eta)
```

was previously installed as a proof-time `unif_rule`.  That was too weak for
the intended Cat-specialized semantics: the right-hand side exposes ordinary
transfor projections (`tapp0_fapp0`, `tapp1_func`, `tapp1_fapp0`), so the bridge
is a runtime normal-form choice rather than mere elaboration compatibility.

The bridge is now promoted to a rewrite rule:

```text
@hom_postcomp_fapp1_fapp0 Cat_cat Cat_cat E W X Y f G H eta
  -> comp_cat_cov_transf(W,E[X],E[Y],E[f],G,H,eta)
```

This deliberately makes Cat-valued capped postcomposition enter the existing
`comp_cat_cov_transf` projection ladder, including for non-identity
`E : Functor Cat_cat Cat_cat`.

Two stale proof-time tele-precomposition compatibility rules were also removed:

```text
@hom_precomp_along_tele_fapp1_func Cat_cat Cat_cat E ...
@hom_precomp_along_tele_fapp1_fapp0 Cat_cat Cat_cat E ...
```

They were originally runtime folds introduced during the naturality/functoriality
work, then downgraded to `unif_rule` after the hom-precomposition endpoint owner
changed.  A focused full-file deletion probe passed both normal and
warning-enabled checks, and current diagnostics do not consume those
proof-time comparisons.  The remaining precomposition story is the
identity-family runtime bridge plus the generic `hom_precomp_along_*` owner.

The following unification-rule hygiene cleanup was also promoted: reconstructible
source/target endpoint arguments on the non-owning side of three `unif_rule`s
were replaced by `_`, matching the same inferred-slot discipline used for
rewrite LHSs.

Validation:

```text
EMDASH_TYPECHECK_TIMEOUT=60s make check
make warning-summary
python3 scripts/audit_rule_lhs.py --strict
git diff --check
```

Warning-enabled results after this promotion:

```text
active make warning-summary: 1316 total warnings
  1152 unjoinable critical pair
   164 replaceable pattern variable
```

This is +2 unjoinable critical-pair warnings relative to the Phase 5 active
baseline.  The new classified family is headed by `hom_postcomp_fapp1_fapp0`
and comes from the intended overlap between the broad Cat-valued postcomposition
bridge and existing generic identity/opposite postcomposition paths.  This is a
runtime semantics choice, not a reason to demote the bridge back to
proof-time-only compatibility.

## Deferred Phase 6: Generalized Cat-Family Transfor Projection Heads

The postcomposition bridge promotion does not yet solve the full arbitrary-base
case `E : Functor K Cat_cat`.  The current promoted broad bridge is still
specialized to `Cat_cat Cat_cat E`, while true directed Cat-valued families use
an arbitrary base category `K`.

The plausible next design is to add owner-preserving generalized Cat-family
transfor projection heads for the capped higher-action owners:

```text
hom_postcomp_fapp1_fapp0 Cat_cat K E W x y f G H eta
  -> generalized Cat cov-transfor head

hom_precomp_along_fapp1_fapp0 Cat_cat K E Z x y f G H eta
  -> generalized Cat con-transfor head

hom_postcomp_tele_fapp1_fapp0 Cat_cat K E W x y f g alpha
  -> generalized Cat tele-postcomposition transfor head

hom_precomp_along_tele_fapp1_fapp0 Cat_cat K E Z x y f g alpha
  -> generalized Cat tele-precomposition transfor head
```

Those heads should use generic `hom_*` endpoints as their owning normal forms,
not raw `comp_cat_fapp0` endpoints, so they do not reintroduce the endpoint
normal-form mismatch that motivated the earlier deferred precomposition folds.
The existing identity-family `comp_cat_*_transf` heads can later be treated as
specializations or public views of the generalized heads if focused probes show
that this is coherent.

## Review Checkpoint 2026-07-05: Staged Cleanup And Phase 6 Feasibility

This checkpoint records the review state after the manual staged cleanup that
followed the postcomposition bridge promotion.  The staged cleanup is not yet
an active promoted checkpoint.

The following staged edits are coherent with the owner principle:

- removing the Cat-valued `hom_postcomp_fapp0 Cat_cat Cat_cat E ...`
  proof-time comparison, because the generic `hom_postcomp_fapp0` comparison
  already subsumes it;
- replacing reconstructible endpoint arguments by `_` in proof-time
  `hom_postcomp_fapp0` comparisons;
- removing the Catd identity-family `hom_postcomp_fapp0` proof-time comparison,
  because the generic identity-family comparison already covers
  `A = Catd_cat K`.

Two staged items need resolution before promotion:

- The raw `DefIso` cancellation rules for `comp_fapp0(defiso_from,defiso_to)`
  and `comp_fapp0(defiso_to,defiso_from)` are duplicated.  This is a source
  coherence and rule-hygiene problem, not a warning-count veto.  Keep one
  runtime pair and delete the duplicate pair, with a single accurate comment.
- The new identity-family proof-time bridge
  `hom_precomp_along_fapp0 A A (id A) ... == comp_fapp0 A ...` typechecks, but
  no current diagnostic consumes it.  Either add a focused typed consumer check
  that justifies it, or defer it to Phase 6 precomposition endpoint work.  A
  proof-time bridge should not be kept solely because it is syntactically
  plausible.

Current staged validation before cleanup resolution:

```text
EMDASH_TYPECHECK_TIMEOUT=60s make check: passed
make warning-summary:
  1332 total warnings
  1166 unjoinable critical pair
   166 replaceable pattern variable
python3 scripts/audit_rule_lhs.py --strict: passed
git diff --check --cached: passed
```

Focused probes on the staged source showed:

```text
delete only the duplicate raw DefIso runtime pair:
  warning-summary equivalent:
  1152 unjoinable critical pair
   165 replaceable pattern variable

delete the duplicate DefIso pair and also defer the new
hom_precomp_along_fapp0 identity-family unif_rule:
  warning-summary equivalent:
  1152 unjoinable critical pair
   164 replaceable pattern variable
```

These warning deltas are diagnostic evidence only.  The promotion decision is
semantic: eliminate the duplicate rule pair, and keep the new precomposition
proof-time bridge only if a concrete consumer or diagnostic needs it.

Phase 6 feasibility is positive in two layers.

First, the fixed capped projection bridges can be generalized directly to
arbitrary Cat-valued bases.  Focused full-file probes passed for the following
shapes:

```text
hom_postcomp_fapp1_fapp0 Cat_cat K E W x y f G H eta
  -> comp_cat_cov_transf
       W E[x] E[y] E[f] G H eta

hom_precomp_along_fapp1_fapp0 K Cat_cat E Z x y f G H eta
  -> comp_cat_con_transf
       E[x] E[y] Z E[f] G H eta
```

The generalized postcomposition bridge added no new warning family in the
focused probe.  The generalized precomposition bridge added one localized
critical-pair warning in the clean probe.  Per the SOP, that warning is not a
veto; it should be documented as the intended overlap between the generic
hom-action owner and the Cat-only transfor projection ladder if the rule is
promoted.

Second, the tele-level arbitrary-base case should not rewrite directly into
the existing identity-family heads
`comp_cat_cov_func_func_transf` and `comp_cat_con_func_func_transf`.  A focused
tele-postcomposition probe failed subject preservation because those existing
heads have identity-family endpoints such as
`hom_postcomp_func Cat_cat Cat_cat (id Cat_cat) ...`, while the arbitrary-base
owner has endpoints such as `hom_postcomp_func Cat_cat K E ...`.  Adding broad
endpoint coercion just to reuse the old head would reintroduce the endpoint
normal-form mismatch this plan is trying to remove.

The Phase 6 design target is therefore:

- initially route fixed capped arbitrary-base bridges through
  `comp_cat_cov_transf` and `comp_cat_con_transf` instantiated at fibres
  `E[x]`, `E[y]`, and functorial action `E[f]`; the corrected follow-up below
  upgrades this to generalizing those fixed heads themselves;
- introduce new generalized tele heads whose endpoints are generic
  `hom_postcomp_func` / `hom_precomp_along_func` endpoints, not identity-family
  `comp_cat_*` endpoints;
- compute the base 2-cell action as:

  ```text
  E[alpha] =
    fapp1_fapp0
      (Hom_cat K x y)
      (Functor_cat E[x] E[y])
      (fapp1_func K Cat_cat E x y)
      f g alpha
  ```

- for tele-postcomposition, the component at `G : Functor W E[x]` should be
  ordinary precomposition of `E[alpha]` by `G`;
- for tele-precomposition, the component at `G : Functor E[y] Z` should be
  ordinary postcomposition of `E[alpha]` by `G`;
- investigate the off-diagonal `tapp1_func` and `tapp1_fapp0` ladders
  separately, especially for tele-precomposition, because the current
  identity-family `comp_cat_con_func_func_transf` head has only the component
  projection ladder currently needed by active consumers.

This keeps Phase 6 aligned with the original goal: do not create generalized
pure `comp_cat*` aliases that merely rename `hom_*`, but do add Cat-specialized
heads where arbitrary-base Cat structure exposes real transfor projections.

## Design Clarification 2026-07-05: Generalized Tele Heads Must Be Linked Owners

The proposed generalized tele heads must not be unrelated new primitives.  If
they are introduced, they must be explicitly the Cat-valued projection normal
forms of the existing generic tele hom-action heads.

The generic owners are:

```text
hom_postcomp_tele_fapp1_fapp0
hom_precomp_along_tele_fapp1_fapp0
```

The linking should be a rewrite rule, not merely a `unif_rule`, if the goal is
runtime `tapp0_fapp0` / `tapp1_*` computation:

```text
hom_postcomp_tele_fapp1_fapp0 Cat_cat K E W x y f g alpha
  -> hom_postcomp_cat_tele_transf K E W x y f g alpha

hom_precomp_along_tele_fapp1_fapp0 K Cat_cat E Z x y f g alpha
  -> hom_precomp_along_cat_tele_transf K E Z x y f g alpha
```

A `unif_rule` would only help elaboration/equality search.  It would not make
`tapp0_fapp0` projections compute on the generic tele term.  Since the reason
for the Cat-specialized head is exactly to expose transfor projections, the
bridge should be runtime if promoted.

The proposed heads are provisional names.  Their important feature is that
they are typed with generic `hom_*` endpoints:

```text
hom_postcomp_cat_tele_transf(K,E,W,x,y,f,g,alpha)
  : Transf
      (hom_postcomp_func Cat_cat K E W x y f)
      (hom_postcomp_func Cat_cat K E W x y g)

hom_precomp_along_cat_tele_transf(K,E,Z,x,y,f,g,alpha)
  : Transf
      (hom_precomp_along_func K Cat_cat E Z x y f)
      (hom_precomp_along_func K Cat_cat E Z x y g)
```

This is the whole point of introducing the generalized heads.  The failed
tele-postcomposition probe tried to land the arbitrary-base term in the old
identity-family head.  That cannot preserve types, because the old head has
endpoints like:

```text
hom_postcomp_func Cat_cat Cat_cat (id Cat_cat) ...
hom_precomp_along_func Cat_cat Cat_cat (id Cat_cat) ...
```

while the arbitrary-base term has endpoints like:

```text
hom_postcomp_func Cat_cat K E ...
hom_precomp_along_func K Cat_cat E ...
```

So the generalized heads are not a new mathematical layer.  They are the same
tele-level concept, generalized from the identity-family case to arbitrary
`E : K -> Cat`.

The relationship to the existing identity-family heads should be:

```text
comp_cat_cov_func_func_transf(X,Y,Z,G,H,eta)
  = hom_postcomp_cat_tele_transf
      Cat_cat (id Cat_cat) X Y Z G H eta

comp_cat_con_func_func_transf(X,Y,Z,F,K,alpha)
  = hom_precomp_along_cat_tele_transf
      Cat_cat (id Cat_cat) Z X Y F K alpha
```

Long-term, they should not coexist as independent primitive owners.  The two
coherent implementation options are:

```text
Option 1:
  introduce better-named generalized heads and demote the old
  comp_cat_*_func_func_transf heads to transparent identity-family aliases.

Option 2:
  generalize the existing comp_cat_*_func_func_transf heads themselves by
  adding K and E parameters, then keep old identity-family public aliases.
```

The current staged preference is Option 1.  It is less disruptive because it
does not immediately change the type of existing public heads, while preserving
the invariant that there is one semantic owner and the old identity-family
names become aliases.

The component rules would use:

```text
Ef =
  fapp1_fapp0 K Cat_cat E x y f

Eg =
  fapp1_fapp0 K Cat_cat E x y g

Ealpha =
  fapp1_fapp0
    (Hom_cat K x y)
    (Functor_cat E[x] E[y])
    (fapp1_func K Cat_cat E x y)
    f g alpha
```

Then:

```text
tapp0_fapp0(hom_postcomp_cat_tele_transf(E,alpha), G)
  -> comp_cat_con_transf W E[x] E[y] G Ef Eg Ealpha
```

and:

```text
tapp0_fapp0(hom_precomp_along_cat_tele_transf(E,alpha), G)
  -> comp_cat_cov_transf E[x] E[y] Z G Ef Eg Ealpha
```

This solves the failed tele probe in the intended way: the rewrite from the
generic `hom_*_tele_fapp1_fapp0` owner lands in a head whose type has the same
generic `hom_*_func` endpoints, so subject preservation is not forced to
identify arbitrary-base endpoints with identity-family endpoints.  The new
primitive is justified only because it owns Cat-specific `tapp0/tapp1`
projections, while generic functoriality, identity, and composition remain
owned by `hom_*`.

## Implementation Checkpoint 2026-07-05, Phase 6

Phase 6 has been promoted for the arbitrary-base Cat-valued transfor projection
paths currently needed by the migration.

Implemented decisions:

- The capped postcomposition bridge is now arbitrary-base:

  ```text
  hom_postcomp_fapp1_fapp0 Cat_cat K E W x y f G H eta
    -> comp_cat_cov_transf(W,E[x],E[y],E[f],G,H,eta)
  ```

- The redundant identity-family capped postcomposition bridge was deleted;
  the arbitrary-base bridge covers it by `K = Cat_cat` and
  `E = id Cat_cat`.
- The capped precomposition bridge is now arbitrary-base:

  ```text
  hom_precomp_along_fapp1_fapp0 K Cat_cat E Z x y f G H eta
    -> comp_cat_con_transf(E[x],E[y],Z,E[f],G,H,eta)
  ```

- Two linked generalized tele heads were introduced:

  ```text
  hom_postcomp_cat_tele_transf(K,E,W,x,y,f,g,alpha)
    : Transf
        (hom_postcomp_func Cat_cat K E W x y f)
        (hom_postcomp_func Cat_cat K E W x y g)

  hom_precomp_along_cat_tele_transf(K,E,Z,x,y,f,g,alpha)
    : Transf
        (hom_precomp_along_func K Cat_cat E Z x y f)
        (hom_precomp_along_func K Cat_cat E Z x y g)
  ```

- Runtime bridge rules link the generic owners to those heads:

  ```text
  hom_postcomp_tele_fapp1_fapp0 Cat_cat K E W x y f g alpha
    -> hom_postcomp_cat_tele_transf(K,E,W,x,y,f,g,alpha)

  hom_precomp_along_tele_fapp1_fapp0 K Cat_cat E Z x y f g alpha
    -> hom_precomp_along_cat_tele_transf(K,E,Z,x,y,f,g,alpha)
  ```

- The old identity-family public heads are now transparent aliases:

  ```text
  comp_cat_cov_func_func_transf(X,Y,Z,G,H,eta)
    := hom_postcomp_cat_tele_transf(Cat_cat,id_Cat,X,Y,Z,G,H,eta)

  comp_cat_con_func_func_transf(X,Y,Z,F,K,alpha)
    := hom_precomp_along_cat_tele_transf(Cat_cat,id_Cat,Z,X,Y,F,K,alpha)
  ```

- The generalized tele-postcomposition head owns `tapp0_fapp0`,
  `tapp1_func`, and `tapp1_fapp0` by routing components and off-diagonal
  capped projections through the existing ordinary horizontal-composite
  helpers.
- The generalized tele-precomposition head currently owns `tapp0_fapp0`.
  Its off-diagonal `tapp1_func` / `tapp1_fapp0` ladder remains deferred,
  matching the previous identity-family situation where
  `comp_cat_con_func_func_transf` only had the component projection consumed
  by active checks.
- The retained identity-family proof-time bridge
  `hom_precomp_along_fapp0 A A (id A) ... == comp_fapp0 A ...` now has a
  typed `eq_refl` diagnostic, so it is no longer only syntactically plausible.

Diagnostics were added for:

```text
arbitrary-base capped postcomposition bridge;
arbitrary-base capped precomposition bridge;
generic tele owner -> linked generalized Cat tele head bridges;
old comp_cat_*_func_func_transf public aliases as identity-family views;
generalized tele-postcomposition tapp0_fapp0, tapp1_func, tapp1_fapp0;
generalized tele-precomposition tapp0_fapp0;
identity-family hom_precomp_along_fapp0 proof-time bridge.
```

Probe and validation commands run during promotion:

```text
EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/catalias_phase6_fixed_bridges.lp
EMDASH_LAMBDAPI_WARNINGS=1 EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/catalias_phase6_fixed_bridges.lp
EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/catalias_phase6_tele_heads.lp
EMDASH_LAMBDAPI_WARNINGS=1 EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/catalias_phase6_tele_heads.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
make catalog
make warning-summary
python3 scripts/audit_rule_lhs.py --strict
git diff --check
```

Warning-enabled results after active promotion:

```text
active make warning-summary: 1313 total warnings
  1147 unjoinable critical pair
   166 replaceable pattern variable
```

The warning count is lower than the immediately preceding active summary
recorded in this report (`1316 = 1152 + 164`).  The replaceable-pattern count
increased by two because the retained identity-family precomposition
proof-time bridge is now active and documented by a typed diagnostic.  The
critical-pair count decreased by five; remaining top heads are the known
composition/hom-action/projection families (`comp_fapp0`,
`hom_postcomp_fapp0`, `tapp0_fapp0`, `fapp1_fapp0`, and
`hom_postcomp_tele_fapp1_fapp0`).

## Corrected Assessment 2026-07-05: Fixed Heads Still Need Generalization

The Phase 6 checkpoint above promoted arbitrary-base bridge rules for fixed
capped Cat actions, but it did not yet generalize the fixed primitive heads
themselves.  Therefore the active implementation is incomplete relative to the
stronger "as-general-as-feasible Cat specialization" principle.

The active bridge rules currently have the shape:

```text
hom_postcomp_fapp1_fapp0 Cat_cat K E W x y f G H eta
  -> comp_cat_cov_transf(W,E[x],E[y],E[f],G,H,eta)

hom_precomp_along_fapp1_fapp0 K Cat_cat E Z x y f G H eta
  -> comp_cat_con_transf(E[x],E[y],Z,E[f],G,H,eta)
```

This makes arbitrary-family `hom_*` terms enter the Cat transfor projection
ladder, but the target heads are still ordinary identity-family-shaped
presentations.  The intended next fixed-head migration is to let those
Cat-specialized transfor heads carry the arbitrary family directly:

```text
comp_cat_cov_transf K E W x y f G H eta
  : Transf
      (comp_cat_fapp0 W E[x] E[y] E[f] G)
      (comp_cat_fapp0 W E[x] E[y] E[f] H)

comp_cat_con_transf K E Z x y f G H eta
  : Transf
      (comp_cat_fapp0 E[x] E[y] Z G E[f])
      (comp_cat_fapp0 E[x] E[y] Z H E[f])
```

The old public ordinary Cat presentations should then be rewritten as
identity-family specializations:

```text
comp_cat_cov_transf(X,Y,Z,G,F,H,eta)
  := comp_cat_cov_transf Cat_cat (id Cat_cat) X Y Z G F H eta

comp_cat_con_transf(X,Y,Z,F,G,H,eta)
  := comp_cat_con_transf Cat_cat (id Cat_cat) Z X Y F G H eta
```

This is analogous to the already-promoted tele-level solution:
`comp_cat_cov_func_func_transf` and `comp_cat_con_func_func_transf` became
identity-family aliases of the generalized
`hom_postcomp_cat_tele_transf` and `hom_precomp_along_cat_tele_transf` heads.

Focused probe result:

```text
tmp/probes/catalias_phase6_general_fixed_heads_probe.lp
EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/catalias_phase6_general_fixed_heads_probe.lp
EMDASH_LAMBDAPI_WARNINGS=1 EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/catalias_phase6_general_fixed_heads_probe.lp
```

Both probes passed.  The warning-enabled probe reported:

```text
1312 total warnings
  1146 unjoinable critical pair
   166 replaceable pattern variable
```

Promotion update 2026-07-05: the generalized fixed heads were promoted in
`emdash3_2.lp`, and the diagnostics in `emdash3_2_checks.lp` were migrated to
the new `K,E` arity.  The active promotion required one additional
LHS-hygiene correction: the generalized `tapp0_fapp0`, `tapp1_func`, and
`tapp1_fapp0` projection rules for both `comp_cat_cov_transf` and
`comp_cat_con_transf` now infer the reconstructible source/target category
slots instead of matching reducible terms such as `fapp0(id_Cat, Z)`.  Without
that correction, the ordinary identity-family public surface could normalize
the inner category argument before the projection rule matched.  The focused
probe was:

```text
tmp/probes/catalias_phase6_general_fixed_lhs_hygiene_probe.lp
EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/catalias_phase6_general_fixed_lhs_hygiene_probe.lp
EMDASH_LAMBDAPI_WARNINGS=1 EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/catalias_phase6_general_fixed_lhs_hygiene_probe.lp
```

The active validation after promotion was:

```text
EMDASH_TYPECHECK_TIMEOUT=60s make check
make catalog
make warning-summary
python3 scripts/audit_rule_lhs.py --strict
git diff --check
```

The warning summary after promotion is:

```text
1315 total warnings
  1149 unjoinable critical pair
   166 replaceable pattern variable
```

This small critical-pair increase is accepted under the SOP because the
generalized transfor term is the semantic owner of the projection, while the
category arguments are reconstructible typing information.

One attempted variant used generic `hom_postcomp_fapp0` /
`hom_precomp_along_fapp0` endpoints for the fixed heads.  That variant failed
subject preservation because the existing `tapp1_*` projection rules compute
through ordinary Cat composition endpoints.  Therefore the feasible fixed-head
generalization should use raw Cat-composition endpoints as shown above.  This
differs from the tele heads, whose endpoints must remain generic
`hom_postcomp_func` / `hom_precomp_along_func` endpoints to preserve the
generic owner of the whole tele-level action.

The generalized fixed heads should own generalized projection rules directly.
For example, the LHS should be headed by the generalized symbol:

```text
tapp0_fapp0(..., comp_cat_cov_transf K E W x y f G H eta)
  -> E[f][eta[-]]

tapp1_func(..., comp_cat_cov_transf K E W x y f G H eta)
  -> E[f][eta[-]]

tapp1_fapp0(..., comp_cat_cov_transf K E W x y f G H eta, p)
  -> E[f][eta[p]]

tapp0_fapp0(..., comp_cat_con_transf K E Z x y f G H eta)
  -> eta[E[f][-]]

tapp1_func(..., comp_cat_con_transf K E Z x y f G H eta)
  -> eta[E[f][-]]

tapp1_fapp0(..., comp_cat_con_transf K E Z x y f G H eta, p)
  -> eta[E[f][p]]
```

The active tele heads already follow the as-general-as-feasible principle for
their promoted projection surface.  In the active source,
`hom_postcomp_cat_tele_transf K E W x y f g alpha` is linked by runtime rewrite
from `hom_postcomp_tele_fapp1_fapp0 Cat_cat K E ...` and already owns
generalized `tapp0_fapp0`, `tapp1_func`, and `tapp1_fapp0` projections.
Likewise, `hom_precomp_along_cat_tele_transf K E Z x y f g alpha` is linked by
runtime rewrite from `hom_precomp_along_tele_fapp1_fapp0 K Cat_cat E ...` and
owns its generalized `tapp0_fapp0`, `tapp1_func`, and `tapp1_fapp0`
projections.

Promotion update 2026-07-05: the remaining tele-precomposition
off-diagonal ladder was promoted by adding the small dual helper
`comp_cat_con_func_func_tapp1_func`.  This helper is the same ordinary
horizontal-composite object as `comp_cat_func_func_tapp1_fapp0`, but
curried in the ordinary transfor `eta : G => H`; its `fapp0` rule routes
directly to `comp_cat_func_func_tapp1_fapp0`.  The generalized
`hom_precomp_along_cat_tele_transf` `tapp1_func` and `tapp1_fapp0` rules then
instantiate that helper in the fibres `E[x]`, `E[y]`.
The capped object intentionally uses the neutral name
`comp_cat_func_func_tapp1_fapp0`; `cov` and `con` remain only on the two
curried `tapp1_func` views.
Naming cleanup 2026-07-05: this neutral name replaced the earlier
`comp_cat_cov_func_func_tapp1_fapp0` spelling in source, diagnostics, and
active reports.  `make check`, `make catalog`, `make warning-summary`,
`python3 scripts/audit_rule_lhs.py --strict`, `git diff --check`, and
`make ci` passed after the rename; the warning count stayed at `1317`.

Focused probe:

```text
tmp/probes/catalias_phase12_precomp_tele_offdiag_probe.lp
EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/catalias_phase12_precomp_tele_offdiag_probe.lp
EMDASH_LAMBDAPI_WARNINGS=1 EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/catalias_phase12_precomp_tele_offdiag_probe.lp
```

Final active validation after CATALIAS-12:

```text
EMDASH_TYPECHECK_TIMEOUT=60s make check
make catalog
make warning-summary
python3 scripts/audit_rule_lhs.py --strict
git diff --check
make ci
```

Final warning summary:

```text
1317 total warnings
  1151 unjoinable critical pair
   166 replaceable pattern variable
```

The CATALIAS-12 promotion accounts for the final +2 critical-pair delta over
the CATALIAS-11 state; this is accepted because the new rules expose a
previously missing semantic projection ladder.

## Success Criteria

The migration is successful when:

```text
id_func and id_funcd are transparent aliases, not rewrite owners;
comp_cat_fapp0 and comp_catd_fapp0 are transparent aliases, not rewrite owners;
pure comp_cat_cov/con object-action helpers are transparent identity-family
  views of hom_postcomp/hom_precomp;
no rewrite LHS discriminates on those transparent aliases;
Cat-only transfor projection heads remain only where they expose tapp0/tapp1
  structure;
fixed `comp_cat_cov_transf` and `comp_cat_con_transf` heads carry arbitrary
  `K,E` Cat-family parameters, with old ordinary Cat spellings as
  identity-family aliases;
generalized fixed `comp_cat_cov_transf` and `comp_cat_con_transf` own their
  `tapp0_fapp0`, `tapp1_func`, and `tapp1_fapp0` projection rules;
generalized `hom_postcomp_cat_tele_transf` owns its component and off-diagonal
  projection rules, and generalized `hom_precomp_along_cat_tele_transf` owns
  the same;
functor-level comp_cat_*_fapp1_func wrappers are transparent aliases of
  identity-family hom_*_fapp1_func owners;
diagnostics distinguish generic-owner normal forms from public alias
  compatibility;
make check passes;
warning-summary deltas are classified.
```

## Open Questions

1. Should public alias names remain indefinitely?

   Current leaning: yes for readability, comments, and theorem statements,
   but never as rewrite discriminators.

2. Should generalized Cat-specialized transfor heads be introduced for
   arbitrary `E : Functor K Cat_cat`?

   Resolved direction: yes, but only for capped transfor projection heads that
   expose extra Cat structure.  Do not introduce generalized pure
   `comp_cat*` aliases merely to rename the generic `hom_*` API.  The fixed
   `comp_cat_cov_transf` / `comp_cat_con_transf` heads have been generalized
   to arbitrary `K,E`; the pure `comp_cat_*_func*` helpers remain aliases.

3. Should Cat-specialized left-associated composition remain runtime?

   Current leaning: preserve current runtime behavior initially, but move the
   rule to `@comp_fapp0 Cat_cat ...`.  Reassess after warning-enabled probes.

4. Should `comp_cat_cov_fapp1_func`, `comp_cat_con_fapp1_func`, and the
   `*_func_func_fapp1_func` heads remain?

   Resolved by the 2026-07-05 corrected assessment: demote them to transparent
   identity-family aliases of the generic `hom_*_fapp1_func` owners.  Keep the
   capped transfor heads that own `tapp0_fapp0`, `tapp1_func`, and
   `tapp1_fapp0`.

## Side-Task Ledger

- `CATALIAS-01`: Inventory alias-headed rewrite LHSs in active source.
  Status: complete for identity, raw composition, and pure curried-helper
  aliases.
- `CATALIAS-02`: Probe transparent `id_func` / `id_funcd` aliases.
  Status: promoted on 2026-07-04.
- `CATALIAS-03`: Probe transparent `comp_cat_fapp0` / `comp_catd_fapp0`
  aliases.  Status: promoted on 2026-07-04.
- `CATALIAS-04`: Probe pure `comp_cat_cov/con_func*` aliases through
  identity-family `hom_*`.  Status: promoted on 2026-07-04.
- `CATALIAS-05`: Migrate Cat-only transfor inbound bridges to generic
  specialized `hom_*` LHSs.  Status: promoted on 2026-07-05 for the capped
  identity-family bridges.
- `CATALIAS-06`: Update diagnostics and warning inventory after promotion.
  Status: complete for Phases 1-5.
- `CATALIAS-07`: Demote functor-level Cat higher-action wrappers to
  identity-family `hom_*_fapp1_func` aliases.  Status: promoted on
  2026-07-05.
- `CATALIAS-08`: Promote Cat_cat-indexed Cat-valued capped postcomposition
  bridge from proof-time compatibility to runtime projection bridge; remove
  stale tele-precomposition proof-time scaffolding.  Status: promoted on
  2026-07-05.
- `CATALIAS-09`: Design generalized arbitrary-base Cat-family transfor
  projection heads for `E : Functor K Cat_cat`.  Status: feasibility reviewed
  on 2026-07-05, design clarified, and promoted for arbitrary-base bridge
  rules, linked tele heads, tele-postcomposition component/off-diagonal
  projections, and tele-precomposition component projection.  The stronger
  fixed-head `K,E` generalization is promoted under `CATALIAS-11`;
  tele-precomposition off-diagonal projections are promoted under
  `CATALIAS-12`.
- `CATALIAS-10`: Resolve the staged 2026-07-05 cleanup before promotion.
  Status: complete.  The duplicate raw DefIso runtime pair is absent from the
  active source, and the retained identity-family
  `hom_precomp_along_fapp0` proof-time bridge has a typed `eq_refl`
  diagnostic.
- `CATALIAS-11`: Generalize fixed `comp_cat_cov_transf` /
  `comp_cat_con_transf` heads to arbitrary `K,E`, demote old ordinary Cat
  spellings to identity-family aliases, and migrate their `tapp0_fapp0`,
  `tapp1_func`, and `tapp1_fapp0` projection rules to the generalized heads.
  Status: promoted on 2026-07-05 with raw Cat-composition endpoints and
  inferred reconstructible category slots on the generalized projection LHSs.
  `make check`, `make catalog`, `make warning-summary`,
  `python3 scripts/audit_rule_lhs.py --strict`, `git diff --check`, and
  `make ci` passed after promotion.
- `CATALIAS-12`: Add generalized `tapp1_func` / `tapp1_fapp0` off-diagonal
  projection ladder for `hom_precomp_along_cat_tele_transf`.
  Status: promoted on 2026-07-05 through the dual helper
  `comp_cat_con_func_func_tapp1_func`, whose object rule reuses
  `comp_cat_func_func_tapp1_fapp0`.  `make check`, `make catalog`,
  `make warning-summary`, `python3 scripts/audit_rule_lhs.py --strict`,
  `git diff --check`, and `make ci` passed after promotion.
