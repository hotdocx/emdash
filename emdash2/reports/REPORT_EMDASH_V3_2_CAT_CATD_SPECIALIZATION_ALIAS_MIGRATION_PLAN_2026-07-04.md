# EMDASH v3.2 Cat/Catd Specialization Alias Migration Plan

Date: 2026-07-04
Last reviewed: 2026-07-04

Plan-ID: EMDASH-V3-2-CAT-CATD-SPECIALIZATION-ALIAS-MIGRATION-2026-07-04
Depends-On: EMDASH-V3.2-DEFISO-HOM-ACTION-PROFCOMP-MIGRATION-2026-06-28; EMDASH-V3-2-ECKMANN-HILTON-APPLICATION-2026-07-03; REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26
Supersedes: no whole report; refines and corrects the Cat-specialized cleanup target in section 5 of REPORT_EMDASH_V3_2_DEFISO_HOM_ACTION_PROFCOMPARISON_MIGRATION_PLAN_2026-06-28.md
Side-Task-Ledger: #side-task-ledger
Infinity-Codex-Origin: current-session-analysis-2026-07-04
Infinity-Codex-Decision-Responses: infinity-codex:019f248f-4d5f-7a71-95a2-7eb8106d6225:019f270d-b800-7611-be54-abf9ff3106de
Status: Phases 1-2 identity/composition alias migrations promoted on
2026-07-04; pure curried-helper and Cat-only transfor bridge phases remain
pending

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
comp_cat_cov_func_func_tapp1_fapp0
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
comp_cat_cov_func_func_tapp1_fapp0
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
comp_cat_cov_func_func_tapp1_fapp0
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
diagnostics distinguish generic-owner normal forms from public alias
  compatibility;
make check passes;
warning-summary deltas are classified.
```

## Open Questions

1. Should public alias names remain indefinitely?

   Current leaning: yes for readability, comments, and theorem statements,
   but never as rewrite discriminators.

2. Should generalized `comp_cat*` names be introduced for arbitrary
   `E : Functor K Cat_cat`?

   Current leaning: no.  The generic `hom_postcomp_*` and
   `hom_precomp_along_*` APIs already express these types directly.

3. Should Cat-specialized left-associated composition remain runtime?

   Current leaning: preserve current runtime behavior initially, but move the
   rule to `@comp_fapp0 Cat_cat ...`.  Reassess after warning-enabled probes.

4. Should `comp_cat_cov_fapp1_func`, `comp_cat_con_fapp1_func`, and the
   `*_func_func_fapp1_func` heads remain?

   Current leaning: demote them if their only role is a functor-level wrapper
   around the generic `hom_*_fapp1_func` owner.  Keep the capped transfor
   heads that own `tapp0_fapp0`, `tapp1_func`, and `tapp1_fapp0`.

## Side-Task Ledger

- `CATALIAS-01`: Inventory alias-headed rewrite LHSs in active source.
  Status: complete for identity and raw composition aliases; curried helpers
  remain pending.
- `CATALIAS-02`: Probe transparent `id_func` / `id_funcd` aliases.
  Status: promoted on 2026-07-04.
- `CATALIAS-03`: Probe transparent `comp_cat_fapp0` / `comp_catd_fapp0`
  aliases.  Status: promoted on 2026-07-04.
- `CATALIAS-04`: Probe pure `comp_cat_cov/con_func*` aliases through
  identity-family `hom_*`.  Status: pending.
- `CATALIAS-05`: Migrate Cat-only transfor inbound bridges to generic
  specialized `hom_*` LHSs.  Status: pending.
- `CATALIAS-06`: Update diagnostics and warning inventory after promotion.
  Status: complete for Phases 1-2.
