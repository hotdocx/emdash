<INSTRUCTIONS>
## Scope And Goal

`emdash2` is the authoritative Lambdapi v3.2 development for functorial type
theory: strict/lax omega-categories, omega-functors, transfors, directed
families, dependent categorical structure, and selected computational
universal constructions.

Active semantics live in `emdash3_2.lp` and its one-way extension modules.
This file is the mandatory editing and validation SOP. It deliberately does
not duplicate the exhaustive module catalogue, current architecture report,
mathematical Foundations, canonical notation guide, plan registry, or
generated executable inventories.

The development is an evolving research kernel. A passing term or attractive
equation is not by itself authority for a new rule. Preserve semantic owners,
variance, retained higher action, subject reduction, and explicit noncollapse
boundaries.

## Authority And Document Roles

Use this order:

1. active Lambdapi declarations, rules, diagnostics, and focused reviewer
   examples;
2. this `AGENTS.md` for mandatory workflow and rule-design constraints;
3. `reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md` for the
   current implementation architecture and owner map;
4. `reports/EMDASH_FOUNDATIONS.md` for the mathematician-facing explanation;
5. `reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md` for
   comments, examples, notation, and parser-boundary planning;
6. the active task plan and `reports/INDEX.md` for decisions, lifecycle, and
   recovery routing;
7. `reports/REPORT_EMDASH_CHECK_CATALOG.md` and
   `reports/REPORT_EMDASH_HEALTH.md` for generated executable evidence; and
8. dated completed plans for historical probes, warning classifications, and
   rejected alternatives.

If prose and active source disagree, source wins and the affected standing
document must be repaired in the same maintenance slice. Book and article
prose never create mathematical authority.

The root `AGENTS.md` additionally governs repository/worktree/package tasks.
For renderer or book work under `print/`, also follow `print/AGENTS.md`.

## Compact Owner Map

- `emdash3_2.lp` owns the generic categorical nucleus: classifiers, iterated
  Homs, functors, transfors, directed families, Sigma/Pi, internal dependent
  homs, represented actions, adjunctions, profunctors, and generic cut
  computation.
- One-way standard-library extensions own equality-valued action and
  truncation, presheaves/sieves/sites/sheafification, commutative algebra and
  geometry, directed/groupoidal HITs, groupoidification, Gray/cubical and
  simplex constructions. Their exact current boundaries are listed once in
  the current-status report.
- `emdash3_2_monads.lp` owns monad-primary triangular extension and its narrow
  opposite-derived computational mirror.
- `emdash3_2_set_path_pointwise_transformation.lp` and
  `emdash3_2_groupoidification_set_extensionality.lp` own the narrow
  set-target whole-transformation and map-extensionality boundary. They do not
  provide arbitrary pointwise naturality, dependent groupoidification, source
  action, or a `Groupoidify` adjunction.
- `emdash3_2_preadditive_categories.lp` owns generic set-valued abelian Hom
  structures and bilinear generic composition.
  `emdash3_2_commutative_algebra_freyd_preadditive_laws.lp` and
  `emdash3_2_commutative_algebra_freyd_preadditive.lp` own full arbitrary-
  quotient Freyd laws and the checked preadditive instance.
  `emdash3_2_commutative_algebra_finite_free_preadditive.lp` packages the
  existing set-valued column-matrix addition and transparent distributivity
  comparisons as the finite-free `PreadditiveCategory` instance. The
  finite-free binary-product, terminal-zero, Cartesian, and additive modules
  select the existing direct-sum functor and rank zero, with stable matrix
  projection/pairing/zero observations and generic triangular computation.
  `emdash3_2_additive_categories.lp` and the finite-direct-sum/Freyd additive
  extensions derive biproducts, terminal/initial zero, and the checked
  `AdditiveCategory` instance. `emdash3_2_weak_kernels.lp` owns the generic
  Hom-fibre computational weak-kernel package and retained per-arrow test
  reindexing. `emdash3_2_kernels_cokernels.lp` adds genuine kernel/cokernel
  universal properties as contractible internal factor fibres, with selected
  lift/colift, reconstruction, uniqueness, whole capability, and thin
  pre-Abelian packaging. Closed quotient-level concrete capability and
  Abelian structure remain separate layers.
  `emdash3_2_abelian_categories.lp` adds direct monic/epic cancellation,
  proves selected kernel embeddings monic and cokernel projections epic, and
  packages normal lift/colift `HFiber`s plus the thin generic computational
  Abelian structure. Concrete Freyd normality remains a witnessed downstream
  construction.
  `emdash3_2_abelian_images.lp` derives coimage as cokernel-of-kernel, image
  as kernel-of-cokernel, their canonical comparison, and the factorization
  through projection/comparison/embedding. Comparison invertibility remains
  downstream normality data and is not postulated.
  `emdash3_2_abelian_bimorphisms.lp` constructs `IsoEvidence` for every
  explicitly monic and epic arrow using the normal-monomorphism lift of the
  codomain identity; it specializes to the canonical comparison when that
  bimorphism evidence is supplied.
  `emdash3_2_commutative_algebra_freyd_normal_monomorphisms.lp` and
  `emdash3_2_commutative_algebra_freyd_normal_epimorphisms.lp` are the
  rule-free witnessed formal Construction 3.14/3.15 owners. The former
  supplies the relation-preserving lift and quotient reconstruction; the
  latter supplies the relation-preserving raw/quotient colift and quotient
  reconstruction. Both construct raw-competitor uniqueness from explicit
  agreements rather than decoding truncated quotient equality.
  `emdash3_2_commutative_algebra_freyd_witnessed_abelian.lp` combines those
  completed normality families with the witnessed pre-Abelian package. Its
  `CommRingFreydWitnessedAbelian` value is capability-indexed by finite-free
  weak kernels and explicit raw agreements; it is not the stronger closed
  `ComputationalAbelianCategory` value.
  `emdash3_2_commutative_algebra_freyd_images.lp` derives the witnessed formal
  cokernel-of-kernel coimage, kernel-of-cokernel image, comparison, and
  factorization. Given explicit comparison monic/epic agreements, it computes
  both normality inverse candidates and packages their derived inverse laws as
  `IsoEvidence`; it does not take an isomorphism as data.
  `emdash3_2_computational_weak_pullbacks.lp` derives weak pullbacks from the
  weak kernel of `[alpha,-gamma]`; its cone is the existing annihilator fibre
  of an arrow into the selected biproduct, not a manual square record. Its
  compatibility/cone theorem modules derive `alpha o p = gamma o q` by
  additive cancellation and turn an explicit equalizing pair back into that
  internal cone.
  `emdash3_2_commutative_algebra_freyd_cokernels.lp` owns formal Freyd
  cokernel presentations, projections, and colifts parameterized by explicit
  zero-composite agreements. It does not decode arbitrary truncated equality
  back into a raw agreement witness.
  `emdash3_2_commutative_algebra_freyd_kernels.lp` consumes an explicit
  finite-free weak-kernel capability, performs the two weak-pullback
  construction, and retains zero/reconstruction agreements through lift and
  quotient uniqueness.
  `emdash3_2_commutative_algebra_freyd_witnessed_preabelian.lp` combines the
  existing Freyd additive structure with both canonical constructions as one
  capability-parameterized witnessed surface. Its universal tests retain raw
  zero/reconstruction agreements; it is not a closed quotient-level
  `PreAbelianCategory` and does not decode arbitrary truncated paths.
  `emdash3_2_commutative_algebra_freyd_normal_monomorphisms.lp` implements the
  witness-enriched Construction 3.14 through raw lift and quotient
  reconstruction using block splitting and the first weak pullback. Its
  raw-competitor uniqueness layer remains downstream.
- `emdash3_2_triangular_binary_products.lp`,
  `emdash3_2_terminal_objects.lp`, and
  `emdash3_2_cartesian_categories.lp` own selected whole binary/empty-product
  computation and thin Cartesian packaging. The assumption-explicit weighted
  bridge remains separate.
- `emdash3_2_pullbacks.lp` and
  `emdash3_2_slice_dependent_products.lp` own the exact-slice families and
  selected chain `Sigma_u |- u* |- Pi_u`. Generic `Pullback_catd`, `Pi_cat`,
  and proposed general `Pi_along_func` are different constructions.
- Cubical structure is derived, not a parallel square theory:

  ```text
  ordinary Sigma + pointwise opposite + homd_int
    -> homdc_int
    -> homdc_total_cat
    -> LaxArrow_cat
    -> CubicalArrow_cat.       // transparent alias
  ```

  A visible lax square packages the generic nested Sigma term
  `(a,(b,alpha))`; `alpha : b o u ==> v o a` is an object of the existing
  iterated Hom, not a separately postulated commutativity field.
- `IsStrictFunctor` and `IsPseudoFunctor` constrain existing compositor
  action. They do not introduce a second functor grammar or automatically
  reflect semantic evidence into judgmental identity.
- `emdash3_2_checks.lp` is the integrated diagnostic suite; `examples/`
  contains independent reviewer-facing consumers. Neither replaces the
  owning implementation declaration.

The in-progress `goal/global-strictness-profile-migration-v3.2` branch is not
part of the integrated baseline. Do not copy its in-flight rules, counts, or
conclusions into current authorities before integration and a dedicated
follow-up audit.

## Starting A v3.2 Task

Before nontrivial edits:

1. read the active implementation, checks, current status, Foundations, and
   canonical syntax relevant to the task;
2. consult `reports/INDEX.md` and the active task-specific plan/side-task
   ledger;
3. run `git status --short`, inspect staged and unstaged diffs separately, and
   preserve unrelated user work;
4. locate current symbols and nearby rules with `rg`; do not rely on remembered
   line numbers;
5. run a bounded baseline check.

The implementation is draft work. When infrastructure is missing, identify
and document the prerequisite rather than forcing a brittle encoding. A
construction that works for the 2-categorical case will often extend through
the iterated-hom architecture to the omega setting.

## Fast Commands

- Active kernel and diagnostics: `make check`
- Reviewer examples: `make examples`
- Local CI gate: `make ci`
- Warning-enabled kernel check: `make check-warnings`
- Compact warning inventory: `make warning-summary`
- Strict inferred-slot audit: `make audit-rules`
- Regenerate/check catalog: `make catalog`
- Check source TOC structure/header equality: `make toc`
- Refresh health report: `make health`
- Watch and recheck: `make watch` (log: `logs/typecheck.log`)
- Focused temporary probe: `scripts/probe.sh tmp/probes/name.lp`
- Decision tree: `scripts/decision_tree.sh SYMBOL`
- Type-aware search: `scripts/lambdapi_search.sh QUERY`
- Print preview/check from the Git root: `./scripts/pnpmw run print:dev` /
  `./scripts/pnpmw run print:check`
- Book assembly/check/render/release from the Git root:
  `./scripts/pnpmw run book:assemble` / `./scripts/pnpmw run book:check` /
  `./scripts/pnpmw run book:render` / `./scripts/pnpmw run book:release`
- Book semantic typography: `../scripts/pnpmw --dir emdash2/print run book:typography`
- Remove compilation artifacts: `make clean`
- Manually prune old logs: `make prune-logs`

## Avoid Hung Typechecks

Early-development hangs usually signal rewrite/unification trouble. Keep
every Lambdapi invocation bounded by the uniform 90-second per-target ceiling.
The central diagnostics and several focused consumers now have measured green
runs near 60 seconds, so the former 60-second distinction between probes and
registered checks can produce false failures. A healthy focused check still
returns immediately; the larger ceiling does not authorize unnecessary broad
or aggregate runs.

```bash
EMDASH_TYPECHECK_TIMEOUT=90s make check
timeout 90s lambdapi check emdash3_2.lp
EMDASH_LAMBDAPI_WARNINGS=1 EMDASH_TYPECHECK_TIMEOUT=90s make check
```

`scripts/check.sh`, `scripts/check_examples.sh`, `scripts/probe.sh`,
`scripts/check_warning_summary.sh`, and `scripts/check_metrics.py` all default
to 90 seconds per Lambdapi target. Resumable health evidence still requires
exact checked-content and environment identity, including the timeout. An
additive registered-file extension may reuse only the predecessor file subset
whose paths and bytes rehash to its recorded snapshot under the same
environment; every newly registered target must check fresh.

All check/probe/metrics scripts append `EMDASH_LAMBDAPI_FLAGS`, for example:

```bash
EMDASH_LAMBDAPI_FLAGS='--debug=u' scripts/probe.sh tmp/probes/name.lp
```

If a quiet run times out or hides the interaction, rerun the smallest target
with warnings enabled before rejecting the proposed rule.

## Rewrite And Unification Hygiene

- Probe every nontrivial rewrite/unification change in a temporary full-file
  copy with a focused assertion before editing the active owner.
- Put the candidate at its intended owning position when auditing critical
  pairs; an append-only import probe can miss later interactions.
- Keep inferred source/target/category/family arguments as `_` on rule LHSs
  unless they are real discriminators or measured subject-reduction/performance
  guards.
- Annotate intentional compound inferred slots immediately above the rule:
  `// lhs-audit: keep SLOT[,SLOT] -- reason`.
- Never apply inferred-slot cleanup mechanically. Run the focused probe,
  bounded full check, and warning comparison when relevant.
- LHS minimality is not a blanket implicit-argument cleanup: RHSs and defined
  bodies must retain parameters not syntactically recoverable from visible
  data, while diagnostic assertions may keep canonical endpoints explicit.
- Avoid outer-eliminator/inner-cut commuting conversions such as
  `sigma_Fst(comp_fapp0(...))`. Prefer a constructor beta rule, existing
  projection ladder, stable intermediate component, or equation at the
  semantic owner.
- A documented canonical projection ladder may contain nested constructor
  patterns. Test both reduction orders for every exceptional commuting bridge.
- Treat warning counts as diagnostics for locating overlap families, not as an
  automatic veto on semantically intended computation.
- In particular, the historical global strict `fapp1` identity/composition and
  strict-naturality cuts are explicitly scheduled for later profile-local
  migration. An intended lax/profile-specific consumer rule may overlap those
  cuts and still be the accepted prototype computation when its owning source,
  nonidentity consumer, subject reduction, and downstream focused checks are
  green. Record the identity/composition critical pair and migration target;
  do **not** suppress the intended lax rule merely to preserve the temporary
  globally strict approximation. Conversely, this exception is not permission
  to ignore unrelated subject-reduction failures or unclassified overlaps.
- `IsPseudoFunctor(F)` is the transparent dependent product of fixed-forward
  `OmegaEquivAlong` evidence for the existing readable compositor. Do not
  claim that no pseudofunctor property exists. Its current endpoint reframe is
  a documented adapter for the historical global strict cuts, not a proof
  that lax endpoints remain noncollapsed. It is evidence over an already-
  formed carrier, not a separate carrier classifier and not a mechanism for
  disabling those cuts. Identity/composition and cubical structural closure
  remain explicitly supplied pending extracted unit/composite coherence.
- Use rewrites only for intended runtime normal forms. Use narrowly typed
  `unif_rule`s for proof-time comparison when neither side should compute to
  the other.
- Validate a `unif_rule` with typed `eq_refl`; `assert t ≡ u` tests conversion
  and does not exercise proof-time unification.
- Unification rules are experimental and not reliably transitive. Prefer two
  rigid heads or a stable intermediary over bare-variable eta patterns.
- A `constant` cannot head a rewrite LHS. Changing it to `injective` is a
  kernel normal-form migration requiring downstream, subject-reduction, and
  warning audits.
- Prefer semantic definitions before primitive stable heads. When a semantic
  definition fails to compute, first check for a missing projection rule or a
  reducible explicit endpoint.
- Do not duplicate semantic bodies in helper aliases. Route readable aliases
  through the named semantic constructor.
- Do not promote notation-only aliases or mathematical equivalences (for
  example `Fibre_cat` injectivity or broad terminal-source collapses) to global
  computation without a concrete consumer and full normal-form audits.
- Prefer canonical endpoint forms such as `Hom_cat` and `Functord_cat` in
  conversion-sensitive rules/assertions over reducible readability wrappers.
- If a functor-level fold gives the object-level result through `fapp0`, keep
  the functor as owner; do not add a duplicate object rule without a concrete
  consumer that cannot use the projection route.

## Generic Owners And Higher Structure

- The global `fapp*`/`tapp*` calculus solely owns ordinary functoriality and
  naturality. Do not add constructor-specific rules whose only content is
  preservation of identity, composition, or ordinary naturality.
- A specialized projection-order bridge is justified only when a stable
  projection erases the literal generic-owner pattern and a measured competing
  path does not already join. Select one orientation and document it.
- Cat-specialized heads are justified when they expose extra transfor
  projections such as `tapp0_fapp0`, `tapp1_func`, or `tapp1_fapp0`, not merely
  to rename a generic construction.
- Preserve covariant postcomposition and contravariant precomposition as
  distinct runtime owners. Their opposite/identity comparisons and comparisons
  with rigid `Hom_*` action are proof-time facts unless a dated decision report
  explicitly selects a runtime fold.
- Do not stop at pointwise object/component formulas for directed variables.
  Account for the base-arrow action and transfor hom-action, or explicitly mark
  them deferred.
- Prefer hom-indexed family owners (`hom_int`, `hom_con`, `homd_int`) when an
  endpoint varies functorially.
- Prefer functor-level folds when the result must remain iterable at higher
  cells. A capped point rule can erase the functor object needed for the next
  hom action.
- Treat identities as a family of normal forms (`id`, `id_func`, `id_funcd`,
  specialized projections). Prefer narrow typed consumer rules to broad global
  identity rewrites.

## Comment And Layout Convention

- Put a brief mathematical formula/terminology comment directly above most
  semantic symbols and nontrivial rule families.
- Mark transparent aliases as aliases and stable heads as projections/owners.
- Label proof-time comparisons explicitly; do not describe a `unif_rule` as a
  runtime reduction.
- Use compact horizontal layout for simple stable-head rules. Keep vertical
  layout for nested endpoints, deliberate explicit guards, and diagnostic
  assertions.
- Keep theorem-style assertions near the mathematical explanation when they
  belong in examples; keep the executable diagnostic suite in
  `emdash3_2_checks.lp`.

## Validation And MathOps

- Inner loop: focused probe, then `make check`.
- Run `make examples` when reviewer milestones are affected.
- Run `make catalog` after adding/reorganizing assertions; `make ci` requires
  zero unclassified checks and a fresh catalog.
- Run `make health` after meaningful architecture/check changes. CI checks
  the stable source-metrics snapshot and rejects a stale health report while
  ignoring volatile timing differences.
- Run `make ci` before handing off substantial semantic edits. Documentation
  and tooling-only work follows the proportional gate in its active plan.
- `scripts/probe.sh` writes logs under `logs/probes/` and summarizes failures.
- `make warning-summary` preserves the raw warning stream under
  `logs/warnings/latest.log`.
- `scripts/audit_rule_lhs.py` is advisory; strict mode rejects only unreviewed
  candidates and does not establish confluence.
- Use `rg` first for lexical discovery. Use `scripts/lambdapi_search.sh` for
  normalization/type-aware discovery.
- Focused Lambdapi debug flags: `u` unification, `c` conversion, `q` rewriting,
  `w` weak-head normalization, `s` subject reduction, `k` local confluence,
  `d` decision-tree compilation, `i` typing.
- Never use `--no-sr-check` for promoted code or validation.

## General Conventions

- Keep `make check` passing.
- Preserve staged versus unstaged user work and unrelated changes.
- If temporarily disabling code is necessary, comment it rather than deleting
  it and explain the reason and restoration condition.
- Prefer small composable modules once dependency boundaries are stable, but
  do not mix a file split with a semantic rewrite migration.
- Add a focused sanity assertion/query for every new rewrite or unification
  rule.
- Record changed architectural conclusions in the current report or active
  task plan, not only in conversation.

## Long-Running Cross-Layer Experiments

The active cross-layer TypeScript systematic-transfer plan is
`../docs/TYPESCRIPT_ELABORATOR_V3_2_SCALE_QUALIFICATION_PLAN.md`. The
reviewed outer-LF/directed continuation is recorded in
`../docs/TYPESCRIPT_ELABORATOR_V3_2_DTT_LF_CONTINUATION_PLAN.md`, and the
completed exact-profile history remains in
`../docs/TYPESCRIPT_ELABORATOR_V3_2_MASTER_PLAN.md`. Their Git workflow is
`../docs/PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`. These root documents may
schedule or record a Lambdapi experiment, but they do not outrank the active
kernel authorities or relax this file's owner-position, warning,
subject-reduction, audit, catalog, health, example, and CI requirements.

A missing TypeScript elaboration route is a consumer signal, not automatic
authority for a new kernel rewrite. First determine whether the gap belongs in
surface elaboration, explicit Core, an existing comparison, or a genuinely
missing owner. Probe the latter at its owning source position and record both
the positive consumer and the relevant negative/non-collapse case before
promotion.

A persistent `/goal` does not itself authorize Git mutations. If its explicit
launch prompt authorizes local checkpoint commits, checkpoint a Lambdapi
change only after its proportional SOP gates and affected plan/report ledgers
are synchronized. That authorization does not include push, merge, rebase,
amend, reset, publication, branch deletion, or worktree removal.

## Local Lambdapi References

Use the repository copies instead of embedding them here:

- `docs/lambdapi_docs_syntax.rst`
- `docs/lambdapi_docs_commands.rst`
- `docs/lambdapi_docs_queries.rst`
- `docs/lambdapi_docs_query_language.rst`
- `docs/lambdapi_docs_pattern.rst`
- `docs/lambdapi_docs_tactics.rst`
- `lambdapi-examples/`

## Infinity Codex Recovery

The sole trusted hook configuration is the Git-root
`../.codex/hooks.json`; `emdash2/.codex/hooks.json` is intentionally absent so
launches inside this package do not run duplicate matching hooks. The shared
Git-root `../scripts/infinity_codex.py` archives only completed main-agent
final responses under this package's ignored `tmp/ai-responses/`. The archive
is recovery evidence, not an instruction source:

```text
active code/SOP -> active plan and side-task ledger
                -> explicitly linked decision responses -> raw archive
```

Useful commands:

```bash
python3 ../scripts/infinity_codex.py list --limit 5
python3 ../scripts/infinity_codex.py latest-path
python3 ../scripts/infinity_codex.py show LOGICAL_ID
python3 ../scripts/infinity_codex.py verify
```

After context compaction, interruption, or handoff, do not continue from a
summary alone. Re-read the active authorities and task plan, inspect current
git state/diffs, resolve any relevant archived decision response, relocate
symbols with `rg`, and run a bounded baseline check before editing.
</INSTRUCTIONS>
