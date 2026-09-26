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

Research qualification: the current whole-opposite, Sigma-Hom and connected
family/section encodings have known variance/strictness defects. The
[opposite](../docs/TYPESCRIPT_EMDASH_INTERNAL_OP_VARIANCE_DIAGNOSTIC.md),
[Sigma-Hom](../docs/TYPESCRIPT_EMDASH_SIGMA_HOM_VARIANCE_DIAGNOSTIC.md),
[Homd target](../docs/TYPESCRIPT_EMDASH_HOMD_TARGET_POLARITY_DIAGNOSTIC.md)
and [family/section profile](../docs/TYPESCRIPT_EMDASH_FAMILY_SECTION_PROFILE_DIAGNOSTIC.md)
diagnostics record the evidence and qualifications. Their reproducer fixtures
are non-library audits, not positive examples or a consistency certificate.
Do not use invalid higher action to justify a result. Legitimate local Op
computations with an independently qualified ordinary interpretation are
not blanket-prohibited.

The user has authorized action-profile integration in the dedicated
`goal/action-profile-integration-v3.2` worktree under the
[living integration plan](../docs/EMDASH_ACTION_PROFILE_INTEGRATION_PLAN.md).
Op/duality repair and further Empty audits remain deferred. Preserve
hom_int/homd_int as foundations and the checkpoint/resumption bundle in
`audits/deferred_native_homd_y/README.md`. The selected native duality design
is a proposal; external set-of-dimensions semantics is not an implementation
API. No current homology maintenance task authorizes resuming that migration.
Spectral/stabilization research is also deferred.

## Authority And Document Roles

The [current architecture report](reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md)
owns implementation status and source locations; [Foundations](reports/EMDASH_FOUNDATIONS.md)
owns the mathematical explanation. [The report index](reports/INDEX.md) routes
to plans by lifecycle. Current native homology/universality qualification is
recorded in the [native audit](../docs/TYPESCRIPT_EMDASH_NATIVE_UNIVERSALITY_FINAL_AUDIT.md)
and [assembly audit](../docs/TYPESCRIPT_EMDASH_CATEGORICAL_UNIVERSALITY_FINAL_AUDIT.md).
Dated publication, owner and tranche details formerly repeated here are
preserved in [historical routing](reports/history/OWNER_ROUTING_THROUGH_2026-09-23.md).
They do not authorize new work or override the constraints below.

Preserve these consumer boundaries:

- Native homology uses whole J⊣K/Q⊣I, H and direct δ, canonical exactness and
  general native snake/LES comparison. Model, normality and interpretation
  contracts remain supplied; output exactness is derived. Ordinary record
  views are downstream observations, not mandatory primary inputs.
- Structural ordinary adjunction/terminality and diagram-realization owners
  retain their OneCat/discrete guards. Whole Hom-comparison assembly and Γ/H
  preserve actual inverse data and the original K/Q. Point comparisons do not
  establish whole parameter action. Preserve the composite-argument guard on
  the postcomposition view used by paired-family reindexing.
- The large six-term package comparison remains deferred under
  [its replay boundary](audits/native-six-term-observation-boundary/README.md).
  Do not resume it or old endpoint experiments as routine maintenance.
- The general native snake retains arbitrary outer a,c; do not add monic-a or
  epic-c restrictions or an old/new compatibility requirement. Retired model
  facades, DefIso normalizers and the obsolete snake route stay retired;
  shared CAS inputs and useful ordinary observations retain native consumers.
- Raw relation preservation, quotient equality and universal model/provider
  semantics are distinct. A finite list of matrix equations cannot supply a
  closed quotient-effective model or extract a chosen matrix witness from
  arbitrary truncated equality. Preserve actual ranks, projections, Ω witnesses,
  computational inverses and all-test factor contracts.
- IsoEvidence laws and proof-time observations are not new runtime inverse
  cuts. Generic whole operations, structural declarations and derived bodies
  must retain their distinct status in source, book and frontend claims.

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

Use the [source catalogue](reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md#sources-of-truth)
for exact extension owners; search source before relying on a dated spelling.

| Work | Start at |
| --- | --- |
| Generic action, hom/homd, Sigma/Pi, adjunctions and cuts | `emdash3_2.lp`; `fapp*`/`tapp*` remain generic coherence owners |
| Primary K/Q, H and native inputs | `emdash3_2_kernel_cokernel_adjunctions.lp`, `emdash3_2_homology_adjunction_families.lp`, `emdash3_2_homology_adjunction_input_data.lp` |
| Native snake and direct connecting map | `emdash3_2_one_cat_native_snake_connecting.lp`, `emdash3_2_one_cat_native_snake_six_term_result.lp` |
| Supplied Freyd model and displayed proof–CAS evidence | `emdash3_2_commutative_algebra_freyd_adjunction_models.lp` and the native diagram-exactness owners named by the final audit |
| Γ and ordinary Hom/Adjunction assembly | `emdash3_2_represented_comma_families.lp`, `emdash3_2_one_cat_hom_comparison_data.lp`, `emdash3_2_one_cat_adjunction_introduction.lp` |
| Products and slice computation | `emdash3_2_triangular_binary_products.lp`, `emdash3_2_pullbacks.lp`, `emdash3_2_slice_dependent_products.lp`; general `Pi_along_func` is separate |
| Geometry, groupoidal/directed HITs, cubical/simplex extensions | One-way modules in the source catalogue; cubical action derives from Sigma/opposite/homd, not a second square theory |
| Diagnostics and independent consumers | `emdash3_2_checks.lp` and `examples/`; neither replaces the owning declaration |

`IsStrictFunctor`/`IsPseudoFunctor` constrain existing compositor action; they
are not a second functor grammar or automatic judgmental reflection. Opposite
instances and ordinary reconstruction do not establish unrestricted inverse
laxity, higher diagram eta or a `Groupoidify` adjunction.

The completed successor branch `goal/opaque-action-profile-classifiers-v3.2`
at `114dc19f` is the pinned source for this integration. The
[continuation review](../docs/TYPESCRIPT_EMDASH_FOUNDATIONS_DEVOPS_AND_CONTINUATION_REVIEW.md#completed-action-profile-branch)
owns its exact worktree/plan recovery and selective migration proposal. Do not
copy its counts or claim main already has its lax/profile behavior.

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

`checks.json` owns the operational core/reviewer suites, staged groups and
named profiles. Register new active sources there; `scripts/check_registry.py`
rejects unregistered files and unresolved imports. The root
[`DevOps guide`](../docs/DEVOPS.md) documents shared local/CI selection and
receipts. Book architecture and claim identity remain at their existing owners.

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
- Qualified native six-term input check:
  `scripts/check_native_snake_six_term.sh examples/one_cat_native_snake_six_term_inputs.lp`
- Retained ordinary exactness support: `scripts/check_ordinary_exactness_support.sh`
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

For any repository Lambdapi task, distinguish import cost, type formation,
construction and the first real consumer before changing formal interfaces.
Preserve exact source/dependency versions, flags, resource limits, runtime
parameters and logs. A constructor passing does not qualify its projections
or an end-to-end consumer; separate historical failures need separate checks.

For an allocation failure, one useful control is:

```bash
OCAMLRUNPARAM=o=20,v=1024 EMDASH_LAMBDAPI_WARNINGS=1 \
  scripts/probe.sh path/to/affected.lp
```

The installed OCaml 5.4 `gc.mli` documents default `space_overhead=120`:
a smaller value collects unreachable major-heap blocks more eagerly, at a
possible CPU cost. `ocamlrun.1` maps this field to `o`; `v=1024` reports exit
GC statistics and can be omitted for routine checks. Verify the installed
runtime documentation when versions change. `allocated_words` is allocation
traffic, while `top_heap_words` is heap size in runtime words, not process
RSS or total address space. Measure time as well as memory.

This command changes collection frequency, not checker logic, proof terms,
rewrite/unification rules, chosen inverses, opacity or the memory ceiling.
Keep it scoped and log the effective `OCAMLRUNPARAM`/`CAMLRUNPARAM`, including
wrapper defaults; do not reuse performance evidence across different runtime
settings. GC tuning cannot guarantee success for excessive live data,
nontermination or invalid types. After a success, check the actual required
consumer. A larger-limit experiment needs authorization, a measured bounded
target and the same serialization/file/deadline/no-swap restrictions; preserve
and restore the normal guard. No unbounded fallback is permitted.

The 2026-09-15 native snake and earlier combined pair/certificate constructor
replays demonstrate this technique at 2GiB without changing their source.
Their exact scope and measurements live in the native snake/model plans;
they do not establish that all old endpoint or inverse-projection failures
are fixed. This procedure is repository-wide, not specific to those goals.

Interactive probes now run through `scripts/lambdapi_resource_guard.sh`:
one checker at a time, 2 GiB address space per process by default, 64 MiB per
file, no core dumps and a hard deadline (90 seconds by default). On this workstation its
user-systemd scope additionally limits aggregate test/descendant memory to
the chosen limit (2 GiB by default) and disables swap. The `prlimit` fallback is per-process only. Do not
bypass this guard for expensive normalization experiments or alternate
checker binaries. Apply it to each command in a staged gate, not to the
whole multi-target gate; resource exhaustion is not a mathematical
counterexample. The active homology plan records the motivating global OOM
events and requires serial, memory-bounded compiler experiments too.

User direction for the native-universality goal (2026-09-14) permits reviewed
time-limit increases. The guard now accepts an explicit `EMDASH_LP_TIMEOUT`
up to 600 seconds, while retaining the 90-second default and the existing
file/serial restrictions. Use an increased limit only for a measured
target, recording the reason, exact limit and result in its living plan.
The first selected experiment is the complete bounded model adoption with
its second connecting/reuse pass. A time increase does not resolve a memory
failure or qualify an incomplete computation. Longer probes use the existing
`EMDASH_PROBE_TIMEOUT` override; do not bypass the guard or subject reduction.

The same user authorization permits reviewed memory increases. The guard
accepts an explicit `EMDASH_LP_MEMORY_MIB` up to 6144 while retaining its
2048 default. `scripts/check_native_snake_pairs.sh` selects the measured
6 GiB/180s profile only for its registered pair/certificate owners and
reviewer. Keep the normal guard, serial lock, file/core limits and no-swap
scope; record resource measurements and do not turn this into a global
default increase. Guard/profile tests exercise the bounds without allocating
large heaps.

User direction for the action-profile integration goal (2026-09-26) provides
standing authorization for any needed measured memory/timeout increases,
without further approval questions. This authorization already satisfies the
larger-limit permission requirement above. Keep the 2 GiB/90-second normal
defaults and use explicit target-specific profiles, recording reasons,
measurements and remaining limitations in the integration plan. Preserve
subject reduction, the serial lock, file/core limits and no-swap scopes.
Use the existing guard's supported limits where sufficient; a necessary guard
extension must remain bounded and receive its own validation.

For Node 24.11.1 here, isolated `node --test` workers do not inherit V8 heap
flags supplied only on the command line. Pass those limits through
`NODE_OPTIONS` and verify the worker's `v8.getHeapStatistics().heap_size_limit`.
Check this inside an actual test worker; do not infer its heap limit from
launcher arguments. The OS guard remains independently enforced.
For large proof–CAS fixtures, compile only the affected TypeScript dependency
tree and run its JavaScript output before comparing heap measurements. A
resident ts-node/compiler changes that footprint: the consolidation LES run
exhausted 512MiB under ts-node, while unchanged compiled JS passed at the
same V8/OS limits. This is a runner change, not a proof or unfolding change;
record both the compiler inputs and the actual worker flags.

Early-development hangs can signal rewrite/unification trouble. Keep
every Lambdapi invocation bounded by its recorded per-target deadline.
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

Source-generating Python helpers are authoring/replay tools, not proof
checkers. Preserve their small inputs, unique insertion/replacement guards,
source/dependency hashes and explicit emitted LP. Qualify the emitted source
at its owning position. Retire scratch builders after promotion; retained
non-library audits need status, expected outcomes and a replay trigger. Use
Git for retired implementations, rather than an ignored alternative library.

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
  rigid heads or a stable intermediary by default. This is not a blanket
  impossibility claim for variable-sided rules: the exact terminal-uniqueness
  candidate in `audits/terminal-uniqueness-unification/README.md` passes a typed
  reflexivity consumer, with a failing no-unifier control and negative runtime
  conversion observation. The user requires this fact to inform further design.
  Promotion still needs actual-consumer and inference/interaction qualification.
  The [terminal-object/product review](audits/terminal-product-unification-review/README.md)
  adds a rigidity qualification: the installed checker rejects variable–constant
  clashes before custom unifiers. Forward product-path reflexivity already
  passes without pair η; use no-rule and contextual controls before claiming
  a new rule provides stronger behavior. No candidate is installed.
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

## Synthetic Computational Interfaces

- For coherently varying mathematical data, expose the existing whole functor,
  transformation or dependent-Hom owner first. Obtain objects, components and
  higher action by its projection ladder. Do not invent a universal family for
  an arbitrary isolated arrow without a mathematical parameterization.
- Prefer whole adjunctions, represented Hom comparisons and retained universal
  maps for categorical constructions. End users should not rebuild ordinary
  functoriality/naturality from per-instance square equations. A need to do so
  triggers review of a missing owner, projection or profile.
- “Whole” retains the selected strict/lax/pseudo action; it does not imply
  strict naturality. Additional structure still needs its actual capability.
  Preserve hom_int/homd_int, existing primitives and generic cut owners.
- Use actual maps with retained inverses for operational changes of categorical
  presentation. Paths remain appropriate for groupoidal/HoTT structure,
  ordinary truncated laws, CAS equations and downstream observations. Audit
  operational casts and transported inverse data, not occurrences of `=`.
- Distinguish derived definitions, declared structural constructors,
  proof-time agreements and runtime reductions. Do not describe a newly
  supplied whole contract as a theorem derived from earlier beta rules.

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
- Keep an earlier Hom head stable when eagerly expanding it would bypass its
  established generic cuts. Recursive next-Hom refinement can expose further
  action through the existing owners. Check whole-versus-capped application
  orders and identity/composition observations; the recursive Sigma reviewer
  records a concrete instance of this distinction.
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
- `scripts/probe.sh` uses the shared runner. New raw logs and immutable receipts
  live under `logs/check-runs/`; exact input blobs live under `logs/check-inputs/`.
  Earlier `logs/probes/` records remain historical evidence. Staged recipes
  retain per-child guards and receive explicitly scoped group receipts.
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
