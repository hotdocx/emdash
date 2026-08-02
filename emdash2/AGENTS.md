<INSTRUCTIONS>
## Goal

`emdash` is a Lambdapi specification for functorial programming and a future
proof assistant for strict/lax omega-categories, omega-functors,
omega-transformations (“transfors”), directed families, and related dependent
categorical structures.

The active kernel is `emdash3_2.lp`. The one-way derived native equality-valued
hom-action/groupoidality extension is `emdash3_2_eq1_hom_action.lp`;
the Cat-valued presheaf, Yoneda, slice, and higher-sieve library is
`emdash3_2_presheaves.lp`;
the native subterminal-category and ordinary-sieve specialization is
`emdash3_2_sieves.lp`;
the direct ordinary-sieve Grothendieck-topology library is
`emdash3_2_sites.lp`;
the transparent native equality-valued evidence-property and finite-dimension truncation
extension is `emdash3_2_eq1_evidence_property.lp`;
the reusable Nat arithmetic/sethood extension is
`emdash3_2_nat_arithmetic.lp`;
the reusable Nat-indexed finite-family extension is
`emdash3_2_finite_families.lp`;
the set-carrier commutative-ring object extension is
`emdash3_2_commutative_algebra.lp`;
the structured commutative-ring morphism/category extension is
`emdash3_2_commutative_algebra_category.lp`;
the finite-sum/unimodular/Zariski-cover-presentation extension is
`emdash3_2_commutative_algebra_finite.lp`;
the universal-property polynomial-algebra extension is
`emdash3_2_commutative_algebra_polynomial.lp`;
the universal-property-first one-element localization extension is
`emdash3_2_commutative_algebra_localization.lp`;
the universal-property iterated/product-localization comparison extension is
`emdash3_2_commutative_algebra_localization_comparison.lp`;
the CommRing-valued-presheaf, restriction, arrowwise-invertibility, and
ordinary-invertibility-sieve extension is
`emdash3_2_commutative_algebra_presheaves.lp`;
the topology-visible invertibility-cover and memberwise localization-factor
extension is `emdash3_2_commutative_algebra_locality.lp`;
the localization-element to coherent matching-family extension is
`emdash3_2_commutative_algebra_matching.lp`;
the presented finite basic-open Zariski-cover, selected containment, and
bounded family base-change extension is
`emdash3_2_commutative_algebra_zariski.lp`;
the supplied Grothendieck-topology compatibility extension for those selected
Zariski presentations is
`emdash3_2_commutative_algebra_zariski_topology.lp`;
the selected walking-endomorphism directed-HIT/`BNat` extension is
`emdash3_2_walking_end_hit.lp`;
executable diagnostics live in `emdash3_2_checks.lp`.

## Authorities

Use the following order:

1. `emdash3_2.lp` for active kernel definitions and computation;
2. `emdash3_2_presheaves.lp` for the rigid Cat-valued presheaf facade,
   restriction along opposite functors, transparent Yoneda and slice
   presentations, and explicitly Cat-valued higher sieves;
3. `emdash3_2_eq1_hom_action.lp` for the transparent derived native
   equality-valued
   next-hom and groupoidality layer;
4. `emdash3_2_eq1_evidence_property.lp` for transparent native equality-valued
   evidence-property, retract-truncation, and finite-`NCat` object-truncation
   theorems;
5. `emdash3_2_sieves.lp` for native subterminal categories, ordinary sieves
   as the pointwise-subterminal specialization of higher sieves, and ordinary
   pullback; it deliberately does not declare `Omega` or topology;
6. `emdash3_2_nat_arithmetic.lp` for reusable Nat addition, associativity,
   Unit/Empty proposition evidence, and Nat sethood;
7. `emdash3_2_finite_families.lp` for Nat-indexed right-associated finite
   families, constructors/projections, pointwise map, dependent pointwise
   evidence, evidence over already-selected dependent evidence, its generic
   pointwise map, and retained sethood;
   it deliberately declares no `Fin`, lookup, list/Sum/inductive interface,
   append, permutation quotient, or package eta;
8. `emdash3_2_commutative_algebra.lp` for set-carrier commutative-ring
   operations and laws, readable projections, and the one-element zero-ring
   model; this object module deliberately declares no morphism/category,
   localization, finite-family, power, or polynomial interface;
9. `emdash3_2_commutative_algebra_category.lp` for structured ring morphisms,
   proposition/sethood proofs, transparent explicit-map observations,
   consumer-justified pointwise extensionality, the `CommRing_cat` facade, and
   the narrowly selected stable pointwise identity/composition comparisons;
   its whole-sieve consumer selects the full-action carrier functor and
   Path-valued carrier family without a competing direct capped-action rule;
   it deliberately declares no localization, finite-family, power, or
   polynomial package;
10. `emdash3_2_commutative_algebra_finite.lp` for finite ring sums/dot
    products, structured-map preservation, retained unimodular coefficient
    presentations, and algebraic Zariski-cover presentation data; it
    deliberately declares no `Spec`, localization family, coverage/topology,
    power/radical, fraction, polynomial, quotient, or mere-existence claim;
11. `emdash3_2_commutative_algebra_polynomial.lp` for free commutative
   `R`-algebras on a variable classifier, expressed by contractible
   structured extensions of base maps and valuations; it deliberately
   declares no monomial/coefficient/quotient syntax, positive-variable
   representation, finite-index facade, runtime rule, unifier, or package
   eta;
12. `emdash3_2_commutative_algebra_localization.lp` for proposition-valued
   unit evidence, unit path transport and structured-map preservation,
   pointwise factor triangles, contractible-factorization localization
   packages, the Path-valued unit-evidence family over total ring elements,
   and named transparent observations; it deliberately declares no concrete
   fractions, iterated comparison, finite-family, power, polynomial, or
   Zariski interface;
13. `emdash3_2_commutative_algebra_localization_comparison.lp` for unit
    multiplication lemmas, the selected stable pointwise ring-map composite
    consumer, two-stage localization packages, and canonical forward/reverse
    comparison factors with pointwise triangles; it
    deliberately declares no fraction syntax, equality of chosen localization
    packages, comparison inverse laws, finite-family, polynomial, or Zariski
    interface;
14. `emdash3_2_commutative_algebra_presheaves.lp` for the transparent
   CommRing-valued presheaf classifier, actual structured restriction maps,
   pointwise identity/composition paths, and proposition-valued arrowwise
   invertibility support closed under restriction; it assembles the
   Path-valued higher support and ordinary invertibility sieve through the
   carrier/unit families and one shaped proof-time variance comparison while
   preserving literal-arrow membership computation. It deliberately declares
   no topology, sheaf, or ringed-site package;
15. `emdash3_2_sites.lp` for ordinary-sieve membership, the canonical maximal
   sieve, proposition-valued sieve coverages, Grothendieck topology laws, and
   the direct chaotic-topology model; it declares no `Omega`, generated
   coverage saturation, sheafification, or descent;
16. `emdash3_2_commutative_algebra_locality.lp` for the coverhood view of the
   already-computing semantic invertibility sieve and the universal-property
   localization factor selected at each literal support member. It packages
   the factors as one internal ordinary transformation from the constant
   localization ring to the CommRing-valued diagram over the support's
   elements category; its one component rule exposes the selected factor, and
   generic `tapp1` owns naturality. Contractible-factor uniqueness separately
   derives the objectwise restriction equation as construction evidence. It
   has a closed zero-ring computation but deliberately claims no limiting
   cone/descent equivalence, sheaf, ringed-site package, generated topology,
   `Spec`, or scheme;
17. `emdash3_2_commutative_algebra_matching.lp` for the Path-valued carrier
   family over support elements, its Pi category of internally coherent
   matching families, and the functor sending a localization element and its
   equality paths to the corresponding matching section. Its one literal
   component rule uses the selected full fibre-covariance carrier action;
   generic Pi/Catd/PathLift owners retain coherence and arrow action. It
   deliberately supplies no inverse/glue, descent equivalence, sheafhood,
   limiting claim, generated topology, `Spec`, or scheme;
18. `emdash3_2_commutative_algebra_zariski.lp` for selected finite families
   of universal-property localizations, presented affine basic-open arrows,
   elementwise localization base-change factors and triangles, and returned
   ordinary-sieve pullback membership. It also retains explicit containment
   for every selected basic open, accepts a mapped presentation's target
   localization family, and exercises bounded singleton assembly through the
   generic finite owner. It is rule-free and deliberately declares no global
   localization choice, specialized rigid membership facade, propositional
   truncation, generated coverage/topology, subcanonicity, `Spec`, or scheme;
19. `emdash3_2_commutative_algebra_zariski_topology.lp` for the rule-free
   property and package saying that every sieve containing a selected finite
   Zariski basic-open presentation covers in an already supplied topology on
   `Op_cat CommRing_cat`. It retains presentation and membership data, proves
   compatibility is proposition-valued, and provides only the chaotic topology
   as a feasibility model; it does not construct the least/generated Zariski
   topology, choose localizations, or declare truncation, sheafification,
   subcanonicity, `Spec`, or schemes;
20. `emdash3_2_walking_end_hit.lp` for the selected concrete walking-
   endomorphism directed-HIT/`BNat` model, eliminator, comparison, and
   directed negative results;
21. `emdash3_2_checks.lp` for executable regression statements;
22. `reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`
   for current architecture and development SOP;
23. `reports/EMDASH_FOUNDATIONS.md` for the mathematical reading;
24. `reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`
   for comment/example notation;
25. `reports/INDEX.md` for task-specific plans and decision records.
26. `book/book.json` and `book/evidence.json` for book source
   order and prose-to-check traceability; book prose never outranks active
   Lambdapi sources.

The former D0/D1/decoder compatibility module and its self-only reviewer
examples are retired. The selected API is the unsuffixed native
equality-valued representation; do not recreate compatibility aliases. Native
`OneCat` structure, hom action, truncation, the one-way ordinary-isomorphism
lift, and WalkingEnd/Nat results remain active. A full native
object-equality/ordinary-isomorphism equivalence is optional future work, not a
compatibility prerequisite.

The obsolete v2/v3.1 material under ignored `.scratchpad/` directories is not
part of normal development. Do not read, summarize, or reference it unless the
user explicitly requests historical recovery. Use
`reports/REPORT_EMDASH_V2_RETIREMENT_AUDIT_2026-06-16.md` when the obsolete v2
retirement summary is relevant.

## Starting A v3.2 Task

Before nontrivial edits:

1. read the active implementation, checks, current SOP, Foundations, and
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

Early-development hangs usually signal rewrite/unification trouble. Use a
timeout no longer than 60 seconds:

```bash
EMDASH_TYPECHECK_TIMEOUT=60s make check
timeout 20s lambdapi check emdash3_2.lp
EMDASH_LAMBDAPI_WARNINGS=1 EMDASH_TYPECHECK_TIMEOUT=20s make check
```

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
- Run `make ci` before handing off substantial edits.
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
