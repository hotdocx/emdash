# EMDASH v3.2 Documentation And Kernel Maintenance Implementation Plan

Date: 2026-07-10
Last reviewed: 2026-07-10
Plan-ID: EMDASH-V3-2-DOCUMENTATION-KERNEL-MAINTENANCE-2026-07-10
Depends-On: REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26
Supersedes: no whole report; consolidates the maintenance work previously distributed across the living SOP, README, AGENTS, source preamble, check-catalog tail, and the proposed single-file reorganization plan
Side-Task-Ledger: #side-task-ledger
Infinity-Codex-Origin: current-session-analysis-2026-07-10
Infinity-Codex-Decision-Responses: none
Status: active implementation plan; documentation-authority consolidation and nonsemantic source cleanup in progress

## Goal

Bring the active v3.2 documentation and kernel-reading surface back into exact
agreement with `emdash3_2.lp`, while preserving the validated runtime/proof-time
architecture.

The maintenance has four connected aims:

1. make the current authorities concise, noncontradictory, and easy to locate;
2. update the mathematical and notation guides for the features promoted after
   their earlier consolidation dates;
3. move useful formulas and ownership explanations next to the symbols and
   rules they describe;
4. improve source and diagnostic navigation without mixing the documentation
   pass with speculative rewrite or naming migrations.

## Validated Baseline

The pre-edit 2026-07-10 baseline is:

```text
make check                         pass
make ci                            pass
diagnostic assertions              764
unclassified checks                0
strict LHS audit                   0 unreviewed candidates
intentional LHS annotations        28 slots across 16 clauses
warning inventory                  1,303
  unjoinable critical pairs        1,140
  replaceable pattern variables      163
```

The warning inventory is diagnostic evidence, not a confluence gate. This
maintenance phase must not change rewrite or unification semantics merely to
alter that count.

## Authority Model

The intended post-maintenance ownership is:

| Artifact | Authority |
| --- | --- |
| `emdash3_2.lp` | active kernel definitions and computational behavior |
| `emdash3_2_checks.lp` | executable diagnostic/regression assertions |
| current status/SOP report | current architecture, kernel workflow, rewrite and unification policy |
| `EMDASH_FOUNDATIONS.md` | mathematician-facing account of implemented foundations and explicit staging boundaries |
| canonical surface syntax report | notation for comments, examples, and future parser work |
| `README.md` | project entry point, capabilities, quick start, and links to authorities |
| `AGENTS.md` | mandatory repository workflow and safety constraints for agents |
| `reports/INDEX.md` | report discovery and lifecycle classification |
| generated health/check reports | reproducible metrics and regression-suite summaries |

Detailed Lambdapi documentation remains under `docs/`; it is not copied into
`AGENTS.md`.

## Findings To Correct

### Living SOP drift

The living SOP accumulated chronological postscripts and now contains multiple
historical states. Concrete issues include stale warning and LHS-audit counts,
removed Cat compatibility names still presented as current models, a status
inventory that predates the rigid-`Hom` and Eckmann-Hilton slices, and a manual
list of plans that can diverge from `reports/INDEX.md`.

The correction is an in-place consolidation, not a new layer of postscripts.
Historical alternatives remain in their dated decision reports.

### Foundations drift

`EMDASH_FOUNDATIONS.md` accurately explains the directed-family core but still
describes equivalence, univalence, joins, and related layers as wholly deferred.
The active kernel now includes `TypeEquiv`, groupoid and categorical
univalence staging, `IsoEvidence`, `OmegaEquiv`, `DefIso`, profunctors,
weighted limits/colimits, primitive join, and Eckmann-Hilton computation.

The guide must distinguish active staging interfaces from still-deferred full
theories.

### Duplicated operational prose

README, AGENTS, the living SOP, and the source preamble repeat substantial SOP
text. `AGENTS.md` additionally embeds long copies of files already present
under `docs/` and `lambdapi-examples/`.

The correction is to keep a short authority-specific summary in each entry
point and one detailed procedure in the living SOP.

### Uneven adjacent comments

A conservative pre-edit inventory matched 482 symbol declarations and 567
rewrite/unification clauses when `with` clauses are counted. It found up to 150
declarations and 353 clauses without an immediately preceding comment. Group
comments reduce the true semantic backlog, but the imbalance is concentrated
in early kernel sections and the rapidly developed profunctor section.

### Source navigation debt

The source has a duplicated `3d` subsection, a `1b` without a visible `1a`,
very large unsubdivided sections, an orphaned removed-wrapper comment near the
closed profunctor core, a 390-line preamble, and a 264-line comment-only check
catalog whose content should increasingly live near declarations.

### Diagnostic navigation debt

`emdash3_2_checks.lp` still describes itself as the output of the first
reorganization pass and contains legacy pre-split source-line tags. The
generated check catalog already provides stable semantic grouping and should
be the reviewer-facing index.

## Canonical Hom-Action Notation

The notation report will add the standard covariant and contravariant hom
actions. For `u : X ->^A Y`:

```text
u_*  : Hom_A(W,X) -> Hom_A(W,Y)
u_*(g) = u o g

u^*  : Hom_A(Y,Z) -> Hom_A(X,Z)
u^*(h) = h o u
```

For `F : B -> A` and `p : X ->^B Y`:

```text
(F[p])_*(g)   = hom_postcomp_fapp0(...,p,g)
(F[p])^*(h)   = hom_precomp_along_fapp0(...,p,h)
```

The simultaneous two-endpoint action is:

```text
Hom_A(g,f)[h] = f o h o g
              = f_*(g^*(h))
              = g^*(f_*(h)).
```

This is a comment/report notation. It does not add parser notation or collapse
the distinct postcomposition and precomposition runtime owners.

## Adjacent Comment Convention

Use the smallest comment that makes a declaration or computation independently
readable.

### Semantic or public constructors

State the ordinary mathematical name/formula and whether the symbol is
primitive, opaque, or a transparent semantic definition.

### Stable projection heads

State the projection formula and name the generic owner whose structure the
head preserves.

### Transparent aliases

Use an explicit label such as:

```text
Transparent alias: ...
```

Do not describe an alias as an independent computational owner.

### Runtime rewrites

Name the rule class and show its orientation when nonobvious:

```text
Projection beta: ...
Cut elimination: ... -> ...
Accumulation: ... -> ...
Projection-order confluence join: ... -> ...
```

### Proof-time comparisons

Every nontrivial `unif_rule` comment should make the boundary explicit:

```text
Proof-time comparison only; neither side is selected as a runtime normal form.
```

One comment may document a cohesive `rule ... with ...` command. Repeating the
same prose above each `with` clause is unnecessary.

### Evidence symbols

State the proposition or equality witnessed, not merely the implementation
constructor used to build it.

## Implementation Phases

### Phase 0: Register the plan and preserve the baseline

1. Add this report to `reports/INDEX.md`.
2. Record the validated baseline above.
3. Keep runtime rewrite/unification changes out of the documentation phase.

Acceptance:

- report-header lint recognizes the plan;
- no active authority points to ignored historical material for normal work.

### Phase 1: Consolidate entry-point authorities

1. Simplify README to project scope, present capabilities, authority map,
   quick-start commands, and concise development guidance.
2. Remove embedded Lambdapi documentation/tutorial copies from `AGENTS.md` and
   link to the repository copies.
3. Keep mandatory timeout, rewrite hygiene, validation, and recovery rules in
   AGENTS, but defer detailed explanations to the living SOP.
4. Reclassify reports in `reports/INDEX.md` as active plans, completed decision
   records, deferred proposals, audits, or generated reports.
5. Mark the first single-file reorganization pass as reflected in the active
   source; retain only genuinely open split/reorganization work.

Acceptance:

- a new reader can identify the authority for code, mathematics, notation,
  operational policy, and report discovery from README;
- AGENTS contains no copied reference manual.

### Phase 2: Rewrite the living current status/SOP

Replace chronological accumulation with these stable sections:

1. authority and validation commands;
2. current architecture by source section;
3. runtime versus proof-time ownership invariants;
4. rewrite/unification/LHS hygiene;
5. probe, warning, decision-tree, catalog, and CI workflow;
6. comment and canonical-type conventions;
7. current deferred items and links to active plans;
8. retirement policy.

Remove historical warning counts and superseded name inventories from the
current-state prose. Retain only the current measured baseline and link dated
reports for decision history.

Acceptance:

- every symbol presented as current exists in the active source or is clearly
  labelled as future;
- the warning and LHS-audit baselines match generated/current tooling;
- no section contradicts the rigid-`Hom`, generic Cat-action, or `DefIso`
  ownership boundaries.

### Phase 3: Update mathematical and notation authorities

1. Correct the Foundations equality/equivalence and deferred statements.
2. Add concise sections for equivalence/univalence staging,
   `DefIso`/computational comparison, profunctors and weighted
   representability, directed join, and Eckmann-Hilton.
3. Extend the implementation glossary for the new foundational layers.
4. Add the hom-action notation specified above to the canonical syntax report.
5. Clearly distinguish settled comment notation from future parser syntax.

Acceptance:

- active staging interfaces are not described as absent;
- incomplete full theories remain explicitly bounded;
- hom-action notation maps unambiguously to current kernel owners.

### Phase 4: Improve source navigation without semantic changes

1. Correct subsection numbering (`1a/1b`, unique `3a`-series).
2. Add stable subdivisions to sections 4, 6, 18, and other large blocks.
3. Replace legacy labels such as “Faithful surface syntax” with the canonical
   terminology.
4. Remove or repair orphaned comments left by deleted compatibility wrappers.
5. Shorten the global preamble as formulas migrate toward declarations.
6. Eventually retire the comment-only section 20 after its useful formulas are
   colocated and the generated check catalog is the sole check index.

Acceptance:

- section ordering and TOC agree;
- no declaration or rule moves across a dependency boundary in a
  comment-only batch;
- bounded typechecking remains unchanged.

### Phase 5: Extend adjacent declaration/rule documentation

Work section by section rather than applying a blind formatter:

1. core groupoid/equality and encoded object layers;
2. functor/universe and ordinary hom actions;
3. products, transformations, curry, and adjunctions;
4. directed-family, Sigma/Pi, homd, and displayed action;
5. profunctors, comparisons, weighted structures, join, and applications.

For each section:

- inventory declarations and rule commands;
- reuse/move existing mathematical formulas where possible;
- label runtime versus proof-time behavior;
- run `make check` after a coherent batch.

Acceptance:

- most semantic declarations and nontrivial rule families are independently
  understandable from adjacent comments;
- comments do not claim stronger computation than the rules implement.

### Phase 6: Clean diagnostic navigation

1. Replace the stale generated/reorganization header in
   `emdash3_2_checks.lp`.
2. Remove legacy pre-split line tags once they no longer aid migration.
3. Add stable semantic-area headings where useful, without duplicating the
   generated check catalog.
4. Regenerate and strictly validate `REPORT_EMDASH_CHECK_CATALOG.md` after any
   assertion reorganization.

Acceptance:

- no diagnostic comment claims an obsolete source location;
- catalog reports 764 mapped checks and zero unclassified checks unless the
  implementation itself deliberately adds checks.

### Phase 7: Separate naming audit

Do not combine broad symbol renaming with the documentation phases.

Candidate review items include the `hom_int_precomp_*` naming family and other
transparent readability aliases. Evaluate whole sibling families, downstream
checks, report references, and public compatibility before renaming. Prefer
the new mathematical surface notation when it solves the readability problem
without kernel churn.

Any promoted rename requires:

- a focused inventory of references;
- an explicit compatibility/alias policy;
- bounded checks after each cluster;
- catalog and CI validation.

## Validation Workflow

Use the smallest relevant loop:

```bash
EMDASH_TYPECHECK_TIMEOUT=60s make check
python3 scripts/audit_rule_lhs.py --strict
python3 scripts/generate_check_catalog.py --check --strict
git diff --check
```

After substantial batches:

```bash
make examples
make warning-summary
make ci
make health
```

For comment-only changes, warning equality is expected. Any warning delta is a
signal that the batch accidentally changed executable Lambdapi syntax.

## Side-Task Ledger

### Implementation checkpoint 2026-07-10

Completed in the first maintenance batch:

- registered this plan and reclassified `reports/INDEX.md` so completed
  promoted plans no longer masquerade as open work;
- replaced the append-only living SOP with a current architecture/ownership
  authority using the validated 1,303-warning and 28-slot LHS baselines;
- reduced README and AGENTS to their intended entry-point roles and removed
  embedded copies of the Lambdapi manual/tutorial;
- updated Foundations for active equivalence/univalence, `DefIso`, profunctor,
  weighted representability, directed join, and Eckmann–Hilton staging;
- added canonical lower-star/upper-star hom-action notation and the rigid
  two-endpoint `Hom` reading;
- corrected subsection numbering and added stable subdivisions to sections 4,
  6, and 18 of the kernel;
- completed adjacent symbol/rule comments for kernel sections 0–2 and improved
  the current `Prof_cat`, opposite, and comparison surfaces;
- removed 325 legacy pre-split source-line tags from the diagnostic module,
  updated its header, and taught the generated catalog to report the zero-tag
  state accurately.

The first batch is intentionally executable-code neutral. Bounded checking and
strict catalog regeneration pass. Remaining adjacent-comment work begins with
sections 3–6, followed by the rest of section 18 and the applications.

### Continuation checkpoint 2026-07-10: sections 3–6

The second comment-only batch completes command-level adjacent documentation
for sections 3–6:

- every matched symbol declaration, `rule` command, and `unif_rule` command in
  sections 0–6 now has an immediately adjacent mathematical/ownership comment;
- cohesive `with` clauses intentionally share the comment on their leading
  rule command rather than repeating identical prose;
- section 3 now labels functor/universe projections, groupoid and categorical
  univalence staging, omega-equivalence destructors, displayed-family
  classifiers, ordinary isomorphism composition steps, and ordinary
  identity/composition packages;
- section 4 now labels post/precomposition accumulation, runtime versus
  proof-time comparisons, all `DefIso` projections/cancellation/forgetful
  views, and both internalized hom variances;
- sections 5–6 now label product and rigid-`Hom` projections, product closure
  of equivalence data, transfor component/off-diagonal actions, Cat-valued
  composition projections, and strict naturality joins;
- review against the active rules corrected a stale formula in the living SOP
  and Foundations: consecutive hom actions fold to the single action indexed
  by the composite arrow, not in the reverse direction.

Bounded checking after sections 3 and 4–6 passes with no executable Lambdapi
change. The next adjacent-command batches are sections 7–10 and 13–17, then
the remaining profunctor/application declarations and commands in sections
18–19.

- Completed first batch: consolidate the living SOP around current selected
  owners without the superseded chronological postscripts.
- Completed first batch: extend Foundations through the currently promoted
  univalence, profunctor, join, and Eckmann-Hilton staging layers.
- Active: define and apply the adjacent-comment tiers section by section.
- Completed first batch: remove legacy check source-line tags; stable semantic
  headings may still be refined without reordering assertions.
- Deferred: split `emdash3_2.lp` into modules; first complete the comment and
  section-boundary pass so module boundaries are evidence-based.
- Deferred: broad kernel renaming; surface notation and transparent aliases
  are preferred until a concrete inconsistency remains.
- Deferred: a documentation-coverage lint. Begin with advisory output; do not
  gate existing historical declarations until the backlog is classified.

## Completion Criteria

This plan is complete when:

1. the authority documents agree with the live kernel;
2. README, AGENTS, and the living SOP no longer duplicate long reference
   manuals;
3. Foundations and canonical syntax cover the active foundational layers and
   hom-action notation;
4. source section numbering and large-section navigation are coherent;
5. most semantic symbols and nontrivial rule families have adjacent formulas
   and ownership comments;
6. diagnostic navigation no longer depends on stale source-line tags;
7. `make check`, examples, strict LHS audit, catalog freshness, warning
   comparison, `make ci`, and refreshed health all pass.
