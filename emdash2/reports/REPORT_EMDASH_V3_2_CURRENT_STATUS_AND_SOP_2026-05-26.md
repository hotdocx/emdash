# EMDASH v3.2 Current Status And SOP

Date: 2026-05-26
Last consolidated: 2026-07-10
Status: living current-state and kernel-development authority

This report describes the active `emdash3_2.lp` architecture and the procedure
for changing it safely. It intentionally records the current selected design,
not the chronological sequence of earlier candidates. Dated implementation
plans in `reports/INDEX.md` retain decision history, rejected orientations, and
detailed probe evidence.

## Sources Of Truth

- `emdash3_2.lp`: active kernel definitions and runtime/proof-time behavior.
- `emdash3_2_checks.lp`: executable diagnostics and regressions.
- `EMDASH_FOUNDATIONS.md`: mathematical reading guide.
- `REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`: notation
  authority for comments, examples, and future parser work.
- `INDEX.md`: active plans, completed decision records, audits, and generated
  reports.
- `REPORT_EMDASH_CHECK_CATALOG.md`: generated map of the diagnostic suite.
- `REPORT_EMDASH_HEALTH.md`: generated source metrics and bounded timings.

The active source outranks every report if they disagree. Correct the report
as part of the same maintenance task rather than preserving a known stale
description.

Ignored `.scratchpad/` material is historical recovery data, not a normal
authority. Use the v2 retirement audit when an obsolete-baseline summary is
needed.

## Validated Current Baseline

The 2026-07-10 baseline is:

```text
make check                         pass
make examples                      pass
make ci                            pass
checked files/examples             8
diagnostic assertions              764
unclassified checks                0
strict LHS audit                   0 unreviewed candidates
intentional LHS annotations        28 slots across 16 clauses
warning inventory                  1,303
  unjoinable critical pairs        1,140
  replaceable pattern variables      163
```

The largest warning families are headed by `comp_fapp0`,
`hom_postcomp_fapp0`, `tapp0_fapp0`, and `fapp1_fapp0`. These reports are
diagnostic evidence for locating overlap families. They are not an automatic
veto on semantically required computation and are not a confluence proof.

`emdash3_2.lp` contains no executable `assert` commands. Diagnostics live in
`emdash3_2_checks.lp`; reviewer-facing milestones live in `examples/`.

## Current Architecture

### Sections 0–3: kernel foundations

The kernel begins with the groupoid/type universe, equality/path induction,
encoded Sigma/Pi/product object layers, and the core category interface.

Active equality/equivalence staging includes:

- `TypeEquiv` with forward/inverse maps and inverse paths;
- path views for encoded Sigma and Pi types;
- `GrpdUnivalence` and decoder-based groupoid-univalence capabilities;
- `IsoEvidence` for ordinary categorical isomorphism data;
- `CatIsoUnivalence` for the 1-categorical staging layer;
- recursive `OmegaEquiv` with identity/opposite/product closure;
- `CatUnivalence` and decoder-based omega-categorical univalence
  capabilities.

These are explicit kernel interfaces and checked computation skeletons. They
do not claim that every future univalence/coherence theorem is already
internalized.

The category universe satisfies the directed-universe principle:

```text
Obj(Cat_cat) = Cat
Hom_cat Cat_cat A B = Functor_cat A B.
```

`Catd_cat K` is the canonical Cat-valued-functor category over `K`.
`Functord_cat` and `Transfd_cat` provide natural/displayed functor and transfor
layers.

Generic identity, composition, functor action, and naturality are owned by the
global `id`, `comp_fapp0`, `fapp*`, and `tapp*` calculus. Specialized
`id_func`, `id_funcd`, `comp_cat_fapp0`, and `comp_catd_fapp0` spellings are
transparent public views or specialization surfaces, not parallel owners.

### Section 4: ordinary internal hom and variance-separated actions

The represented covariant family is:

```text
hom_(F,W)[y] = Hom_A(W,F[y]).
```

Its postcomposition action is owned by the `hom_postcomp_*` hierarchy:

```text
(F[p])_*(g) = F[p] o g.
```

The represented contravariant family is primitive:

```text
hom_con(W,F)[y] = Hom_A(F[y],W).
```

Its precomposition action is owned by `hom_precomp_along_*`:

```text
(F[p])^*(h) = h o F[p].
```

`hom_int(F)` internalizes the represented source object; `hom_con_int(F)` is
the target-internalized mirror. Both expose their off-diagonal actions through
the rigid two-endpoint hom action:

```text
Hom_func(g,f)[h] = Hom_fapp0(g,f,h) = f o h o g.
```

Runtime normalization preserves the postcomposition, precomposition, and
rigid-`Hom` provenance. Opposite/identity presentations, independently
factored pre/post cuts, and one-inactive-endpoint degenerations are related by
narrow two-rigid-head `unif_rule`s. They are not global runtime folds.

`Hom_tele_func`, `Hom_func`, and `Hom_fapp0` retain focused runtime identity
and composition joins because projection can hide the literal generic
functor-action pattern.

`DefIso(C,x,y)` is the computational isomorphism package whose inverse cuts
cancel under the stable hom-action owner. `IsoEvidence` is its ordinary
propositional view.

### Sections 5–7: products, transfors, curry, and adjunctions

The product architecture includes:

- `Product_cat`, componentwise homs, projections, pairing, and symmetry;
- product-valued functor/transfor projection ladders;
- `Product_cat_func` for internalized product formation;
- `Product_map_func` for componentwise endpoint maps;
- `Eval_func`, fixed-object evaluation, semantic curry, and semantic uncurry;
- ordinary weakening, exchange, and contraction packages;
- a first-class `Adjunction(R,L)` with left/right functor, unit/counit, and
  both component-level triangle cut-elimination laws.

Cat-valued horizontal action is expressed through the generic
`comp_prod_fapp1_func` / `comp_prod_fapp1_fapp0` owner and its projection
ladder. Remaining `comp_cat_cov_*` / `comp_cat_con_*` names are transparent
readability or Cat-only projection surfaces where they expose transfor
structure; they do not own a duplicate functor law.

### Sections 8–10: directed Cat-valued families, Sigma/Pi, and mixed variance

Active family constructors include fibre notation, pullback/reindexing,
constant/terminal/opposite families, displayed composition, section
categories, and internalized Pi over varying bases.

```text
Pi_cat(E) = Functord_cat(Terminal_catd K,E)
Pi_cat(Const_catd K A) = Functor_cat K A.
```

Sigma total objects are dependent pairs. A total arrow consists of a base
arrow and a fibre arrow:

```text
(p,alpha) : (x,u) -> (y,v)
alpha : E[p](u) -> v.
```

`sigma_arrow` and `sigma_transport_arrow` are defined through this hom
characterization. `sigma_map_func` uses the displayed internal-hom projection
ladder for its fibre action; arbitrary displayed functors are lax rather than
silently strict/cartesian.

`Functor_catd`, `Hom_catd`, and `Transf_catd` are mixed-variance family
constructors. Pointwise formulas do not replace their required base-arrow
actions.

### Sections 11–17: representables, dependent hom, and displayed action

The dependent-hom architecture is shared by Sigma homs, fibre transport, and
section action. Important owners are:

```text
Rep_catd
Edge_catd_func / HomPresheaf_catd_func
homd_ / homd_int
homd_src_func / homd_src_sec / homd_tgt_func
fib_cov_int / fib_cov_transf
tdapp1_int_func_transfd / fdapp1_int_transfd
fdapp1_int_* / tdapp1_int_*
```

The Sigma-map fibre projection ladder ends at:

```text
fdapp1_int_hom_fapp0(FF,p,u,alpha)
```

with the transported-identity specialization:

```text
fdapp1_int_hom_fapp0(FF,p,u,id) -> fdapp1_int_cell(FF,p,u).
```

This is the component-level displayed laxity normal form. A whole-transfor
laxity interface remains deferred.

Section 17 contains generic Sigma/Pi introduction/evaluation, constant
sections, ordinary structural logic, generic functor hom-action, section
pullback, and internal Pi action.

### Section 18: Cat-valued profunctors and computational comparison

`Prof_cat(A,B)` is the primitive fixed-endpoint category of Cat-valued
profunctors on `A^op × B`; `Prof(A,B)` is its object classifier and `ProfMap`
is its fixed-endpoint vertical hom.

Active infrastructure includes:

- primitive `Unit_prof(A)` with direct rigid `Hom_*` base action;
- `Prof_reindex` through `Product_map_func(Op_func(F),G)`;
- readable representables `Hom_prof_along`, `Hom_prof`, `Companion_prof`, and
  `Conjoint_prof`;
- shaped cells/elements and internalized reindexing;
- primitive profunctor tensor and fixed-endpoint co-Yoneda maps;
- covariant and contravariant profunctor implication;
- fixed-endpoint eval/lambda inverse pairs;
- weighted cone/limit comparison and the dual weighted-colimit presentation;
- adjunction mate comparison and preservation of weighted limits/colimits;
- primitive directed join and its internally natural cross cell.

`ProfComparison(P,Q)` is a transparent compatibility name for
`DefIso(Prof_cat(A,B),P,Q)`. Its push/pull and evidence APIs route through the
generic `DefIso` and hom-action owners; it is not an independent eliminator
theory.

`Prof_tensor` and implication objects are symbolic primitives where the
current kernel lacks a general coend/coinserter quotient. Their checked beta,
reindexing, and closed-core interfaces state the active computational scope.

### Section 19: PathOut, path induction, and Eckmann–Hilton

For fixed `x : Z`:

```text
PathOut_Z(x) = Sigma (y : Z), Hom_Z(x,y).
```

The canonical arrow from `(x,id_x)` to `(y,p)` is the generic Sigma transport
arrow for the representable family. The primary path-induction package is the
telescope theorem `PathInd_transfd(Z)`; `PathInd_funcd(Z)` is derived by
`Sigma_transfd_funcd`.

The transitivity benchmark computes to ordinary composition. Nested telescope
terms stress the mixed-variance surface.

The first Eckmann–Hilton slice defines 2-endomorphisms of an identity 1-cell,
vertical and represented horizontal composition, the common-middle
equalities, and commutativity `EH_comm`.

## Core Ownership Invariants

### Runtime computation versus proof-time comparison

A rewrite rule selects a runtime normal form and participates in critical
pairs. A `unif_rule` helps elaboration/proof construction when neither side is
chosen as the runtime normal form.

Use:

```text
assert t ≡ u
```

for runtime conversion, and a typed reflexive equality:

```text
eq_refl(t) : τ(t = u)
```

to exercise a proof-time unification comparison. Do not infer runtime
joinability from a successful typed `eq_refl` probe.

### One generic owner for ordinary laws

The global `fapp*`/`tapp*` calculus is the sole owner of ordinary identity,
composition, functoriality, and naturality. A constructor-specific rule whose
only content is one of those laws indicates a missing internalized
functor/transfor owner or a detached projection.

A specialized projection-order bridge is exceptional but legitimate when:

1. a stable projection erases the literal generic-owner pattern;
2. an outer generic cut competes with that projection;
3. the two paths do not already join;
4. a focused owner-position probe establishes one canonical orientation.

Never install both orientations or generate such bridges mechanically.

### Hom variance and Došen cuts

When a term is already expressed through a stable hom-action owner, fold
consecutive actions to the one action indexed by the composite arrow:

```text
(F q)_*((F p)_*(g)) -> (F(q o p))_*(g)
(F p)^*((F q)^*(g)) -> (F(q o p))^*(g).
```

The second formula reflects contravariance: `q o p` first traverses `p`, then
`q`, while the induced precomposition actions are encountered in the reverse
endpoint order. These are the current runtime accumulation orientations.

Raw expanded compositions should normally remain `comp_fapp0` terms. Use the
existing proof-time bridges when a theorem compares them with stable hom-action
syntax. Add a raw runtime bridge only for a concrete consumer after testing
owner-first and projection-first reductions.

### Omega-friendly structure

Prefer functor-level folds over capped object rules when later hom action is
needed. A RHS that computes one selected cell can lose the functor object
required for the next dimension.

A formula `E[x] = ...` is only the object part of a directed family. A formula
`eta[x] = ...` is only a transfor component. Identify the base-arrow action and
off-diagonal/naturality action or explicitly record them as deferred.

## Before Editing The Kernel

1. Identify the semantic owner and whether the desired result is runtime or
   proof-time.
2. Search current declarations, rules, checks, examples, and the relevant plan
   with `rg`.
3. Decide whether a missing projection, transparent alias, or canonical
   endpoint fixes the problem before introducing a stable head.
4. Write the mathematical formula and the intended normal form.
5. Probe the candidate in a temporary full-file copy at its owning position.
6. Add a focused conversion assertion or typed `eq_refl` consumer.
7. Run a bounded quiet check; enable warnings when interactions are unclear.
8. Promote the smallest working change and add a durable diagnostic/example.
9. Update the task report when the architecture or a rejected orientation
   matters beyond the local rule.

## Rewrite And LHS Hygiene

### Minimal inferred slots

Keep reconstructible source/target/category/family arguments as `_` on rule
LHSs unless they are:

- the actual constructor discriminator;
- a composition-interface guard;
- required for subject reduction;
- a measured decision-tree/performance guard.

Compound reducible inferred terms such as `fapp0 F x`, `Functor_catd ...`,
`Op_cat(Hom_cat ...)`, or transparent readability aliases can cause brittle
matching and conversion explosions.

Audit candidates with:

```bash
python3 scripts/audit_rule_lhs.py --show-kept
make audit-rules
```

Do not apply the scanner mechanically. Probe each `_` replacement. Mark a
measured exception immediately above the rule:

```text
// lhs-audit: keep SLOT[,SLOT] -- reason
```

### Outer eliminators over active cuts

Treat an LHS such as:

```text
sigma_Fst(comp_fapp0(...))
sigma_Snd(fapp0(specialized_func,...))
```

as a high-risk commuting conversion. The outer projection and inner cut can
reduce in competing orders. Prefer:

1. an existing generic projection ladder;
2. a constructor beta rule;
3. a stable intermediate component;
4. an equation at the functor/transfor owner;
5. propositional evidence when judgmental computation is unnecessary.

A new commuting conversion requires a concrete consumer, focused checks for
both paths, an owner-position full-file probe, and warning classification.

### Canonical types and expected-type probes

Prefer reduced declared types and canonical endpoints:

```text
τ(Functord E D)
Hom_cat Z x y
Functord_cat E D
```

Use unreduced types only when the exact projection route is intentional and
document why.

A bare `assert t ≡ u` lets Lambdapi infer both sides independently. When a real
consumer supplies an expected type, test that typed shape explicitly before
concluding that conversion fails.

### Constants and unification limits

A `constant` cannot head a rewrite LHS. Changing it to `injective` is a global
normal-form migration requiring full downstream, subject-reduction, warning,
and decision-tree review.

Unification rules are experimental and not reliably transitive. Prefer two
rigid heads or a stable intermediary. Apply inferred-slot hygiene to both sides
of a `unif_rule`.

## Identity Normal Forms

Identity may appear as `@id`, `id_func`, `id_funcd`, or a specialized projected
identity. A rule for the generic surface does not automatically match every
already-normalized presentation.

Prefer narrow typed consumer rules or a coherent small specialization package
over broad global identity rewrites. The current middle-constrained generic
composition identity rules keep the shared middle object as the true cut
interface while inferring outer endpoints. Competing runtime identity
spellings are joined through the typed pre/post proof-time bridge; that
proof-time joinability is the selected criterion for this measured overlap.

## Comment And Layout SOP

Put a brief comment immediately above most semantic symbols and nontrivial
rule families:

- public constructor: mathematical name/formula and primitive/defined status;
- stable head: projection formula and generic owner;
- transparent alias: explicitly label it an alias/view;
- rewrite: label beta, projection, cut, accumulation, or confluence join;
- unification: state that it is proof-time only;
- evidence symbol: state the proposition witnessed.

One comment may cover a cohesive `rule ... with ...` command.

Use compact horizontal layout for simple stable-head rules. Keep vertical
layout for nested endpoint formulas, deliberate explicit guards, and
diagnostic assertions that expose canonical endpoints.

Do not duplicate a semantic body in a readability helper. Route aliases
through the named semantic constructor.

## Development And Validation Workflow

### Bounded checks

```bash
EMDASH_TYPECHECK_TIMEOUT=60s make check
timeout 20s lambdapi check emdash3_2.lp
make check-warnings
```

If a quiet check times out or hides the interaction, rerun the smallest target
with warnings enabled before changing the architecture.

### Focused probes

```bash
scripts/probe.sh tmp/probes/name.lp
scripts/explain_failure.py logs/probes/name.log
```

Ordinary experiments belong under ignored `tmp/probes/`. Move durable
reviewer-facing computations to `examples/`.

### Warning and decision-tree diagnosis

```bash
make warning-summary
scripts/explain_failure.py --warning logs/warnings/latest.log
scripts/decision_tree.sh SYMBOL
scripts/decision_tree.sh --png /tmp/tree.png SYMBOL
```

Use the smallest Lambdapi debug flag set: `u` unification, `c` conversion, `q`
rewriting, `w` weak-head normalization, `s` subject reduction, `k` local
confluence, `d` decision-tree compilation, and `i` typing. Never use
`--no-sr-check` for promoted code.

### Catalog, examples, CI, and health

```bash
make examples
make catalog
make ci
make health
```

`make catalog` can be non-strict during exploration; `make ci` requires a fresh
catalog and zero unclassified checks. Run `make health` after meaningful
architecture/check changes.

### Type-aware search

Use `rg` for ordinary discovery and:

```bash
scripts/lambdapi_search.sh 'name = hom_int'
scripts/lambdapi_search.sh 'type >= Prof_imply_cov'
```

for normalization/type-aware search.

## Current Deferred Boundaries

The following remain explicit future work rather than hidden assumptions:

- full general dependent adjunctions `Sigma_F ⊣ F^* ⊣ Pi_F`, including the
  planned `Pi_f`/comma-category infrastructure;
- displayed structural logic and remaining product/curry compatibility;
- semantic uncurry action on arbitrary transfors;
- whole-transfor displayed laxity beyond `fdapp1_int_cell`;
- the arrow action of `sigma_intro_tapp0_func`;
- a fully internalized general coend/coinserter semantics for profunctor tensor;
- general tensor associativity/coherence and complete co-Yoneda equivalences;
- dependent elimination and semantic collage construction for primitive join;
- specialized higher `fapp1*` projections of `Hom_tele_func` beyond current
  demand;
- complete computational univalence/coherence APIs beyond the active staging
  capabilities;
- general higher-inductive categories and pushouts;
- a finalized parser/surface language;
- module splitting of the single kernel file after comment/section boundaries
  stabilize.

Consult `INDEX.md` for the active plan owning a deferred item. Do not copy a
constructor-local law from an older plan without first rechecking the current
generic owner.

## Retirement And Recovery Policy

The v3.1 and v2 baselines are retired from normal checking and design work.
Their surviving lessons are represented in the active source, this SOP,
Foundations, canonical syntax, current plans, and the v2 retirement audit.

Infinity Codex response archives under `tmp/ai-responses/` are recovery
evidence only. Authority remains:

```text
active code/SOP -> active plan and side-task ledger
                -> explicitly linked decision responses -> raw archive.
```

After compaction/interruption, re-read the active authorities and task plan,
inspect staged/unstaged diffs, relocate symbols with `rg`, and run a bounded
baseline check before continuing.
