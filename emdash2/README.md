# m— / emdash

`emdash` is a Lambdapi specification for functorial programming and a future
programming language/proof assistant for strict and lax omega-categories,
omega-functors, omega-transformations (“transfors”), directed families, and
dependent categorical constructions.

The computational style is inspired by Kosta Došen’s cut elimination in
categories: rewrite rules select useful runtime normal forms, while narrowly
typed unification rules relate alternative proof-time presentations when no
runtime orientation is intended.

The active development is v3.2 and remains experimental.

## Current Scope

The checked kernel currently includes:

- iterated hom-categories, ordinary functors, transfors, products, evaluation,
  curry/uncurry infrastructure, and the indexed `Adjunction(F,G)` relation
  with transparent functor views, stable unit/counit observations, both
  triangles, opposite adjunctions, and computational mate consumers;
- directed Cat-valued families, natural/displayed functors and transfors,
  Sigma total categories, section/Pi categories, dependent homs, and fibre
  transport;
- decoded Empty/Unit/Bool/Nat formers plus a named finite dependent-record
  convention, with dependent elimination, constructor beta, and visible
  Unit/Boolean/Nat constructor equality whose closed cases compute to Unit,
  Empty, or predecessor equality while generic `eq_refl` retains proof
  provenance; the generic J
  beta guards both its category and repeated endpoint so a foreign or
  predecessor reflexivity proof cannot fire merely through a shared reduced
  classifier; plus a nested-Sigma
  observational path view, stable shaped reflexivity, projection betas, and
  reflexive J, propositional arbitrary Sigma path round trips, transparent
  named PathRecord path round trips that preserve shaped reflexivity, recursive
  homotopy-truncation properties from contractible
  through proposition/set/groupoid levels, a level-recursive one-step
  monotonicity theorem, arbitrary-level dependent-Pi and same-level
  dependent-Sigma truncation closure, proposition-valued truncation evidence
  at every native level, canonical invariance under ordinary `TypeEquiv`, and
  packaged proposition/set/ordinary-groupoid universes whose carrier and
  retained truncation evidence project computationally. Package equality is
  equivalent to equality of the retained carriers: proposition-valued
  evidence reconstructs the dependent field path, and both inverse laws are
  propositional. Composing that path equivalence with the canonical ambient
  decoder now gives restricted univalence between package equality and
  ordinary `TypeEquiv` data for the carriers, again without runtime package
  eta or inverse cancellation. An explicit-inverse contractible base together
  with successor Pi/Sigma/property closure proves `TypeEquiv(A,B)` is
  `n`-truncated for `n`-truncated endpoints; transporting this through the
  restricted package equivalence gives the expected
  `IsTruncGrpd(trunc_succ n, TruncGrpdU n)` theorem without a same-level
  universe claim or proof erasure.
  The ordinary dependent-Pi happly/funext layer has
  related-input action, pointwise runtime beta, generic-J propositional eta,
  and a contractible-fibre `TypeEquiv` package, ordinary identity, symmetry,
  and categorical-order composition of type equivalences with executable map
  projections, plus equality/path categories
  whose composition retains the shared categorical owner with propositional
  J-derived transitivity agreement, a genuine opposite presentation, and
  functor-owned path symmetry with propositional J-derived agreement and
  involution, type equivalence, ordinary and omega-categorical equivalence
  staging, and groupoid decoder univalence with both propositional round trips,
  a derived canonical contractible-fibre capability, a propositional transport
  square, and a Pi-universe action consumer. The equality-valued overlay adds
  a decoded native `OmegaEquivAlong_EQ1(f)` record with separate inverse arrows
  and ordinary equality-valued cancellation laws, plus a stable first-class
  `OmegaEquiv_EQ1` facade with construction, projections, dependent
  elimination, propositional eta, and a transparent Sigma comparison. Generic
  object equality compares with that facade at proof time; rigid Cat and Grpd
  universe equality reduce to it at runtime, while explicit path packages own
  observer computation. The D0-free library view
  `GrpdPathView = TypeEquiv` and its explicit adapters remain in the kernel and
  use a transparent quasi-inverse-to-contractible-fibre theorem. The older
  recursive D0/D0b/D1 certificates, unsuffixed omega-equivalence facade, Cat
  decoder, and their round trips have been mechanically extracted into the
  frozen opt-in `emdash3_2_legacy_compat.lp` module. They are absent from the
  active kernel/native/check dependency closure and are not a second
  equivalence foundation. The self-only one-layer and dimension-indexed D0
  observation trees were deleted rather than extracted.

  The downstream transparent evidence module proves fixed-arrow native-EQ1
  evidence proposition-valued for every category by contracting two
  composition-map homotopy fibres. It also proves truncation closure under
  explicit retractions and the unconditional finite-dimensional theorem
  `IsNCat(n,C) -> IsObjTruncCat(cat_dim_trunc_level(n),C)`, with computing base
  and successor equations. The obsolete uninhabited D0 global evidence-
  property capability and its conditional theorem are retired; the generic
  `prop_is_trunc_cat_dim` lemma remains because the native theorem uses it.
  Ordinary Product isomorphism evidence retains its componentwise constructor
  provenance even when both components are reflexive. The extracted legacy
  module separately preserves its historical Product omega-equivalence and
  decoder computation only for seven explicitly legacy reviewer examples;
- covariant/contravariant hom actions and the rigid simultaneous `Hom_*`
  action used by the unit hom profunctor;
- the exact two-field `IsDiscreteCat(C)` contract, with set-truncated objects
  and native `IsGroupoidalCat_EQ1(C)` evidence. The one-way native hom-action
  extension derives the iterable core-inclusion hom equivalence, selected
  `hom_to_path`, equality-valued re-inclusion, and the retained directed-cell
  round-trip surface without broad runtime cancellation;
- independent `IsObjTruncCat`, native `CatDim`, its recursive
  `cat_dim_trunc_level` object-level index, recursive `IsNCat`, and
  evidence-retaining `NCat(n)` packages with `ZeroCat`/`OneCat`; a packaged
  one-category exposes discrete hom-categories and iterates native
  core-inclusion adequacy between parallel arrows. Native fixed-map
  `OmegaEquivAlong_EQ1(F)` induces an ordinary equivalence of object
  classifiers and transports `IsObjTruncCat`; native EQ1 evidence proves the
  recursive `IsNCat` object-truncation theorem unconditionally. Ordinary
  strict isomorphism evidence has a direct one-way native lift through
  `iso_evidence_omega_along_EQ1`/`iso_evidence_omega_equiv_EQ1`: both native
  inverse slots reuse the ordinary inverse and both equations already have the
  required equality-valued types. The complete two-sided OneCat
  `one_cat_iso_type_equiv` contract remains in the frozen compatibility module:
  a focused native replacement stops at the intentional stable-cast/facade-
  package-to-raw-path reification boundary even at reflexivity. The theorem is
  retained intact rather than weakened or supported by a new proof-time
  identification, and no new compatibility consumer is permitted;
- canonical iterable `Path_cat_func`/`path_map_func` action for every raw
  groupoid function. Its capped `fapp1_fapp0` action computes directly to
  `eq_ap`, its full next-hom action remains iterable through `fapp1_func`, and
  identity/composition are inherited from the generic functor calculus. No
  parallel selected-action registry or second runtime owner remains. The
  unused dependent registry is retired, so the PathRecord witness field acts
  through direct `eq_apd` and `PathOver`; any stronger dependent analogue
  would be displayed functor/section structure. Recursive Nat equality keeps
  the former-specific `nat_succ_ind_eqr` facade, which
  then accepts arbitrary proof-dependent successor-path motives and computes
  only when the exposed predecessor proof is component reflexivity, by routing
  through the existing generic J owner. Outer reflexivity remains
  noncomputational; this is not a global fibrancy package. The isolated Sum
  experiment was retired on 2026-07-20 for later consumer-led redesign;
- Cat-valued profunctors, reindexing, tensor, implication, computational
  comparison, weighted-limit/colimit staging, and adjunction mates;
- a primitive directed join slice, synthetic PathOut/path induction, and a
  reviewer-facing Eckmann–Hilton computation.

These are kernel and architecture milestones, not a finalized surface parser
or a completed foundational theory.

## Authorities And Layout

- `emdash3_2.lp`: active v3.2 kernel implementation.
- `emdash3_2_eq1_hom_action.lp`: one-way transparent derived native-EQ1
  hom-action, groupoidality, and structured-transport extension.
- `emdash3_2_eq1_evidence_property.lp`: downstream transparent native-EQ1
  evidence-property, retract-truncation, and finite-`NCat` object-truncation
  extension.
- `emdash3_2_nat_arithmetic.lp`: reusable Nat arithmetic, canonical
  `NatSucc_func`, proposition witnesses, and Nat sethood.
- `emdash3_2_walking_end_hit.lp`: selected walking-endomorphism directed-HIT,
  eliminator/comparison, and separate `BNat` consistency model.
- `emdash3_2_checks.lp`: executable diagnostic/regression suite.
- `emdash3_2_legacy_compat.lp`: frozen opt-in D0/D1 and decoder compatibility
  module. It imports the kernel one-way, is non-authoritative, and may be used
  only by the seven explicitly legacy examples; no new consumer or feature is
  accepted.
- `reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`:
  current architecture and development SOP.
- `reports/EMDASH_FOUNDATIONS.md`: mathematical reading guide.
- `reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`:
  notation authority for comments, examples, and future parser work.
- `reports/INDEX.md`: report lifecycle and task-specific plan map.
- `reports/REPORT_EMDASH_CHECK_CATALOG.md`: generated reviewer map of checks.
- `reports/REPORT_EMDASH_HEALTH.md`: generated validation/source metrics.
- `examples/`: small reviewer-facing milestones.
- `docs/`: local Lambdapi syntax, command, query, pattern, and tactic notes.
- `lambdapi-examples/`: upstream-style syntax and proof examples.
- `scripts/`: checking, probing, warning, decision-tree, catalog, search, and
  maintenance utilities.
- `print/`: paper/Markdown renderer and Arrowgram validation support.

Obsolete v2/v3.1 material is retired under ignored `.scratchpad/` directories
and is not part of normal development. Use the active reports rather than
historical files unless explicitly doing archaeology.

## Quick Start

Prerequisite: `lambdapi` on `PATH`. The current environment is tested with
development build `3.0.0-90-gdb4f780`; this is an environment record, not a
hard CI version gate.

```bash
make check                 # active kernel and diagnostics
make examples              # reviewer milestones
make ci                    # local handoff gate
make check-warnings        # warning-enabled kernel check
make warning-summary       # compact warning inventory + raw log
make audit-rules           # strict inferred-LHS-slot audit
make catalog               # regenerate the check catalog
make toc                   # verify header/source heading equality
make health                # refresh generated health metrics
```

During rewrite/unification development, keep checks bounded:

```bash
EMDASH_TYPECHECK_TIMEOUT=60s make check
timeout 20s lambdapi check emdash3_2.lp
```

If a quiet run does not localize an interaction:

```bash
EMDASH_LAMBDAPI_WARNINGS=1 EMDASH_TYPECHECK_TIMEOUT=20s make check
EMDASH_LAMBDAPI_FLAGS='--debug=u' scripts/probe.sh tmp/probes/name.lp
```

## Development Loop

For a nontrivial rule or unification change:

1. locate the semantic owner and nearby projection ladder with `rg`;
2. place the candidate in a temporary full-file copy at its intended owning
   position;
3. add a focused assertion exercising the intended runtime conversion or typed
   proof-time comparison;
4. run `scripts/probe.sh tmp/probes/name.lp` with a short timeout;
5. compare warning-enabled behavior when the change can affect overlaps;
6. promote the smallest semantically correct rule/projection and run
   `make check`;
7. update diagnostics/catalog and run `make ci` before handoff.

The detailed policies for inferred LHS slots, outer-eliminator/inner-cut
patterns, runtime versus proof-time ownership, generic `fapp*`/`tapp*`
ownership, stable projection heads, and identity normal forms live in the
current SOP report. `AGENTS.md` contains the mandatory condensed workflow.

## Useful MathOps Commands

```bash
scripts/probe.sh tmp/probes/name.lp
scripts/explain_failure.py logs/typecheck.log
scripts/decision_tree.sh fapp1_func
scripts/decision_tree.sh --png /tmp/fapp1.png fapp1_func
scripts/lambdapi_search.sh 'type >= Prof_imply_cov'
python3 scripts/audit_rule_lhs.py --show-kept
python3 scripts/arxiv_search.py --query 'cat:math.CT AND abs:"omega category"'
```

Watch mode:

```bash
make watch
tail -f logs/typecheck.log
```

Logs are retained for diagnosis and are pruned only on explicit request:

```bash
make prune-logs
EMDASH_LOG_KEEP_DAYS=7 make prune-logs
```

## Check And Documentation Maintenance

- Executable assertions belong in `emdash3_2_checks.lp`; keep the generated
  catalog fresh with `make catalog`.
- Add mathematical formulas and ownership notes adjacent to semantic symbols
  and nontrivial rule families in `emdash3_2.lp`.
- Use the canonical syntax report for comment/example notation.
- Add new reports to `reports/INDEX.md` and include the required plan metadata.
- Refresh `make health` after meaningful architecture or check changes.
- Do not treat warning counts as an automatic veto; use warning locations and
  term heads to classify concrete overlap families.

## Infinity Codex Recovery

Trusted project hooks archive completed main-agent final responses under
ignored `tmp/ai-responses/`. The archive contains recovery evidence, not
current instructions. Current code/SOP and the active task plan always take
precedence.

```bash
python3 scripts/infinity_codex.py list --limit 5
python3 scripts/infinity_codex.py latest-path
python3 scripts/infinity_codex.py show LOGICAL_ID
python3 scripts/infinity_codex.py verify
```

The hook does not archive user prompts, commentary, tool calls, or subagent
output. See the indexed Infinity Codex implementation report for the complete
recovery and retention policy.

## Print Pipeline

Run from this directory:

```bash
npm run install:print
npm run dev
npm run validate:paper
npm run check:render
```
