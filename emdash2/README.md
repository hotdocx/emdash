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
- decoded Empty/Unit/Bool/Nat and general binary-sum formers, plus a named
  finite dependent-record convention, with dependent elimination, constructor
  beta, and visible Unit/Boolean/Nat/general-sum constructor equality whose
  closed cases compute to Unit, Empty, predecessor equality, or component
  equality while generic `eq_refl` retains proof provenance; the generic J
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
  square, and a Pi-universe action consumer. The named
  `GrpdPathView(A,B) = TypeEquiv(A,B)` now provides a finite groupoid-universe
  identity view with decoder-owned encode/decode, propositional inverse laws,
  and transport agreement while public universe equality remains opaque; a
  direct equality rule was rejected because it recursively expands the
  unstratified self-universe normal form. The public fixed-arrow
  `OmegaEquivAlong(f)` evidence interface and Sigma-packaged `OmegaEquiv`, whose
  exact projections, recursive observations, reflexive/opposite/Product
  generators, and evidence-indexed decoder compute through one owner. At the
  categorical universe, public equality now reduces directly to
  `CatPathView(A,B) = OmegaEquiv(Cat_cat,A,B)`: named reflexivity, decoder-owned
  encode/decode and propositional round trips, reflexive Product action, and a
  D0b next-hom consumer reuse that package. Generic `eq_refl` remains a
  distinct proof form so literal J and path-action beta are preserved; the
  unstratified self-universe normal form terminates at opaque fixed-arrow
  evidence. A finite `OmegaEquivAlongPathView_D0(u,v)` now compares the nested
  Sigma/Product records of the two selected inverse arrows and recursive cell
  packages; genuine certificate paths act on that view, but there is no
  decoder or eta principle. The direct recursive certificate-equality rule is
  rejected because both owner-position checking and self-normalization exceed
  their bounds, so property-valuedness remains separate. The directed-
  dimension theorem is now executable conditionally: a named global
  `OmegaEquivAlongEvidenceProp_D0` capability is retained as an explicit input,
  while `ncat_obj_trunc_from_evidence_prop` computes from the discrete base and
  recursively closes each public omega-equivalence Sigma package before
  transporting through categorical univalence. No inhabitant of that
  capability is inferred from the finite view, so bare `IsNCat` evidence still
  does not prove object truncation. A separate dimension-indexed observation
  now makes the recursive certificate shape executable without changing that
  boundary: `OmegaEquivAlongDimObservation_D0(n,h,f)` is Unit at dimension zero
  and at a successor retains both inverse arrows plus recursively observed
  inverse cells in the smaller-dimensional hom-categories. Its observation
  map reuses the four D0 owners, and its path view has reflexivity and one-way
  path action. `ZeroCat` and `OneCat` controls normalize, but there is still no
  reverse decoder, eta, evidence-property inhabitant, or public certificate-
  equality rule.
  Product
  isomorphism and omega-equivalence evidence retain their componentwise
  constructor provenance even when both components are reflexive; projections
  and decoders compute componentwise without collapsing to the distinct
  generic reflexive evidence heads. The
  categorical decoder supplies a named equivalence, both propositional round
  trips, and a propositional `path_to_hom` square. Its variable-evidence Cat
  hom-action repairs raw inverse-action endpoints by recursive-cell components
  and yields the first iterable next-hom univalence/action witness;
- covariant/contravariant hom actions and the rigid simultaneous `Hom_*`
  action used by the unit hom profunctor;
- the exact two-field `IsDiscreteCat(C)` contract, with set-truncated objects,
  fixed core-inclusion evidence, D0b-derived homwise omega-equivalence,
  selected `hom_to_path`, both coherent round trips, and an iterable recursive
  cell without broad runtime cancellation;
- independent `IsObjTruncCat`, native `CatDim`, its recursive
  `cat_dim_trunc_level` object-level index, recursive `IsNCat`, and
  evidence-retaining `NCat(n)` packages with `ZeroCat`/`OneCat`; a packaged
  one-category exposes discrete hom-categories and iterates core-inclusion
  adequacy between parallel arrows. Fixed-map `OmegaEquivAlong(F)` now induces
  an ordinary equivalence of object classifiers and transports
  `IsObjTruncCat`; the index still does not itself prove the recursive
  `IsNCat` object-truncation theorem. Ordinary strict isomorphism evidence now
  has a backed lift to recursive `OmegaEquiv`: both inverse arrows reuse the
  ordinary inverse and the two inverse equations encode as next-hom cells. A
  packaged one-category consequently has a derived `one_cat_iso_path` decoder
  and the decoder-after-`idtoiso_cat` round trip. Recursive inverse cells now
  also construct `omega_equiv_along_left_to_right_D0`, and OneCat hom
  discreteness decodes it through `one_cat_omega_inverse_path` without
  identifying the two inverse observations by rewrite or proof-time fiat.
  The decoded right law transports along that path, reconstructing ordinary
  `IsoEvidence` from arbitrary OneCat omega evidence. Hom discreteness makes
  its two inverse-law proof fields proposition-valued, so the existing nested-
  Sigma path view proves reconstruction and the second round trip. The derived
  `one_cat_iso_univalence` and `one_cat_iso_type_equiv` are therefore fully
  OneCat-scoped. The unused arbitrary-category capability inhabitants and
  hardcoded classifier are retired; the distinct legacy decoder remains only
  for its reflexive/Product compatibility computation;
- registered `ObsAction`/`ObsDAction` packages whose selected open-map or
  dependent-section action carries next-dimensional agreement with semantic
  `eq_ap`/`eq_apd`; identity action and registered composition compute,
  PathRecord maps act on shaped paths, and the dependent witness field acts
  through `PathOver`. The canonical binary-sum map now lifts registrations on
  both summands to a componentwise action: equal tags delegate to their
  supplied action, mixed tags use Empty, and agreement with generic `eq_ap`
  remains propositional and runtime-distinct. Recursive Nat equality now also
  has a registered successor action: the selected map retains the exposed
  predecessor path `p`, while a stable proof-time basis and generic J prove
  agreement with `eq_ap(succ)`. The former-specific `nat_succ_ind_eqr` facade
  then accepts arbitrary proof-dependent successor-path motives and computes
  only when the exposed predecessor proof is component reflexivity, by routing
  through the existing generic J owner. Outer reflexivity and the action basis
  remain noncomputational; this is not a global fibrancy package. Neither
  action erases proof provenance;
- Cat-valued profunctors, reindexing, tensor, implication, computational
  comparison, weighted-limit/colimit staging, and adjunction mates;
- a primitive directed join slice, synthetic PathOut/path induction, and a
  reviewer-facing Eckmann–Hilton computation.

These are kernel and architecture milestones, not a finalized surface parser
or a completed foundational theory.

## Authorities And Layout

- `emdash3_2.lp`: active v3.2 kernel implementation.
- `emdash3_2_checks.lp`: executable diagnostic/regression suite.
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
