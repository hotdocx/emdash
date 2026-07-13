# EMDASH v3.2 Primitive Pi Eliminator Audit And Redesign Plan

Date: 2026-07-13
Last reviewed: 2026-07-13
Plan-ID: EMDASH-V3-2-PRIMITIVE-PI-ELIMINATOR-AUDIT-REDESIGN-2026-07-13
Depends-On: EMDASH-V3-2-PRIMITIVE-PI-FACADE-REARCHITECTURE-2026-07-12; EMDASH-V3-2-DISPLAYED-FACADE-TOWER-REARCHITECTURE-2026-07-11; REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26
Supersedes: no whole report; reopens only the eliminator-ownership question whose earlier answer assumed transparent Pi_cat
Side-Task-Ledger: #side-task-ledger
Infinity-Codex-Origin: current-session-analysis-2026-07-13
Infinity-Codex-Decision-Responses: infinity-codex:019f526a-dafb-77d0-9dea-2778a57275b7:019f5a1c-abb8-7152-b1ce-8a3076fc288f
Status: promoted 2026-07-13; semantic eliminators retained, generic full/capped component-hom projection promoted, diagnostics/catalog/health/warnings/reviewer examples/full local CI pass

## Goal

Determine whether the existing transparent `piapp0*` and `piapp1*` semantic
definitions remain the correct eliminator/action architecture now that
`Pi_cat` is a primitive stable section-category facade.

The preferred outcome is the smallest coherent calculus that satisfies:

1. public eliminators accept only genuine section objects
   `s : Obj(Pi_cat E)`;
2. object, hom, and next-hom action compute through documented owners;
3. the construction remains iterable at higher cells;
4. generic displayed action remains the sole owner of ordinary
   functoriality/naturality;
5. no retired terminal-specialized `piapp1_int_*` pipeline or broad raw
   `fapp0` bridge is resurrected without a new measured consumer.

## Current Status Relative To The Primitive Pi Facade

The category-facade migration is complete and healthy. `Pi_cat` is an
injective category head, proof-time-comparable with terminal-source
`Functord_cat` and ordinary Cat-valued `Transf_cat`, with runtime `Obj` and
`Hom_cat` projections.

The eliminator surfaces were not migrated to stable runtime heads:

| Surface | Current form | Semantic owner after unfolding |
| --- | --- | --- |
| `piapp0_func(E,k)` | transparent functor definition | terminal-source `tapp0_func` plus terminal evaluation |
| `piapp0(s,k)` | transparent application definition | generic `fapp0` |
| `pi_hom_fapp0(eta,k)` | transparent hom-component definition | `tdapp0_fapp0` / `tapp0_fapp0` |
| `piapp1_src_obj(s,f)` | transparent endpoint definition | `fib_cov_tapp0_func` |
| `piapp1_func(s,x,y)` | transparent section definition | `fdapp1_int_presheaf_arrow` |
| `piapp1_fapp0(s,f)` | transparent capped definition | `piapp0(piapp1_func(...),f)` |

These heads have no rewrite decision trees of their own. This is not presently
an end-user type-safety defect: every public section argument has type
`Obj(Pi_cat E)`, whose runtime representation is specifically a displayed
functor from `Const_catd K Terminal_cat` to `E`. A displayed functor from an
arbitrary source family cannot be passed unless that source unifies with the
terminal family.

The open question is ownership and higher iterability: computation currently
requires unfolding the Pi-facing surface into generic displayed machinery.

## Historical Boundary

The 2026-05-25/31 Pi-alias work made `Pi_cat` transparent and concluded:

- `piapp0_func` and `piapp0` were conceptually correct defined surfaces;
- `piapp1_src_obj`, `piapp1_func`, and `piapp1_fapp0` could remain surface
  definitions over generic displayed action;
- the separate `piapp1_int`, `piapp1_int_src_transf`,
  `piapp1_int_src_app`, and `piapp1_int_tgt_transf` pipeline should be
  retired;
- a raw constant-family rule
  `fapp0(piapp1_func(...),f) -> fapp1_fapp0(...)` should be removed because it
  created a competing representation path; the capped `piapp1_fapp0` API was
  sufficient.

That outcome is reflected in commits `9ac7e3f` and `1c2fb1b`. Its premise was
that terminal-source `Functord_cat` was the only category head for sections.
Primitive `Pi_cat` is the concrete new circumstance that justifies this
focused re-audit, but not automatic restoration of the retired machinery.

## Audit Questions

### Pi object evaluation

Check that the declared functor and capped application remain coherent:

```text
piapp0_func(E,k) : Pi_cat(E) -> E[k]
piapp0(s,k) = piapp0_func(E,k)[s].
```

Exercise both the Pi-facing term and its unfolded terminal-source component
route.

### Pi hom evaluation

The crucial missing executable comparison is:

```text
piapp0_func(E,k)[eta]
  = pi_hom_fapp0(eta,k)
```

for `eta : Hom_(Pi_cat E)(s,t)`. This tests whether the generic hom action of
the evaluation functor joins the explicitly named section-hom component.

### Section action

Retain the existing object endpoint and capped action checks:

```text
piapp1_src_obj(s,f) = E[f](s[x])
piapp1_fapp0(s,f) = piapp0(piapp1_func(s,x,y),f).
```

Add a higher-action probe for an arrow `alpha : f -> g` in the relevant
opposite hom category. The goal is to show that the section
`piapp1_func(s,x,y)` remains iterable and that its next action is owned by the
same dependent-hom/displayed-laxity stack.

### Constant-family comparison

Preserve the capped public computation:

```text
piapp1_fapp0(Const_catd K A,s,f) = fapp1_fapp0(s,f).
```

Do not restore the rejected raw projection rule merely to make an assertion
about `fapp0(piapp1_func(...),f)` pass through a second representation path.

## Candidate Architectures

### Candidate A: semantic eliminators, strengthened diagnostics

Keep the current transparent definitions. Add direct object/hom/next-hom
checks and document the generic projection ladder as their computational
owner.

This candidate is preferred if the focused probes compute without local
commuting bridges. It follows the SOP rule to prefer semantic definitions
before primitive stable heads.

### Candidate B: minimal stable eliminator packages

If a concrete higher consumer cannot retain the Pi-facing owner, introduce
only the smallest required stable package, likely `piapp0_func` and/or
`piapp1_func`, with explicit object and hom projections to the existing
generic displayed machinery.

Do not make only an object-level projection stable: that would cap the result
and erase the functor/section needed for the next hom action.

### Candidate C: restored Pi-specific internal pipeline

Rejected by default. Restoring `piapp1_int_*` duplicates the generic
displayed-action owner and previously required fragile terminal-source
bridges. Reconsider only if candidates A and B fail under a concrete required
consumer.

## Documentation Corrections

The audit must correct two known stale statements:

1. the living SOP still prints `Pi_cat(E) = Functord_cat(...)` without marking
   the comparison as proof-time;
2. `reports/INDEX.md` still describes the path-induction section owner as
   deferred in the displayed-facade record, although the primitive-Pi facade
   resolved it.

The primitive-Pi plan should also distinguish a named semantic interface from
a stable rewrite owner: `piapp0_func` is presently the former, not the latter.

## Implementation Phases

### Phase 0: plan and baseline

1. Create and index this plan.
2. Reconfirm clean staged/unstaged state and bounded `make check` baseline.
3. Preserve positive/negative probes under ignored `tmp/probes/`.

### Phase 1: `piapp0` object and hom action

1. Add a full-file focused probe for object evaluation through both paths.
2. Probe `fapp1_func` and capped `fapp1_fapp0` of `piapp0_func`.
3. Compare the capped result with `pi_hom_fapp0`.
4. Classify any missing join before adding a rule.

### Phase 2: `piapp1` object and higher action

1. Recheck the general and constant-family capped computations.
2. Probe the next action of `piapp1_func` on arrows between base arrows.
3. Verify the result remains at an iterable dependent-hom owner.
4. Do not add a raw constant-family `fapp0(piapp1_func(...),f)` bridge.

### Phase 3: architecture decision and promotion

1. Select candidate A if all required generic paths join.
2. Otherwise probe candidate B at its owning positions with object and hom
   projections together.
3. Record rejected alternatives and warning effects.
4. Promote only the smallest complete owner set.

### Phase 4: diagnostics and active documentation

1. Add one focused diagnostic for every accepted object/hom/next-hom law.
2. Correct the SOP, Foundations, canonical syntax, primitive-Pi report, and
   report index where required.
3. Regenerate catalog and health reports.

### Phase 5: handoff gate

Run:

```text
make check
make examples
make warning-summary
make audit-rules
make catalog
make toc
make health
make ci
git diff --check
```

## Promotion Criteria

The audit is complete when:

1. section inputs are demonstrably confined to `Obj(Pi_cat E)` and its exact
   terminal-source representation;
2. `piapp0_func` object and hom actions have executable checks;
3. `pi_hom_fapp0` is exercised by the diagnostic suite;
4. `piapp1_func` has a measured higher-action/iterability result or an
   explicitly documented prerequisite;
5. the constant-family capped API computes without the rejected raw bridge;
6. stable heads are introduced only for a concrete generic-path failure;
7. active documentation no longer conflates proof-time comparison with
   runtime reduction or a semantic name with a rewrite owner;
8. the complete validation gate passes.

## Implementation Results

### Public boundary and object evaluation

The public boundary is already strict enough. Every section argument has type
`Obj(Pi_cat E)`, whose runtime classifier is exactly
`Obj(Functord_cat(Const_catd K Terminal_cat,E))`. A displayed functor from an
arbitrary nonterminal source family therefore cannot be supplied to `piapp0*`
or `piapp1*` without first solving the terminal-source type constraint.

Both object probes pass with the existing definitions:

```text
piapp0_func(E,k)[s] = piapp0(s,k)
terminal component evaluation at k and Terminal_obj = piapp0(s,k).
```

Thus making `Pi_cat` primitive did not require a new primitive object
eliminator.

### Missing generic hom projection

The initial hom probe did fail:

```text
piapp0_func(E,k)[eta] = pi_hom_fapp0(eta,k).
```

Unfolding `piapp0_func` showed a genuine generic projection gap. Its inner
functor is Cat-valued component evaluation
`tapp0_func(K,Cat,E,D,k)`. The full hom action of that functor should be the
existing displayed-component functor `tdapp0_func(k)`, and its capped action
should be `tdapp0_fapp0(k,eta)`. Only the object projection had previously
been installed.

The promoted generic package is therefore:

```text
fapp1_func(tapp0_func(K,Cat,E,D,k),FF,GG)
  -> tdapp0_func(K,E,D,FF,GG,k)

fapp1_fapp0(tapp0_func(K,Cat,E,D,k),FF,GG,eta)
  -> tdapp0_fapp0(K,E,D,FF,GG,k,eta).
```

The first rule preserves the functor needed for iteration; the second is the
direct capped join required by the generic `fapp1_fapp0` route. They belong to
Cat-valued component evaluation, not to Pi. With them, the `piapp0_func` hom
probe and the named `pi_hom_fapp0` comparison pass.

### `piapp1*` next action

The first higher-action probe passes without any new rule. For
`alpha : f -> g` in `Op_cat(Hom_cat K x y)`, the action of the section
`piapp1_func(s,x,y)` reduces to the terminal-source specialization of:

```text
fdapp1_int_hom_fapp0
  (piapp1_func(s,x,y), f, g, alpha,
   Terminal_obj, Terminal_obj, Terminal_obj).
```

This establishes the required first iterability step: `piapp1_func` does not
cap the tower at `s[f]`; its next action stays in the generic displayed
internal-hom calculus. The existing constant-family capped comparison with
ordinary `fapp1_fapp0` also continues to pass.

### Architecture selection

Candidate A is selected with one correction to the previously documented
generic projection ladder:

- keep `piapp0_func`, `piapp0`, `pi_hom_fapp0`, `piapp1_src_obj`,
  `piapp1_func`, and `piapp1_fapp0` as semantic definitions;
- promote the missing full and capped generic `tapp0_func` hom projections;
- do not introduce primitive Pi-eliminator heads;
- do not restore the retired `piapp1_int_*` pipeline or its raw constant-family
  `fapp0` bridge.

The fact that the declarations of `piapp0*` / `piapp1*` remain definitions is
therefore a positive result, not an omitted migration. The stable category
head is needed at the category boundary; the eliminators already factor
through stable generic functor-level owners.

### Warning and ablation evidence

The baseline warning inventory was 1,253 warnings: 1,090 unjoinable critical
pairs and 163 replaceable pattern variables. The generic full/capped package
produces 1,257 warnings: 1,094 critical pairs and the same 163 pattern
warnings. The four additions are two identity-overlap reports (one repeated
through the displayed-category presentation) and two generic
naturality/composition overlaps involving the newly visible capped component.
They expose already-deferred higher naturality joins; they do not affect the
focused object, hom, or next-hom computations.

A terminal-source-only alternative was also measured. It produced 1,100
critical-pair warnings, ten above the baseline, because its nested
`Const_catd` discriminator overlaps more broadly under conversion. It is
rejected as both less general and diagnostically worse. Adding the full
`fapp1_func -> tdapp0_func` projection does not increase the warning inventory
beyond the four warnings already introduced by the required capped rule.

Positive and negative evidence is retained under ignored `tmp/probes/`, with
raw logs under `logs/probes/`.

### Validation record

The promoted source and documentation pass:

```text
make check             pass
make examples          pass
make warning-summary   pass (1,257 classified warnings)
make audit-rules       pass (0 unreviewed candidates)
make catalog           pass (780 classified diagnostics)
make toc               pass (86 headings, sections 0-19)
make health            pass (8 checked files/examples)
make ci                pass
git diff --check       pass
```

## Side-Task Ledger

- `PIELIM-01`: Create/index the plan and recover the relevant historical
  boundary. Status: complete.
- `PIELIM-02`: Probe `piapp0_func` object and hom action, including
  `pi_hom_fapp0`. Status: complete; object evaluation passed, the generic hom
  projection gap was isolated and repaired.
- `PIELIM-03`: Probe `piapp1_func` object and higher action. Status: complete;
  the first next action reaches `fdapp1_int_hom_fapp0` without a new rule.
- `PIELIM-04`: Select/promote the minimal architecture. Status: complete;
  semantic eliminators plus the generic full/capped component projection were
  selected.
- `PIELIM-05`: Correct active documentation and add diagnostics. Status:
  complete.
- `PIELIM-06`: Complete warning comparison and full CI. Status: complete.

## Deferred Boundaries

This plan does not implement:

- general `Pi_along_func` or comma/right-Kan infrastructure;
- a new surface parser;
- a restored `piapp1_int_*` chain without new evidence;
- arbitrary commuting conversions over raw `fapp0`/`tapp0_fapp0` terms;
- general higher coherence beyond the first concrete next-action probe.
