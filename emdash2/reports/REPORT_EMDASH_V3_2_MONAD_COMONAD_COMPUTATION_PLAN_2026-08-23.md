# Emdash v3.2 Monad And Comonad Computation Plan

Date: 2026-08-23 (America/Toronto)

Plan-ID: `MONAD-COMONAD-COMPUTATION-V3.2`

Status: **completed post-`e90ce3c` direct Monad-usability correction as of
2026-08-26**. Commit `e90ce3c` preserves the validated transparent-whole
correction as a historical checkpoint. Final review then identified that the
adjunction-derived unit was prematurely installed as a runtime projection,
whereas whole multiplication is properly a semantic projection.
`MCD-MONAD-USABILITY-19` moves only the unit comparison to proof time, retains
transparent `G epsilon F` multiplication, and supplies a derived propositional
join for its two component reductions. `MCD-RECLOSE-20` records the scoped
green closure.
TypeScript automation, free syntax/decidability, and an explicit Kleisli
category remain deliberately outside this correction.

Depends-On: active v3.2 `Adjunction`, `Op_cat`, `Op_func`, `Op_transf`,
`tapp1_func`/`tapp1_fapp0`, stable represented precomposition and
postcomposition owners, current rewrite/unification SOP, Foundations, and
canonical syntax

Supersedes: the completed-state conclusion recorded at historical checkpoint
`c1f4419`. The first review correctly fixed the accumulation orientation but
incorrectly replaced ambient composition by a primitive stable-cut owner and
treated a warning delta as a veto.

Infinity-Codex-Origin: session `01a02f68-6142-7e53-993a-4505aa8e2cbe`,
response `0001`

Infinity-Codex-Decision-Responses: responses `0001`, `0003`, `0005`, `0007`,
and `0014`; the 2026-08-24 through 2026-08-26 user clarifications supersede
the first checkpoint's raw-rule rejection, the `ac1671c`
propositional-duality facade, and the premature runtime adjunction-operation
projections. This plan is authoritative.

Side-Task-Ledger: `MCD-00`, `MCD-OWNER-1`, `MCD-MONAD-2`, `MCD-KLEISLI-3`,
`MCD-OP-4`, `MCD-ADJ-5`, `MCD-CLOSE-6`, `MCD-FREE-7`, `MCD-TS-8`,
`MCD-AMBIENT-9`, `MCD-DUAL-10`, `MCD-KLCAT-11`, `MCD-RECLOSE-12`,
`MCD-MONAD-SOP-13`, `MCD-OP-DEF-14`, `MCD-CODUAL-15`,
`MCD-RECLOSE-16`, `MCD-CODUAL-WHOLE-17`, `MCD-RECLOSE-18`,
`MCD-MONAD-USABILITY-19`, and `MCD-RECLOSE-20`

Baseline: local direct-usability checkpoint `3a47e2b` over transparent-whole
checkpoint `e90ce3c`, `ad46632`, `ac1671c`, and the user's earlier checkpoint
`c1f4419`

Worktree: `/home/user1/emdash1-monads-v3.2`

Branch: `goal/monad-comonad-computation-v3.2`

Git authority: the user's 2026-08-23 instruction explicitly authorized
restoring the `main` checkout to `/home/user1/emdash1`, creating this dedicated
goal branch/worktree, starting the persistent goal, evolving this plan, and
performing the scoped implementation and validation. The user separately
authorized the local historical checkpoints through `e90ce3c`, then on
2026-08-26 explicitly authorized checkpoint `3a47e2b` and one final local
commit containing the reviewed correction plus `tmp/EMAIL.md`. Pushes, merges,
publication, release, history rewriting, branch deletion, and worktree removal
remain unauthorized.

Recovery archive: response `0001` is archived at
`/home/user1/emdash1/emdash2/tmp/ai-responses/sessions/2026-08-23_01a02f686142/responses/0001_2026-08-23T16-44-54Z_01a02f6e-40e9-7583-a15c-955153fb9f89.md`.
The archive is recovery evidence only. Active code/SOP and this evolving plan
are authoritative.

## Objective

Add a computational monad interface aligned with active emdash v3.2 whole
functors and higher action, obtain comonad computation by checked opposite
duality, and connect both to the existing indexed adjunction calculus.

The corrected boundary separates four roles:

1. full functor and full transformation observations are the structural
   authority;
2. whole Kleisli extension plus ordinary ambient `comp_fapp0` form Došen's
   selected triangular runtime language;
3. delta/Kleisli composition and an explicit Kleisli category are derived,
   separately gated constructions rather than substitutes for ambient cut
   elimination; and
4. Došen's rectangular and triangular presentations are derived,
   testable views rather than competing global normal forms.

The first implementation target is an additive extension module, provisionally
`emdash3_2_monads.lp`. Promotion into `emdash3_2.lp` is not assumed and would
require a concrete dependency reason plus a separate interaction audit.

## Authority Order

Use, in order:

1. `emdash3_2.lp` for current categories, whole functors, transfors,
   adjunctions, opposites, and hom-action computation;
2. `emdash3_2_checks.lp` for current executable owner and non-collapse
   patterns;
3. `reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`;
4. `reports/EMDASH_FOUNDATIONS.md`;
5. `reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`;
6. `../../docs/ADJUNCTION_USABILITY_V3_2_PLAN.md` for the existing Došen
   mapping and declaration trust boundary;
7. `reports/INDEX.md` and this plan;
8. Kosta Došen, *Cut Elimination in Categories*, especially §§5.1, 5.3,
   5.7, and 5.8, as mathematical source rather than kernel authority.

Došen's cited monadic precedent is Joachim Lambek, “Deductive systems and
categories II: Standard constructions and closed categories,” Lecture Notes
in Mathematics 86 (1969), pp. 76--122, DOI `10.1007/BFb0079385`. The current
review uses Došen's explicit reduction table for orientation; the Lambek
reference confirms provenance rather than replacing that table.

The local source copies are:

```text
/home/user1/dosen-book/kosta-dosen-book-cut-elimination-in-categories.pdf
/home/user1/dosen-book/kosta-dosen-book-cut-elimination-in-categories.txt
```

## Corrected Mathematical Review

### Structural, rectangular, and triangular presentations

Došen distinguishes:

```text
standard:             <A,D,epsilon,delta>
cut-friendly:         <A,D,epsilon^a,delta^c>
triangular/extension: <A,epsilon^a,Delta>.
```

The cut-friendly rectangular laws are necessary and sufficient for his Cut
Disintegration result. The triangular presentation is more economical and
absorbs the rectangular presentation's difficult commuting conversions. It
is the syntax used for the explicit strong-normalization, Church--Rosser, and
commuting decision procedure.

`A*` in §§5.6--5.8 is the category of a free comonad. It is not a parameter of
the general comonad structure. The generic categorical interface and a future
free-syntax normalizer must remain distinct.

### Exact dual reduction orientation

Došen's printed reduction table in §5.8.3 orients the triangular comonad laws
as follows:

```text
f2 o epsilon^a(f1)       -> epsilon^a(f2 o f1)
epsilon^a(f2) o Delta(f1)-> f2 o f1
Delta(f2) o Delta(f1)    -> Delta(f2 o Delta(f1))
Delta(epsilon^a(1_A))    -> 1_DA.
```

Opposite reverses categorical composition but preserves the direction of a
reduction step. With

```text
eta^c(f) : X -> T(Y)
f*       : T(X) -> T(Y)  for f : X -> T(Y),
```

the exact monadic dual is:

```text
eta^c(g) o f       -> eta^c(g o f)
g* o eta^c(f)      -> g o f
g* o f*            -> (g* o f)*
(eta_X)*           -> 1_TX.
```

Here `eta_X = eta^c(1_X)`. In particular, the associativity equation is often
written

```text
(g* o f)* = g* o f*,
```

but Došen's normalization direction is **right-to-left in that displayed
equation**:

```text
g* o f* -> (g* o f)*.
```

This direction removes the top-level cut between two extension-generated
arrows and retains one extension whose inner cut has lower degree. It also
matches the active emdash policy that consecutive stable hom actions
accumulate into one action indexed by a composite.

The previously proposed reverse runtime orientation
`(g* o f)* -> g* o f*` is rejected.

### Ambient composition versus delta/Kleisli composition

The 2026-08-24 source review corrects a more fundamental owner mistake. In
§5.1.5 Došen separately defines delta composition by

```text
f2 odot f1 = f2 o Delta(f1).
```

Its monadic dual is exactly `KleisliCut(g,f)=g* o f`. Došen then treats the
Kleisli category separately in §5.1.6. He explicitly warns that taking delta
composition as primitive is not practical for cut elimination because both
ordinary composition and delta composition would have to be eliminated. His
§5.8.3 normalizer therefore orients reductions on ordinary ambient
composition, not on an `odot`/Kleisli-composition constructor.

The historical checkpoint made `kleisli_cut_func`/`kleisli_cut_fapp0`
primitive owners and left ambient `g* o f*` deliberately non-convertible,
with only `kleisli_extend_comp_path` as equality evidence. That is a useful
Kleisli-composition presentation, but it is not the requested Došen ambient
normalizer. The theorem-level comparison is insufficient at conversion time.

The correction is:

```text
ordinary comp_fapp0(g*,eta^c(f)) -> g o f
ordinary comp_fapp0(g*,f*)       -> (g* o f)*.
```

`KleisliCut` must be deleted as a primitive owner or retained only as
transparent notation. A future `Kleisli_cat(M)` may make it an alias for
ordinary composition in that separate category, but that construction cannot
replace the ambient rules.

### Warning evidence is diagnostic, not a veto

The historical raw probe passed quiet typing but reported four additional
critical pairs and one replaceable pattern variable. That count was used as a
veto, contrary to the active SOP. The minimized corrective probe
`tmp/probes/monad_raw_ambient_review.lp`:

- keeps the ambient composition owner in the component-first beta bridge;
- adds the honest terminal-extension projection;
- uses inferred LHS slots; and
- passes quiet checking and strict LHS audit.

It reports `1133/159`, only two critical-pair reports above the inherited
`1131/159`: the `Op_cat` dual reduction order and the deliberately inherited
`EqSkeleton_cat` composition projection. These reports require explicit
classification and both-order evidence. They neither prove the rule safe nor
justify replacing its semantics by a warning-neutral private head.

### What the theorem transfers, and what it does not

Opposite duality transports the free-comonad reduction relation to the
free-monad reduction relation. Strong normalization, confluence, unique normal
forms, and the free commuting decision procedure therefore transfer through
the syntactic involution.

This does not prove decidability or confluence of the entire Lambdapi/emdash
conversion relation. Every promoted rule must still pass owner-position,
critical-pair, subject-reduction, warning, and higher-action audits. The book's
free-syntax decision procedure is metatheoretical orientation evidence only;
this project deliberately does not schedule a separate free-term grammar or
normalizer.

## Active Emdash Owner Analysis

### Existing owners to reuse

The current kernel already provides:

- `Adjunction(F,G)` indexed by full functors;
- stable `unit_adj_transf` and `counit_adj_transf` observations;
- the two Došen rectangular `(ac)` triangle cut rules;
- involutive `Op_cat`, `Op_func`, and `Op_transf` computation;
- opposite off-diagonal action with swapped endpoints;
- whole `tapp1_func` and capped `tapp1_fapp0` action;
- stable `hom_postcomp_func` and `hom_precomp_along_func` owners;
- runtime accumulation of consecutive postcomposition/precomposition actions;
  and
- proof-time, rather than runtime, ordinary composition associativity.

No active `Monad`, `Comonad`, Kleisli, or Eilenberg--Moore classifier was
found.

### Generic naturality already owns the first triangular law

For `eta : id_A => T`, the existing strict off-diagonal naturality rule owns

```text
eta^c(g) o f -> eta^c(g o f).
```

The monad extension must not add a constructor-specific duplicate of that
rule. It should add only genuinely monadic extension reductions that generic
functoriality/naturality cannot own.

### Semantic whole Kleisli extension

For a full endofunctor `T`, multiplication `mu : T o T => T`, and objects
`X,Y`, the semantic whole extension is the composite

```text
Hom_A(X,T(Y))
  -- T[-] --> Hom_A(T(X),T(T(Y)))
  -- mu_Y o - --> Hom_A(T(X),T(Y)).
```

The existing `fapp1_func` and `hom_postcomp_func` owners express this as a
whole functor and retain higher action. The owner-position probe established
that this transparent semantic definition does not provide a reliable hot law
discriminator. The selected interface therefore keeps stable whole
`kleisli_extend_func`/`kleisli_extend_fapp0` owners. Two SOP-minimal
`unif_rule`s compare the whole and point owners with the actual post-`mu`
semantic normal forms; the former opaque equality path has been removed.

The owner-position probe must reject any design that caps extension to an
arrow family and loses its next hom action.

### One normal-form language for multiplication

The common full multiplication remains a public whole transformation. Its
component satisfies

```text
mu_X = (1_TX)*.
```

If an owner-position probe validates a component bridge, its runtime
orientation should compile standard multiplication syntax into the triangular
owner:

```text
mu_X -> (1_TX)*.
```

The reverse orientation would expose two runtime normal forms. No bridge is
promoted merely from mathematical equivalence; it requires a concrete
adjunction-derived consumer and both-order overlap tests.

The unit has a related projection-order issue: generic computation already
reduces `tapp1(eta,1_X)` to `tapp0(eta,X)`. Consequently, the Kleisli identity
rule must join the component-first and extension-first paths without adding
both broad orientations.

## Proposed Structural API

The first probe should use an indexed relation mirroring active adjunctions:

```text
M : Monad(T)
T : Functor A A

unit_monad_transf(M) : Transf(id_A,T)
mult_monad_transf(M) : Transf(T o T,T).
```

`T` is an index, not a recoverable field. Unit and multiplication are stable
observations. Independently named operations do not compute or unify with
them without declaration-backed evidence, preserving the existing adjunction
trust boundary.

The proposed whole computational surface is:

```text
kleisli_extend_func(M,X,Y)
  : Functor(Hom_A(X,T(Y)), Hom_A(T(X),T(Y))).
```

Its selected object observation, provisionally
`kleisli_extend_fapp0(M,f)`, denotes `f*` and must retain a route to the whole
functor for higher action.

The owner probe accepted these names and the whole/stable-point split.

### Ambient composition is the triangular owner

A direct generic runtime rule on ambient composition,

```text
g* o f* -> (g* o f)*,
```

is required for the Došen runtime language. The optimized component-first
beta bridge is:

```text
g* o eta_X -> g o id_X,
```

which lets specialized ambient categories choose their existing composition
normal form before generic identity elimination. A narrow terminal-extension
projection joins the terminal accumulation order. The remaining `Op_cat` and
`EqSkeleton_cat` reports must be classified at the intended owner position.

The historical stable-cut probe and its warning-neutral boundary remain
valuable backtracking evidence, but warning neutrality obtained by changing
the requested operation is not acceptance evidence. Whole higher action is
already retained by `kleisli_extend_func`; no second whole cut functor is
needed for the ambient rule.

## Opposite-Derived Comonad

The first candidate is the transparent dual facade:

```text
Comonad_A(D) := Monad_(Op(A))(Op_func(D)).
```

Its public observations are definitionally connected to:

```text
counit_comonad_transf(C) := Op_transf(unit_monad_transf(C))
comult_comonad_transf(C) := Op_transf(mult_monad_transf(C)).
```

The mathematical coextension is the endpoint-swapped view of monadic
extension, since

```text
Hom_(Op A)(X,Op(D)[Y]) = Hom_A(D(Y),X).
```

The transparent classifier remains accepted and gives one evidence authority.
A transparent alias cannot itself discriminate a rewrite LHS, so executable
dual rules must match the canonical unfolded monadic/`Op` heads. The first raw
probe repeated `D[X]`, `D[Y]`, `D[Z]`, `Op_func(D)`, and identity endpoints;
that anti-SOP shape passed quietly but overlapped every reducible endofunctor
projection. It is diagnostic evidence only.

The corrected probes then separated two facts. Transparent coextension
accumulation can be made subject-reduction safe with one measured endpoint
guard, but a transparent co-beta rule can be registered and participate in
critical-pair analysis while still missing its exact open runtime term. That
runtime false negative is the measured stable-discriminator blocker required
by the fallback hierarchy.

The `ad46632` checkpoint kept the transparent `Comonad` classifier but still
retained a stable whole and point coextension mirror. Further review showed
that this was one stable head too many. Stable heads are justified by runtime
discrimination, not merely by duality or API symmetry:

- `Op_transf(unit)` and `Op_transf(mult)` fold to stable whole counit and
  comultiplication observations, with reverse `Op_transf` folds for
  double-opposite recovery. These whole observations remain stable because
  their heads occur under the triangular `tapp*` discriminators;
- direct opposite unit/multiplication components fold toward the stable
  components, preserving the component-first triangular heads;
- whole coextension is transparently the endpoint-swapped primary monadic
  whole extension. It needs neither a second primitive owner, a custom `fapp0`
  rule, nor a proof-time comparison, because no triangular LHS discriminates
  on the whole coextension head;
- point opposite extension folds at the surviving `Op_func(D)` head, with all
  category and endpoint LHS slots inferred. This stable point remains
  necessary because ambient co-beta and accumulation discriminate on it; and
- the duplicated ambient dual beta/accumulation rules operate only on those
  stable point and observation heads.

All former opaque equality constants have been deleted. This is the same
layered pattern seen elsewhere: transparent dual classifiers at theorem level,
with stable owners only where normalization destroys a required runtime
discriminator. The quiet-green
`tmp/probes/monad_comonad_transparent_whole_review.lp` confirms that generic
whole projection, retained higher action, co-beta, and accumulation all work
with only the stable point mirror.

## Adjunction-Derived Consumers

For

```text
J : Adjunction(F,G)
F : Functor R L
G : Functor L R,
```

the first concrete monad consumer is:

```text
T   = G o F                  on R
eta = unit_adj_transf(J)
mu  = G counit_adj_transf(J) F.
```

The comonad is:

```text
D       = F o G              on L
epsilon = counit_adj_transf(J)
delta   = F unit_adj_transf(J) G.
```

The transparent construction `adjunction_monad(Op_adjunction(J))` folds into
the retained stable `adjunction_comonad` witness, because the transparent
argument likewise fails to remain a reliable discriminator below stable
comonad observations. Both its Monad-on-opposite and Comonad observations now
follow the selected narrow dual runtime mirror. On the primary
`adjunction_monad(J)` side, the source adjunction unit is a proof-time
usability endpoint rather than a reduct of the canonical unit owner. Whole
multiplication remains semantic and reduces to transparent `G epsilon F`.
The selected comultiplication is the `Op` of that transparent
opposite-adjunction multiplication; mathematically this is the usual
`F eta G`. The former opaque equality paths remain deleted.

The adjunction-derived instance is mandatory before any generic monad rule is
promoted. It exercises the existing stable unit/counit observations and gives
the rectangular-to-triangular interaction a real consumer.

## Required Positive And Negative Evidence

Every candidate implementation must include:

1. exact types of `Monad(T)`, unit, multiplication, and whole Kleisli
   extension;
2. one retained next hom action of `kleisli_extend_func`;
3. ambient beta conversion `g* o eta^c(f) -> g o f`, including its
   component-first projection order;
4. ambient accumulation conversion `g* o f* -> (g* o f)*`;
5. unit-extension reduction `(eta_X)* -> 1_TX`, including both projection
   orders around `tapp1(eta,1_X) -> tapp0(eta,X)`;
6. absence of the reverse accumulation rewrite;
7. an independently named same-typed unit/multiplication non-agreement;
8. a positive adjunction-derived monad instance;
9. executable ambient comonad beta and accumulation in the exact dual
   directions, not merely equality paths through `Op`;
10. a positive opposite-derived comonad instance, double-opposite recovery,
    and exact counit/comultiplication observations;
11. noncollapse negatives showing that independently named same-typed
    observations do not acquire definitional agreement; this generic layer
    must not be advertised as a model-theoretic free or non-idempotent monad;
    and
12. both-order checks for every overlap with generic naturality,
    functoriality, identity, associativity, or stable hom-action accumulation.

## Work Ledger

| Row | Status | Depends on | Deliverable |
| --- | --- | --- | --- |
| `MCD-00` | complete | user review; baseline `689f41c` | Living plan, source audit, exact dual reduction table, restored root `main`, dedicated goal/worktree, Infinity verification, and green bounded baseline. |
| `MCD-OWNER-1` | historical/superseded | `MCD-00` | Correctly selected stable whole extension plus capped projection, but incorrectly selected primitive Kleisli cut in place of ambient composition. Preserved at `c1f4419`. |
| `MCD-MONAD-2` | complete | accepted `MCD-OWNER-1` | `emdash3_2_monads.lp` adds indexed `Monad(T)`, stable full unit/multiplication, semantic equality paths, and trust negatives. |
| `MCD-KLEISLI-3` | historical/superseded | `MCD-MONAD-2` | Primitive Kleisli-composition implementation and raw-composition negative preserved at `c1f4419`; not accepted as Došen ambient computation. |
| `MCD-OP-4` | historical/superseded | `MCD-AMBIENT-9` | The classifier and standard observations remain useful, but its transparent facade did not supply ambient dual reductions. The completed `MCD-DUAL-10` replaces that facade. |
| `MCD-ADJ-5` | historical/superseded in its runtime-observation boundary | `MCD-MONAD-2`, `MCD-OP-4` | Correctly supplied adjunction-derived witnesses and exact `G epsilon F`/`F eta G` data, but prematurely made the Monad observations reduce to the adjunction spellings. `MCD-MONAD-USABILITY-19` retains the construction while moving those two comparisons to proof time. |
| `MCD-CLOSE-6` | historical/superseded | historical implementation rows | Green checkpoint evidence at `c1f4419`; superseded semantically by the 2026-08-24 review. |
| `MCD-FREE-7` | out of scope | explicit user decision, 2026-08-25 | Došen's free-syntax normalizer and decidability proof remain metatheory; emdash implements their useful ambient rewrite consequences only. |
| `MCD-TS-8` | deferred | stable kernel API plus TypeScript consumer | Optional outer-LF automation of the now-selected usability protocol remains future work; this correction implements the proof-time boundary directly in Lambdapi and adds no TypeScript. |
| `MCD-AMBIENT-9` | complete | historical checkpoint `c1f4419`; response `0003` | Ambient monad beta/accumulation, component and Terminal joins, positive conversion checks, transparent `KleisliCut`, and classified `Op_cat`/`EqSkeleton_cat` orders. |
| `MCD-DUAL-10` | historical/superseded | accepted `MCD-AMBIENT-9` | The stable whole/point coextension facade and opaque Op equality evidence are preserved at `ac1671c` but are not the selected definitional-duality architecture. |
| `MCD-KLCAT-11` | deferred/separate | stable ambient calculus plus explicit consumer | Optional `Kleisli_cat(M)`, canonical functors, and composition aliases. It must not replace ambient normalization. |
| `MCD-RECLOSE-12` | historical checkpoint | `MCD-AMBIENT-9`, `MCD-DUAL-10` | Checks/examples/authorities, catalog, health, warning/order audits, and full 270-file CI are preserved at `ac1671c`. |
| `MCD-MONAD-SOP-13` | complete | checkpoint `ac1671c`; response `0007` | Primary Monad rules bind category/functor indices once at rigid operation heads; strict LHS audit is empty. Whole/point semantic comparison uses two proof-time equations at the actual post-`mu` normal forms, and the opaque path is gone. |
| `MCD-OP-DEF-14` | complete | accepted `MCD-MONAD-SOP-13` | `Op_transf _ _ _ _ (Op_transf _ _ _ _ eta) -> eta` is the active involution owner. Base checking is green at `1116/159`, down from `1131/159`, and the opposite-adjunction counit route computes. |
| `MCD-CODUAL-15` | historical checkpoint | accepted `MCD-MONAD-SOP-13`, `MCD-OP-DEF-14` | Checkpoint `ad46632` removed opaque duality evidence and supplied the narrow runtime mirror, but still retained an unnecessary stable whole coextension plus proof-time comparison. `MCD-CODUAL-WHOLE-17` corrects that final excess owner. |
| `MCD-RECLOSE-16` | historical checkpoint | accepted implementation rows | The 2,260-check catalog, warning/audit boundary, fresh 270-file health, and independent full CI are preserved at `ad46632`. |
| `MCD-CODUAL-WHOLE-17` | complete | checkpoint `ad46632`; user review | Stable whole coextension is now the transparent endpoint-swapped primary monadic whole owner. Its custom point projection and whole unifier are removed; stable observations and stable point coextension remain as the only justified dual runtime discriminators. |
| `MCD-RECLOSE-18` | complete | accepted `MCD-CODUAL-WHOLE-17`; user-scoped validation boundary | Focused module/check/example/probe validation, strict LHS audit, active rationale documents, unchanged `1140/159` module warnings, the 2,260-check catalog, and fresh 270-target health are synchronized. Per the user's 2026-08-25 instruction, no further repository-wide long aggregate was required; an already-started independent CI sweep was stopped after its snapshot gate and initial green targets. |
| `MCD-MONAD-USABILITY-19` | complete | checkpoint `e90ce3c`; response `0014`; user clarification 2026-08-26 | `adjunction_monad(J)` remains the canonical witness. Only its unit runtime projection is replaced by a SOP-minimal proof-time agreement because the unit head occurs in triangular LHSs. Whole multiplication is semantic rather than a triangular discriminator, so its runtime projection to transparent `G epsilon F` is retained. A non-axiomatic path, checked from the common component before installing the whole projection, propositionally joins the `G epsilon F` component and `(id_TX)*`. The rejected opacity workaround and multiplication `unif_rule` are absent. TypeScript automation remains deferred. |
| `MCD-RECLOSE-20` | complete | accepted `MCD-MONAD-USABILITY-19`; user-scoped validation boundary | Module, 2,268-check central suite, reviewer example, both unit proof-time orientations, runtime/proof-time unit nonleakage, semantic whole multiplication, propositional component join, opposite/comonad routes, `1139/159` warnings, zero strict-LHS findings, catalog, active references, report headers, source TOC, and exact diff are green. Per user instruction, no repository-wide health or CI aggregate was run. |

No implementation row remains in progress. A rejected probe updates the
decision ledger and may split or defer its dependent row rather than forcing
the proposed signature.

## Decision Ledger

| Decision | Status | Conclusion |
| --- | --- | --- |
| `D-MCD-001` | accepted | Monad is the primary public/primitive direction; comonad is obtained through checked opposite duality. |
| `D-MCD-002` | accepted | Full endofunctor and full unit/multiplication transfors are structural authority; an object-only triangular structure is not the sole emdash core. |
| `D-MCD-003` | corrected/accepted | Whole extension is retained, but ordinary ambient composition is the Došen runtime owner. Primitive Kleisli cut is not the ambient normalizer. |
| `D-MCD-004` | corrected/accepted | Runtime accumulation is `g* o f* -> (g* o f)*`. The previously proposed reverse orientation is rejected. |
| `D-MCD-005` | accepted | Generic `tapp1` naturality owns `eta^c(g) o f -> eta^c(g o f)`; do not duplicate it in the monad module. |
| `D-MCD-006` | accepted | Multiplication components compile one-way toward `(1_TX)*`; the reverse is absent. |
| `D-MCD-007` | corrected/accepted | `Comonad_A(D) := Monad_(A^op)(D^op)` remains the evidence classifier. Improve generic Op inference and use unfolded primary heads before considering any generic mirror owner; do not introduce an equality-connected comonad facade. |
| `D-MCD-008` | accepted | The four triangular laws are retained for the full monad/equality normalizer even though the identity-extension law is not needed for Cut Disintegration alone. |
| `D-MCD-009` | accepted | `A*` freeness and the decision algorithm are separate from the generic monad relation and generic Lambdapi conversion. |
| `D-MCD-010` | accepted | The first real consumer is the monad/comonad induced by the existing indexed adjunction. |
| `D-MCD-011` | refined Git boundary | Dedicated branch/worktree and scoped edits were initially authorized without commits. The user separately authorized one local post-validation checkpoint on 2026-08-25; remote, integration, history-rewrite, publication, and cleanup mutations remain unauthorized. |
| `D-MCD-012` | resolved/accepted | Kleisli extension remains the selected whole/point monadic runtime owner. Two SOP-minimal proof-time equations connect it to the actual semantic normal forms; no opaque equality constant or hot expansion is used. |
| `D-MCD-013` | corrected/accepted | `Comonad` remains a transparent classifier. Stable counit/comultiplication and point coextension are retained only where Op normalization loses a required runtime discriminator. Whole coextension transparently reuses primary monadic whole extension. |
| `D-MCD-014` | reversed/accepted requirement | Ambient `comp_fapp0(g*,f*) -> ...` is required. Its warning families must be classified and joined where appropriate; warning count alone is not a veto. |
| `D-MCD-015` | historical/superseded | The inferred-slot result remains useful evidence, but the primitive stable-cut rule it governed is no longer the selected owner. |
| `D-MCD-016` | partially superseded | `adjunction_monad(Op_adjunction(J))` still folds into the stable adjunction-comonad witness. Its claim that adjunction-derived Monad observations should reduce at runtime is superseded by `D-MCD-039`; the source operations are proof-time usability endpoints. |
| `D-MCD-017` | historical closeout | Records the green `c1f4419` checkpoint; its semantic acceptance conclusion is superseded. |
| `D-MCD-018` | accepted source correction | Došen's delta/Kleisli composition and Kleisli category are separate from the ambient-composition reductions used by §5.8.3. |
| `D-MCD-019` | accepted warning policy | Critical-pair reports are classified diagnostic evidence. Preserve intended computation unless an actual cycle, subject-reduction failure, unacceptable conversion loss, or better owner is demonstrated. |
| `D-MCD-020` | accepted separation | A future explicit Kleisli category may derive `KleisliCut` from its ordinary composition and extension from its canonical right functor; it is not part of the corrective ambient tranche. |
| `D-MCD-021` | corrected/accepted | The former 19-report bridge delta was warning evidence, not a veto. The selected point bridge matches only the surviving `Op_func(D)` owner. The former whole proof-time bridge is removed because transparent whole reuse is sufficient. |
| `D-MCD-022` | historical warning boundary | `1135/159` is the `ac1671c` module inventory. The current definitional-duality boundary is recorded separately by `D-MCD-035`. |
| `D-MCD-023` | accepted scope correction | Do not implement a free monad/comonad syntax, normalizer, or commuting decision procedure; use Došen's results only to select the useful ambient reductions. |
| `D-MCD-024` | accepted definitional boundary | Opaque equality constants may not mediate Monad/comonad duality or semantic/runtime presentations. Use transparent definitions, selected runtime folds, or narrowly validated `unif_rule`s. |
| `D-MCD-025` | accepted SOP correction | Bind an inferred category/functor once at a rigid operation head; repeat it nowhere else on a rule LHS unless a measured subject-reduction failure makes it a real discriminator, then annotate the retained slot. |
| `D-MCD-026` | accepted probe direction | The candidate `Op_transf _ _ _ _ (Op_transf _ _ _ _ eta) -> eta` is quiet-green, strict-LHS-green, and closes the adjunction-counit route. Measure it only as an owner-position replacement, not beside the old rule. |
| `D-MCD-027` | accepted sequencing | Monad is the required primary computation. Executable comonad duality is an optional, subsequent, uniform `Op` consumer and must not block the monad correction. |
| `D-MCD-028` | accepted fallback hierarchy | Weighted colimits are transparent opposite-weighted limits, while lower variance infrastructure sometimes has parallel stable owners (`Prof_imply_cov/con`, `hom_int/con_int`). A comonad mirror is a last-resort generic variance design, not the first solution. |
| `D-MCD-029` | rejected probe shape | The expanded semantic-unification and raw dual rules that repeated `D[X]`, `D[Y]`, identity endpoints, and `Op_func(D)` together are anti-SOP false-negative probes. The later point bridge keeps only the independently necessary `Op_func(D)` discriminator. |
| `D-MCD-030` | accepted measured blocker | Transparent dual accumulation is subject-reduction feasible, but the transparent co-beta rule was registered yet missed its exact open runtime term. This runtime false negative, not warning count, justifies the narrow stable variance mirror. |
| `D-MCD-031` | historical/superseded | `ad46632` used a whole `unif_rule` and point runtime fold. The resulting two whole runtime heads were an unnecessary asymmetry; `D-MCD-038` replaces it. |
| `D-MCD-032` | accepted component direction | Raw opposite unit/multiplication components fold toward stable comonad components. The reverse direction erased component-first triangular discriminators and was rejected. |
| `D-MCD-033` | accepted observation duality | Whole unit/multiplication under `Op_transf` fold to counit/comultiplication, with reverse Op folds for double-opposite recovery. No opaque equality constant remains. |
| `D-MCD-034` | accepted with corrected usability boundary | The stable adjunction-comonad witness is retained because a transparent defined argument is not a reliable observation discriminator. The opposite-adjunction witness fold and canonical dual observations remain. On the primary adjunction-to-Monad side, only the unit spelling stops erasing its canonical runtime head; whole multiplication deliberately remains semantic. |
| `D-MCD-035` | historical warning boundary | At `e90ce3c`, base warnings are `1116/159` and the monad module is `1140/159`, including two adjunction-operation critical pairs created by the now-superseded runtime projections. `D-MCD-042` records the corrected boundary. |
| `D-MCD-036` | accepted local checkpoint | After the complete green closeout, the user explicitly authorized committing this bounded tranche as a local historical checkpoint. This does not authorize push, merge, publication, release, history rewriting, branch deletion, or worktree removal. |
| `D-MCD-037` | accepted stable-head criterion | A dual stable head is justified only when an active runtime LHS must discriminate on it after Op normalization. API symmetry, warning count, or proof-time convenience alone is insufficient. |
| `D-MCD-038` | accepted transparent whole | No triangular rule matches whole coextension. Define it transparently as endpoint-swapped `kleisli_extend_func`; generic projection plus the retained point fold gives the stable point, and primary higher action remains available. Remove the custom whole projection rule and whole unifier. |
| `D-MCD-039` | corrected/accepted direct usability boundary | Canonical `unit_monad_transf(adjunction_monad(J))` remains a runtime discriminator because it occurs in triangular beta/unit-extension LHSs; `unit_adj_transf(J)` is its proof-time usability endpoint. Whole `mult_monad_transf` is semantic rather than a primary triangular discriminator and retains its runtime projection to transparent `G epsilon F`. TypeScript automation is deferred. |
| `D-MCD-040` | rejected opacity workaround | Making `adjunction_monad_mult_transf(J)` opaque forced a rigid proof-time endpoint but discarded its `G epsilon F` body from runtime reduction. This is not normal computational-owner SOP and is removed. The bare-variable fallback is also rejected: it violated the two-rigid-head preference and triggered a Lambdapi evaluator assertion. |
| `D-MCD-041` | accepted asymmetric evidence boundary | Typed `eq_refl` exercises both unit-agreement orientations, while raw adjunction unit runtime conversion remains false. Whole multiplication conversion to transparent `G epsilon F` is positive. Its whole-first semantic component and component-first `(id_TX)*` reduction are propositionally joined by a non-axiomatic path defined from their common ancestor; no duplicate triangular runtime owner is added. |
| `D-MCD-042` | accepted measured boundary | Warning-enabled module checking is `1139/159`, removing the historical unit-observation overlap from `1140/159` while retaining the intended semantic multiplication overlap and adding no replaceable-variable diagnostics. The strict LHS audit remains empty. |
| `D-MCD-043` | accepted local checkpoints | The user explicitly authorized two local commits on 2026-08-26: `3a47e2b` records the first reviewed direct-usability tranche, and one final commit may record the corrected asymmetric unit/multiplication boundary, propositional component join, synchronized authorities, and `tmp/EMAIL.md`. This does not authorize any remote or integration mutation. |

## Historical First-Checkpoint Evidence

The formerly accepted owner probe is `tmp/probes/monad_kleisli_cut.lp`. Its
quiet and warning-enabled runs are preserved as historical evidence:

```text
logs/probes/monad_kleisli_cut-20260823-141458.log
logs/probes/monad_kleisli_cut-20260823-141543.log
```

The minimized precursor run at `20260823-140408` established the inherited
`1131/159` warning boundary. The first raw-composition probe is
`tmp/probes/monad_kleisli_rules.lp`; its warning-enabled run at
`20260823-135351` measured `1135/160`, including four new unjoinable pairs.
That result is no longer rejection evidence. The broad opposite-involution
probe in `monad_owner_types.lp` reached `1141` unjoinable pairs and remains
unpromoted.

Corrective review probes are:

```text
tmp/probes/monad_raw_ambient_review.lp
tmp/probes/monad_kleisli_category_review.lp
tmp/probes/monad_raw_dual_review.lp
```

The minimized ambient monad probe is quiet-green, strict-LHS-green, and
reports `1133/159` after joining the component-first Terminal order and the
terminal-extension order. Its remaining reports are precisely `Op_cat` and
`EqSkeleton_cat`. The separate Kleisli-category feasibility probe is
quiet-green, strict-LHS-green, and exactly `1131/159` when extension is the
hom action of the canonical right functor. The naive transparent-Op dual probe
shows why `MCD-DUAL-10` needs a stable facade or narrow bridge: literal
reducible `D[-]` guards produce hundreds of avoidable overlaps.

Tracked implementation now includes:

```text
emdash3_2_monads.lp
emdash3_2_checks.lp
examples/monads_comonads.lp
scripts/check.sh
scripts/check_metrics.py
```

Focused evidence is green:

```bash
./scripts/check.sh emdash3_2_monads.lp
./scripts/check.sh emdash3_2_checks.lp
timeout --signal=INT 90s lambdapi check -w examples/monads_comonads.lp
python3 scripts/audit_rule_lhs.py --strict emdash3_2_monads.lp
```

The warning-enabled module check is exactly `1131/159`, so the accepted
module adds zero warnings. The strict module LHS audit reports zero
reconstructible compound slots and zero unreviewed clauses.

## Historical ad46632 Definitional-Duality Evidence

At checkpoint `ad46632`, the primary Monad correction was focused-green. Its ambient beta,
component-beta, accumulation, unit-extension, and multiplication-component
rules have SOP-minimal inferred LHS slots. The semantic whole and point
comparisons are proof-time equations at the actual post-multiplication normal
forms; the former opaque semantic path is absent. The strict module audit
reports zero reconstructible compound slots and zero unreviewed clauses.

The generic `Op_transf` involution is now fully inferred. The base warning
inventory is `1116/159`, down from checkpoint-era `1131/159`, and the formerly
blocked opposite-adjunction counit route computes by typed conversion.

The dual probe sequence records the selected fallback boundary:

```text
tmp/probes/monad_transparent_comonad_accum_review.lp
  transparent accumulation: quiet-green after owner reconstruction

tmp/probes/monad_transparent_comonad_beta_review.lp
  fused transparent co-beta: subject-reduction valid and warning-visible,
  but exact generic open-term conversion still misses

tmp/probes/monad_comonad_definitional_mirror_review.lp
  stable variance mirror with runtime/proof-time Op bridges: quiet-green

tmp/probes/monad_comonad_component_unif_review.lp
  raw-component-to-stable direction: quiet-green and strict-LHS-green
```

The checkpointed module has no opaque constants. Canonical raw Op observations,
components, and point extensions feed the stable mirror; whole extension uses
proof-time comparison. Both stable and raw ambient co-beta/accumulation,
double-opposite observation recovery, retained higher action, and all four
adjunction-derived observations are central-check green. The generated catalog
now records 2,260 checks across 110 mapped areas, including 52 checks in the
Monad/comonad area, with zero unclassified checks. The reviewer example has 14
statements; both its changed target and the complete registered reviewer sweep
are green.

Warning-enabled module checking is `1140/159` against the `1116/159` base.
The 24-report module delta is:

```text
 8  primary/dual accumulation against Op, EqSkeleton, and Terminal orders
 9  Op_func point-bridge projection orders
 4  whole observation against double-Op involution
 2  observation bridge against concrete adjunction-monad projection
 1  opposite-adjunction witness bridge against Op_adjunction involution
```

These are classified diagnostics, not vetoes. Typed checks cover the intended
raw/stable, component-first, Terminal, double-opposite, and adjunction routes.

The fresh health pass checked all 270 registered files with zero failures and
no resumed evidence. It records source snapshot
`sha256:dfd5b4a779f5cd0df4222f8dbfd3a4d6951f27c4267f6e9eab52a7a6b2e89206`
and check-content snapshot
`sha256:d25158420e69f5401872f2b67abe45cc6de68aa807517a0a10578ae511b684e2`.
The monad module is 931 lines with 30 symbols, 29 runtime rules, and three
proof-time equations; the reviewer example is 237 lines with 13 positive
assertions plus one negative.

The final `make ci` gate independently checked all 270 registered files in
1,802.847 seconds. Its post-check gates passed 44 Python unit tests, 5 Node
registry tests, Python and shell syntax, diff hygiene, source TOC, active
references, report headers, book evidence/typography/KaTeX/assembly, the base
strict LHS audit, and strict catalog freshness. The user subsequently
authorized one local historical checkpoint of this validated tranche. Push,
merge, publication, release, history rewrite, branch deletion, and worktree
removal remain outside that authorization.

## Post-e90ce3c Direct Monad-Usability Evidence

The adjunction-usability precedent separates canonical runtime observations
from independently named proof-time agreement endpoints. Applying that
boundary directly in Lambdapi removes the unit runtime projection from
`unit_monad_transf(adjunction_monad(J))` to `unit_adj_transf(J)`. The
replacement `unif_rule` binds only the witness `J`; all category and functor
slots are inferred.

The multiplication case is intentionally asymmetric. Whole
`mult_monad_transf` is a standard semantic observation, not a primary
triangular discriminator; its component alone compiles into `(-)*`.
Accordingly the adjunction-induced whole multiplication retains its runtime
projection to the transparent checked `G epsilon F` construction. A rejected
opacity workaround made that construction rigid enough for a second
`unif_rule` only by removing its semantic body from reduction. A rejected
bare-variable fallback also triggered a Lambdapi evaluator assertion. Neither
workaround is part of the implementation.

Focused diagnostics verify both unit-agreement orientations, runtime and
proof-time unit nonleakage, canonical beta and unit-extension for the
adjunction-induced witness, whole multiplication projection to `G epsilon F`,
and the propositional join between the whole-first semantic component and the
component-first `(id_TX)*` branch. That join is not an axiom: its first path is
checked by reflexivity at the common component before the whole multiplication
projection is installed; after installation, the exported path has the two
desired reducts as endpoints. It does not change runtime reduction preference.

Module, the 2,268-check central diagnostics with zero unclassified checks, and
the reviewer example are focused-green. Warning-enabled module checking is
`1139/159` against the unchanged `1116/159` base, eliminating the historical
unit-observation critical pair while retaining the intended semantic
multiplication interaction and adding no replaceable-variable diagnostics.
The strict module LHS audit is empty; catalog, active-reference, report-header,
source-TOC, and exact-diff checks are green. Per the user's scoped-validation
instruction, no repository-wide health or CI aggregate was run.

## Post-ad46632 Transparent-Whole Evidence

The owner-position probe
`tmp/probes/monad_comonad_transparent_whole_review.lp` is quiet-green and
strict-LHS-green. With whole coextension defined transparently as
endpoint-swapped `kleisli_extend_func`, it verifies:

- generic whole object projection reaches stable point coextension through the
  existing primary projection and `Op_func(D)` point fold;
- the primary whole owner retains the next hom action;
- the projected whole term feeds ambient comonad beta; and
- two projected whole terms feed ambient comonad accumulation.

The active correction therefore removes the primitive/injective whole
coextension owner, its custom `fapp0` rule, and its proof-time equation. Stable
counit, comultiplication, and point coextension remain because their heads are
actual triangular runtime discriminators. This is explicitly a narrow
computational mirror rather than a duplicated full comonad theory. Focused
module, central, reviewer, and probe checks are green, and the strict module
LHS audit remains empty. Warning-enabled module checking remains `1140/159`
against the `1116/159` base: removing the unnecessary whole owner changes the
architecture, not the classified warning boundary. The regenerated catalog
contains 2,260 checks across 110 mapped areas with zero unclassified checks.
Fresh health checks all 270 registered kernel/example targets with zero
failures and zero resumed results; its source-metrics and checked-content
snapshots are respectively
`e7914e963e5a71d01907813e284f9f792a44bb9bd1668af8b516ff81f519c7cd`
and `aba9a05571c9e6d7785d9e3800feeaba354fb354149f6182638dbeb9b7be664d`.

After that health run, the user explicitly narrowed final validation to the
changed files and features and asked to avoid further repository-wide long
aggregates. An independent CI sweep that had just started was therefore
stopped after its health-snapshot gate and initial green targets. The scoped
closure uses the focused checks above plus catalog, health-snapshot,
active-reference, report-header, source-TOC, and exact-diff consistency gates;
it does not claim a new completed full-CI run for this post-checkpoint
correction.

## Historical ac1671c Corrective Evidence

At checkpoint `ac1671c`, the then-corrected module, central diagnostics, and
reviewer example were focused-green. The central area contained 37 checks,
and the reviewer had 12 statements. The generated catalog contained 2,244
checks across 110 mapped areas with zero unclassified entries.

The strict module LHS audit was empty. Warning-enabled checking reported
`1135/159`, a classified delta of four critical-pair reports:

```text
monad accumulation   x Op_cat
monad accumulation   x EqSkeleton_cat
comonad accumulation x Op_cat
comonad accumulation x EqSkeleton_cat
```

The component-first beta orders preserve ambient identity composition, and
the monad/comonad Terminal extension projections join the Terminal orders.
Stable whole coextension retains higher action and explicit whole/point
equality evidence to opposite monadic extension. A proposed direct runtime Op
bridge passed quiet typing but raised the boundary to `1154/159`, duplicating
19 whole/higher-action projection interactions; it was removed. The four
remaining reports expose ordinary category projection before versus after the
intended accumulation law and are retained as classified warning debt rather
than treated as a semantic veto.

The complete reviewer-example sweep and fresh 270-file health pass were green.
The health report recorded source snapshot
`sha256:3bdea4b20549469d0d2cdbfad57a4a184e333b58f7a6d27467419ddcbc48a0bc`
and check-content snapshot
`sha256:efac5fae4151945619b94ef41a713fc8eb97b99fb6e3e5ad594cd731d539acc3`.
It records current exit-0 evidence for the 1,013-line/40-symbol/18-rule monad
module, central checks, and the 205-line reviewer example.

The full `make ci` closeout checked all 270 registered files in 1,316.709
seconds. Its post-check gates passed 44 Python unit tests, 5 Node registry
tests, source TOC and active-reference lint, report headers, book
evidence/typography/KaTeX and assembly checks, shell syntax, Python
compilation, diff hygiene, the base strict LHS audit, and strict catalog and
health freshness. No commit, push, merge, publication, release, history
rewrite, branch deletion, or worktree removal was performed by this
corrective goal.

## Historical Closeout Evidence

At checkpoint `c1f4419`, the generated catalog records 2,233 checks in 110
areas, including 26 checks under `Monad and comonad triangular computation`,
with zero unclassified checks. The repository warning inventory remains
exactly 1,290 inherited
warnings: 1,131 unjoinable critical pairs and 159 replaceable pattern
variables. The historical module therefore added no warning delta by moving
computation to its private head; this is no longer semantic acceptance
evidence.

At that checkpoint, its health report recorded source-metrics snapshot
`sha256:0744074076bbdf57f26343a2d6f49e05d0e4bd86e70f99de2b8cff9603058b5b`
and check-content snapshot
`sha256:28f9c195853ad966491bd2756c7a681fd2f36cb4bd8ebc871b67cee8b70418a2`.
It records exit 0 for `emdash3_2_monads.lp`, `emdash3_2_checks.lp`, and
`examples/monads_comonads.lp`, together with every other registered source
and example.

Closeout commands completed green:

```bash
make examples
make warning-summary
make audit-rules
python3 scripts/audit_rule_lhs.py --strict emdash3_2_monads.lp
make catalog
make health
make ci
```

The independent CI metrics pass checked 270 files in 1,267.575 seconds. Its
post-check gates passed 44 Python unit tests, 5 Node registry tests, source
TOC and active-reference lint, report headers, book evidence/typography/KaTeX
and assembly checks, shell syntax, Python compilation, diff hygiene, the base
strict LHS audit, and strict catalog freshness. No commit, push, merge,
publication, release, history rewrite, branch deletion, or worktree removal
was performed.

At historical checkpoint `c1f4419`, the raw-composition negative and
independently named unit/multiplication negatives were deliberately
conversion-level noncollapse evidence. The raw-composition negative is now
superseded by positive ambient reductions. The remaining negatives do not
claim that this generic interface constructs a free, non-idempotent model.
No free-syntax construction or normalizer is scheduled.

## Validation Policy

All Lambdapi targets are bounded to 90 seconds. The first implementation row
must follow:

```text
owner-position full-file probe
  -> focused positive and negative assertions
  -> bounded active-kernel check
  -> warning comparison
  -> strict inferred-LHS audit
  -> additive extension registration
  -> focused source and reviewer checks
  -> catalog/health synchronization
  -> proportional CI.
```

Required commands, selected proportionally as rows advance, include:

```bash
EMDASH_TYPECHECK_TIMEOUT=90s make check
scripts/probe.sh tmp/probes/monad_owner.lp
make check-warnings
make warning-summary
make audit-rules
make examples
make catalog
make health
make ci
```

Do not run root TypeScript, print, browser, book, package, or repository-wide
aggregates unless a changed cross-layer contract makes them relevant.

### Baseline evidence

Before the first implementation, the clean goal worktree at `689f41c` passed
the full registered check. The user then committed the complete first tranche
as historical checkpoint `c1f4419`. At the start of the corrective goal that
checkpoint passed:

```bash
./scripts/check.sh emdash3_2_monads.lp
./scripts/check.sh emdash3_2_checks.lp
make warning-summary  # 1131/159
```

Its prior 270-file health and CI evidence remains exact-byte historical
evidence. This is comparison evidence, not permission to skip affected checks
after correction.

## Acceptance And Stop Conditions

The first kernel tranche is accepted only when:

- the indexed full-functor Monad interface is stable and declaration-safe;
- Kleisli extension is whole and retains higher action;
- the exact Došen-dual reductions compute on ordinary ambient composition in
  the corrected orientation;
- the rejected reverse orientation remains absent;
- every new warning family is classified with both-order evidence, and every
  practical narrow join is installed without cycles or subject-reduction
  failure;
- if the optional comonad row is promoted, opposite duality provides genuine
  computation and double-opposite recovery without opaque equality bridges;
- primitive `KleisliCut` is absent from the ambient owner boundary or is only
  transparent derived notation;
- the existing adjunction constructs both sides with exact unit/counit and
  whiskered multiplication/comultiplication;
- noncollapse negatives preserve the declaration trust boundary without
  overstating the generic interface as a free or non-idempotent model; and
- warnings, audits, diagnostics, examples, catalog, health, and affected
  authorities are synchronized.

Stop and revise rather than promote if:

- the Kleisli surface loses the whole functor needed for higher action;
- a proposed optional Comonad rule still has an actual subject-reduction or
  runtime-matching blocker after generic Op/inference alternatives are
  exhausted;
- standard multiplication and Kleisli extension create competing runtime
  normal forms that cannot be joined narrowly;
- a candidate rule duplicates generic naturality/functoriality;
- the corrected accumulation direction creates a cycle with a semantic
  expansion or existing hom-action fold; or
- a global rewrite is justified only by the free-category metatheorem rather
  than a typed active consumer; or
- warning neutrality is obtained only by replacing ambient computation with
  a private operation head.

## Completed Direct Usability Objective

```text
Execute the post-e90ce3c direct Monad-usability correction in this evolving
plan. Keep adjunction_monad(J) as the canonical formal witness and keep its
unit observation as the runtime head consumed by the triangular calculus.
Relate unit_adj_transf(J) by one SOP-minimal proof-time agreement, with typed
eq_refl and runtime-negative evidence. Retain whole multiplication as the
semantic runtime projection to transparent G-epsilon-F; keep the generic
component-to-extension rule and expose a derived propositional join of the two
component reductions. Do not add per-adjunction triangular runtime rewrites,
change the Terminal rule, or implement the deferred TypeScript automation.
Audit the opposite/comonad routes and run only scoped validation. Preserve
checkpoint e90ce3c and unrelated work. Make only the two local commits
explicitly authorized by the user after review; do not push, merge, publish,
release, rewrite history, delete branches, or remove worktrees.
```

## Completed Transparent-Whole Objective

```text
Execute the post-ad46632 transparent-whole correction in this evolving plan.
Keep Monad primary and `Comonad` transparently classified on the opposite
category. Retain stable comonad heads only where an active runtime LHS needs a
post-Op discriminator: counit, comultiplication, and point coextension. Make
whole coextension transparently reuse endpoint-swapped monadic whole extension;
remove its custom projection rule and proof-time equation. Synchronize checks,
examples, active authorities, warning evidence, catalog, health, and CI.
Preserve checkpoint `ad46632` and unrelated work. Do not commit, push, merge,
publish, release, rewrite history, delete branches, or remove worktrees without
separate authorization.
```
