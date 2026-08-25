# Emdash v3.2 Monad And Comonad Computation Plan

Date: 2026-08-23 (America/Toronto)

Plan-ID: `MONAD-COMONAD-COMPUTATION-V3.2`

Status: **completed corrective persistent goal as of 2026-08-24**. Commit
`c1f4419` preserves the first implementation as a historical checkpoint, but
its substitution of primitive `KleisliCut` computation for Došen's ambient
composition reductions is superseded. `MCD-AMBIENT-9` and `MCD-DUAL-10` are
complete, and `MCD-RECLOSE-12` records green catalog, health, warning/audit,
example, and full-CI evidence. An explicit Kleisli category is the separate
`MCD-KLCAT-11` row and is not a prerequisite for the ambient normalizer.

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

Infinity-Codex-Decision-Responses: responses `0001` and `0003`; response
`0003` and the 2026-08-24 user clarification supersede the first checkpoint's
raw-rule rejection. This plan is authoritative.

Side-Task-Ledger: `MCD-00`, `MCD-OWNER-1`, `MCD-MONAD-2`, `MCD-KLEISLI-3`,
`MCD-OP-4`, `MCD-ADJ-5`, `MCD-CLOSE-6`, `MCD-FREE-7`, `MCD-TS-8`,
`MCD-AMBIENT-9`, `MCD-DUAL-10`, `MCD-KLCAT-11`, and `MCD-RECLOSE-12`

Baseline: clean user-authored historical checkpoint
`c1f4419ac65cbd6b68b357accea3564ed6fa21a8`

Worktree: `/home/user1/emdash1-monads-v3.2`

Branch: `goal/monad-comonad-computation-v3.2`

Git authority: the user's 2026-08-23 instruction explicitly authorizes
restoring the `main` checkout to `/home/user1/emdash1`, creating this dedicated
goal branch/worktree, starting the persistent goal, evolving this plan, and
performing the scoped implementation and validation. It does **not** authorize
commits, pushes, merges, publication, release, history rewriting, branch
deletion, or worktree removal.

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
critical-pair, subject-reduction, warning, and higher-action audits. A future
executable decision procedure for free monad syntax belongs in a separate
syntax/normalizer layer that translates both supported presentations to the
triangular normal form.

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
`kleisli_extend_func`/`kleisli_extend_fapp0` owners and an explicit equality
path to the semantic composite.

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

Its public observations are intended to be:

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
However, a transparent `cokleisli_extend_fapp0` alias does not by itself make
ordinary composition in `A` match a monadic rule indexed by `A^op`: the
canonical `Op_cat(Op_cat A) -> A` direction erases the matching head first.
`MCD-DUAL-10` must therefore select either a stable whole/point coextension
facade with explicit equality to the opposite monad, or a narrower checked
`Op` bridge. A naive underlying-Op rule with literal `D[X]`, `D[Y]`, and
`D[Z]` endpoint guards passed quietly but produced hundreds of reducible
endpoint overlaps and is rejected. The dual ambient reductions must be
computationally demonstrated, not inferred merely from the classifier alias.

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

The selected `adjunction_comonad` witness is stable. Its standard whole
counit/comultiplication compute directly to the original counit and
`F eta G`; its underlying Monad-on-opposite operations agree with the dual
adjunction operations by explicit equality evidence. Making those underlying
agreements runtime rules at a literal `Op_cat L` index added six category-head
overlaps and was rejected.

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
| `MCD-ADJ-5` | complete | `MCD-MONAD-2`, `MCD-OP-4` | Adjunction-derived monad/comonad witnesses, exact `G epsilon F` and `F eta G`, direct standard observations, and theorem-level underlying opposite-operation agreements. |
| `MCD-CLOSE-6` | historical/superseded | historical implementation rows | Green checkpoint evidence at `c1f4419`; superseded semantically by the 2026-08-24 review. |
| `MCD-FREE-7` | deferred | explicit free-syntax consumer | Separate free monad/comonad term grammar, rectangular-to-triangular translation, normalizer, and decision procedure; no global Lambdapi decidability claim. |
| `MCD-TS-8` | deferred | stable kernel API plus TypeScript consumer | Optional outer-LF declaration/compiler surface; no trusted Core macro merely to mirror the kernel relation. |
| `MCD-AMBIENT-9` | complete | historical checkpoint `c1f4419`; response `0003` | Ambient monad beta/accumulation, component and Terminal joins, positive conversion checks, transparent `KleisliCut`, and classified `Op_cat`/`EqSkeleton_cat` orders. |
| `MCD-DUAL-10` | complete | accepted `MCD-AMBIENT-9` | Stable whole/point coextension with Op equality evidence, executable ambient comonad beta/accumulation/unit/comultiplication, retained higher action, and classified dual projection orders. A broad Op runtime bridge was rejected. |
| `MCD-KLCAT-11` | deferred/separate | stable ambient calculus plus explicit consumer | Optional `Kleisli_cat(M)`, canonical functors, and composition aliases. It must not replace ambient normalization. |
| `MCD-RECLOSE-12` | complete | `MCD-AMBIENT-9`, `MCD-DUAL-10` | Checks/examples/authorities, catalog, fresh health, warning/order audits, and the full 270-file CI boundary are green. |

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
| `D-MCD-007` | refined/accepted | `Comonad_A(D) := Monad_(A^op)(D^op)` remains the evidence classifier; its ambient computational facade may require stable coextension owners because transparent Op alone does not preserve the matching head. |
| `D-MCD-008` | accepted | The four triangular laws are retained for the full monad/equality normalizer even though the identity-extension law is not needed for Cut Disintegration alone. |
| `D-MCD-009` | accepted | `A*` freeness and the decision algorithm are separate from the generic monad relation and generic Lambdapi conversion. |
| `D-MCD-010` | accepted | The first real consumer is the monad/comonad induced by the existing indexed adjunction. |
| `D-MCD-011` | accepted Git boundary | Dedicated branch/worktree and scoped edits are authorized; local commits and every remote/integration/cleanup mutation are not. |
| `D-MCD-012` | resolved | Kleisli extension needs a stable whole owner plus stable capped projection; its semantic composite is retained by equality evidence. |
| `D-MCD-013` | resolved | Comonad remains a transparent classifier alias; stable counit/comultiplication observations and direct computational views avoid double-Op runtime competition. |
| `D-MCD-014` | reversed/accepted requirement | Ambient `comp_fapp0(g*,f*) -> ...` is required. Its warning families must be classified and joined where appropriate; warning count alone is not a veto. |
| `D-MCD-015` | historical/superseded | The inferred-slot result remains useful evidence, but the primitive stable-cut rule it governed is no longer the selected owner. |
| `D-MCD-016` | accepted adjunction dual boundary | Direct full comonad observations compute for `adjunction_comonad`; underlying Monad-on-opposite agreements are equality evidence because runtime rules at literal `Op_cat L` added six overlaps. |
| `D-MCD-017` | historical closeout | Records the green `c1f4419` checkpoint; its semantic acceptance conclusion is superseded. |
| `D-MCD-018` | accepted source correction | Došen's delta/Kleisli composition and Kleisli category are separate from the ambient-composition reductions used by §5.8.3. |
| `D-MCD-019` | accepted warning policy | Critical-pair reports are classified diagnostic evidence. Preserve intended computation unless an actual cycle, subject-reduction failure, unacceptable conversion loss, or better owner is demonstrated. |
| `D-MCD-020` | accepted separation | A future explicit Kleisli category may derive `KleisliCut` from its ordinary composition and extension from its canonical right functor; it is not part of the corrective ambient tranche. |
| `D-MCD-021` | rejected bridge | A direct runtime bridge from monadic extension in `A^op` to stable coextension duplicated 19 whole/higher-action projection interactions. Retain explicit equality evidence instead. |
| `D-MCD-022` | accepted warning boundary | The corrected module reports `1135/159`: exactly monad/comonad accumulation against `Op_cat` and `EqSkeleton_cat`. Component-first and Terminal orders are joined; the four remaining category-projection reports are classified debt. |

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

## Corrective Implementation Evidence

The corrected module, central diagnostics, and reviewer example are
focused-green. The central area now contains 37 checks, and the reviewer has
12 statements. The generated catalog contains 2,244 checks across 110 mapped
areas with zero unclassified entries.

The strict module LHS audit remains empty. Warning-enabled checking reports
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

The complete reviewer-example sweep and fresh 270-file health pass are green.
The health report records source snapshot
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
claim that this generic interface constructs a free, non-idempotent model;
that stronger claim belongs only after `MCD-FREE-7` supplies explicit syntax
and a normalizer.

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
- opposite duality provides genuine comonad computations and double-opposite
  recovery;
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
- transparent Comonad introduces persistent `Op_*` endpoint brittleness;
- standard multiplication and Kleisli extension create competing runtime
  normal forms that cannot be joined narrowly;
- a candidate rule duplicates generic naturality/functoriality;
- the corrected accumulation direction creates a cycle with a semantic
  expansion or existing hom-action fold; or
- a global rewrite is justified only by the free-category metatheorem rather
  than a typed active consumer; or
- warning neutrality is obtained only by replacing ambient computation with
  a private operation head.

## Current Persistent Goal Objective

```text
Execute the evolving living plan to correct the checkpointed tranche. Make
Došen's triangular laws compute on ordinary ambient composition with the exact
orientations; replace the primitive KleisliCut substitution by ambient rules
and, at most, transparent derived notation; classify and join or explicitly
accept warning interactions under the active SOP; and provide a genuinely
computational ambient Op-dual comonad surface. Keep any explicit Kleisli
category separate from the main Došen normalizer. Evolve the plan, checks,
examples, authorities, catalog, health, and CI evidence. Preserve historical
checkpoint c1f4419 and unrelated work. Do not commit, push, merge, publish,
release, rewrite history, delete branches, or remove worktrees without
separate user authorization.
```
