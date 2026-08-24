# Emdash v3.2 Monad And Comonad Computation Plan

Date: 2026-08-23 (America/Toronto)

Plan-ID: `MONAD-COMONAD-COMPUTATION-V3.2`

Status: **completed kernel tranche; persistent-goal objective achieved
2026-08-23**. Rows `MCD-00` through `MCD-CLOSE-6` are complete. The Došen
reduction orientation is corrected, the raw-composition candidate is rejected
with measured evidence, and the selected additive module is aggregate-green
at the exact inherited warning boundary. `MCD-FREE-7` and `MCD-TS-8` remain
explicitly deferred behind their recorded consumer prerequisites.

Depends-On: active v3.2 `Adjunction`, `Op_cat`, `Op_func`, `Op_transf`,
`tapp1_func`/`tapp1_fapp0`, stable represented precomposition and
postcomposition owners, current rewrite/unification SOP, Foundations, and
canonical syntax

Supersedes: no earlier monad/comonad implementation plan. It refines the
initial 2026-08-23 review by correcting the Kleisli accumulation orientation
and then replaces its raw-composition proposal with the measured stable-cut
owner.

Infinity-Codex-Origin: session `01a02f68-6142-7e53-993a-4505aa8e2cbe`,
response `0001`

Infinity-Codex-Decision-Responses: response `0001`; the current owner probes
correct its raw rewrite realization, and this plan is authoritative.

Side-Task-Ledger: `MCD-00`, `MCD-OWNER-1`, `MCD-MONAD-2`, `MCD-KLEISLI-3`,
`MCD-OP-4`, `MCD-ADJ-5`, `MCD-CLOSE-6`, `MCD-FREE-7`, and `MCD-TS-8`

Baseline: clean `main` checkpoint
`689f41c057f5eeee5fd82486fcad79acd136bdfa`

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

The intended boundary separates three roles:

1. full functor and full transformation observations are the structural
   authority;
2. Kleisli extension plus a stable Kleisli-cut owner form the selected
   monadic runtime language; and
3. Došen's rectangular and triangular presentations are derived,
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

### Stable Kleisli cut instead of a raw composition rule

A direct generic runtime rule on base-category composition,

```text
g* o f* -> (g* o f)*,
```

passed quiet typing but added four unjoined critical pairs: opposite-category
composition, terminal composition, and equality-skeleton composition. This
is the same raw-composition failure mode rejected by earlier
profunctor-comparison work. The direct rule is not promoted.

The accepted owner is the whole `kleisli_cut_func`, with capped
`kleisli_cut_fapp0` and semantic equality
`KleisliCut(g,f)=g* o f`. The corrected hot rule is:

```text
KleisliCut(g,f*) -> (KleisliCut(g,f))*.
```

Writing its first source endpoint as inferred `_` is essential. An explicit
`T[X]` LHS slot passed quietly but created more than one hundred avoidable
object-action overlaps. With the inferred slot and the remaining audited
LHSs, the full monad plus opposite-derived comonad probe stays exactly at the
inherited `1131/159` warning boundary.

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

The co-Kleisli extension should be the endpoint-swapped view of the same
Kleisli owner, since

```text
Hom_(Op A)(X,Op(D)[Y]) = Hom_A(D(Y),X).
```

The transparent classifier is accepted and gives one law authority. Whole
coextension and co-Kleisli cut are endpoint-swapped monadic owners and remain
warning-neutral. Standard whole counit/comultiplication observations are
stable, with explicit equality paths to opposite unit/multiplication and
computational component/antecedental views. This avoids a transparent
double-`Op_transf` runtime boundary while retaining exact mathematical
duality.

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
3. Kleisli beta at the stable cut owner, with theorem-level semantic reading
   `g* o eta^c(f) = g o f`;
4. corrected stable-cut accumulation, with theorem-level semantic reading
   `g* o f* = (g* o f)*`;
5. unit-extension reduction `(eta_X)* -> 1_TX`, including both projection
   orders around `tapp1(eta,1_X) -> tapp0(eta,X)`;
6. absence of the rejected reverse accumulation;
7. an independently named same-typed unit/multiplication non-agreement;
8. a positive adjunction-derived monad instance;
9. a positive opposite-derived comonad instance;
10. double-opposite recovery and exact counit/comultiplication observations;
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
| `MCD-OWNER-1` | complete | `MCD-00` | Selected stable whole extension plus capped projection, stable whole Kleisli cut, and transparent Comonad classifier with stable standard observations; rejected broad raw composition and broad Op-involution candidates with warning evidence. |
| `MCD-MONAD-2` | complete | accepted `MCD-OWNER-1` | `emdash3_2_monads.lp` adds indexed `Monad(T)`, stable full unit/multiplication, semantic equality paths, and trust negatives. |
| `MCD-KLEISLI-3` | complete | `MCD-MONAD-2` | Whole Kleisli extension/cut, capped projections, beta, corrected owner-aligned accumulation, unit, multiplication, higher action, and raw-composition negative. |
| `MCD-OP-4` | complete | `MCD-KLEISLI-3` | Transparent Comonad classifier, stable standard observations with opposite paths, warning-neutral endpoint-swapped coextension/cut, dual beta/accumulation/unit, and retained higher action. |
| `MCD-ADJ-5` | complete | `MCD-MONAD-2`, `MCD-OP-4` | Adjunction-derived monad/comonad witnesses, exact `G epsilon F` and `F eta G`, direct standard observations, and theorem-level underlying opposite-operation agreements. |
| `MCD-CLOSE-6` | complete | accepted implementation rows | Source/check/example registration, exact warning comparison, zero LHS audit, 2,233-check catalog, fresh 270-file health evidence, aggregate CI, authority prose, and final ledger synchronization. |
| `MCD-FREE-7` | deferred | explicit free-syntax consumer | Separate free monad/comonad term grammar, rectangular-to-triangular translation, normalizer, and decision procedure; no global Lambdapi decidability claim. |
| `MCD-TS-8` | deferred | stable kernel API plus TypeScript consumer | Optional outer-LF declaration/compiler surface; no trusted Core macro merely to mirror the kernel relation. |

At most one implementation row is in progress. A rejected probe updates the
decision ledger and may split or defer its dependent row rather than forcing
the proposed signature.

## Decision Ledger

| Decision | Status | Conclusion |
| --- | --- | --- |
| `D-MCD-001` | accepted | Monad is the primary public/primitive direction; comonad is obtained through checked opposite duality. |
| `D-MCD-002` | accepted | Full endofunctor and full unit/multiplication transfors are structural authority; an object-only triangular structure is not the sole emdash core. |
| `D-MCD-003` | refined/accepted | Whole Kleisli extension and stable whole Kleisli cut are the selected runtime language; raw rectangular compositions are theorem-level views. |
| `D-MCD-004` | corrected/accepted | Runtime accumulation is `g* o f* -> (g* o f)*`. The previously proposed reverse orientation is rejected. |
| `D-MCD-005` | accepted | Generic `tapp1` naturality owns `eta^c(g) o f -> eta^c(g o f)`; do not duplicate it in the monad module. |
| `D-MCD-006` | accepted | Multiplication components compile one-way toward `(1_TX)*`; the reverse is absent. |
| `D-MCD-007` | accepted | `Comonad_A(D) := Monad_(A^op)(D^op)` is transparent; standard whole observations stay stable with explicit opposite-agreement paths. |
| `D-MCD-008` | accepted | The four triangular laws are retained for the full monad/equality normalizer even though the identity-extension law is not needed for Cut Disintegration alone. |
| `D-MCD-009` | accepted | `A*` freeness and the decision algorithm are separate from the generic monad relation and generic Lambdapi conversion. |
| `D-MCD-010` | accepted | The first real consumer is the monad/comonad induced by the existing indexed adjunction. |
| `D-MCD-011` | accepted Git boundary | Dedicated branch/worktree and scoped edits are authorized; local commits and every remote/integration/cleanup mutation are not. |
| `D-MCD-012` | resolved | Kleisli extension needs a stable whole owner plus stable capped projection; its semantic composite is retained by equality evidence. |
| `D-MCD-013` | resolved | Comonad remains a transparent classifier alias; stable counit/comultiplication observations and direct computational views avoid double-Op runtime competition. |
| `D-MCD-014` | rejected raw rule | Generic `comp_fapp0(g*,f*) -> ...` adds four unjoined specialized-category/opposite pairs; use stable `KleisliCut` instead. |
| `D-MCD-015` | accepted LHS discipline | The corrected stable-cut rule keeps its reconstructible source endpoint `_`; explicitly spelling `T[X]` created over one hundred avoidable overlaps. |
| `D-MCD-016` | accepted adjunction dual boundary | Direct full comonad observations compute for `adjunction_comonad`; underlying Monad-on-opposite agreements are equality evidence because runtime rules at literal `Op_cat L` added six overlaps. |
| `D-MCD-017` | completed closeout | The additive module remains separate from `emdash3_2.lp`; all registered source/example, catalog, health, warning, audit, and CI boundaries are green, while free syntax and TypeScript stay separately gated. |

## First Implementation Checkpoint Evidence

The accepted owner probe is `tmp/probes/monad_kleisli_cut.lp`. Its quiet and
warning-enabled dual runs are:

```text
logs/probes/monad_kleisli_cut-20260823-141458.log
logs/probes/monad_kleisli_cut-20260823-141543.log
```

The minimized precursor run at `20260823-140408` first established the exact
inherited `1131/159` warning boundary. The rejected raw-composition probe is
`tmp/probes/monad_kleisli_rules.lp`; its warning-enabled run at
`20260823-135351` measured `1135/160`, including four new unjoinable pairs.
The rejected broad opposite-involution probe in `monad_owner_types.lp`
reached `1141` unjoinable pairs and is not promoted.

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

## Final Closeout Evidence

The generated catalog records 2,233 checks in 110 areas, including 26 checks
under `Monad and comonad triangular computation`, with zero unclassified
checks. The repository warning inventory remains exactly 1,290 inherited
warnings: 1,131 unjoinable critical pairs and 159 replaceable pattern
variables. The accepted module therefore adds no warning delta.

The fresh health report records source-metrics snapshot
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

The raw-composition negative and independently named unit/multiplication
negatives are deliberately conversion-level noncollapse evidence. They do not
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

### Launch baseline evidence

Before tracked plan edits, the clean goal worktree at `689f41c` passed:

```bash
EMDASH_TYPECHECK_TIMEOUT=90s make -C emdash2 check
```

Every registered Lambdapi target completed within the uniform per-target
ceiling. The command emitted no failure. This is comparison evidence for the
untouched baseline, not permission to skip focused checks after changes.

## Acceptance And Stop Conditions

The first kernel tranche is accepted only when:

- the indexed full-functor Monad interface is stable and declaration-safe;
- Kleisli extension is whole and retains higher action;
- the exact Došen-dual reductions use the corrected orientation;
- the rejected reverse orientation remains absent;
- the selected runtime heads have no unjoined owner/projection reduction
  order;
- opposite duality provides genuine comonad computations and double-opposite
  recovery;
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
  than a typed active consumer.

## Completed Persistent Goal Objective

```text
Execute MONAD-COMONAD-COMPUTATION-V3.2 according to this living plan. First
settle the owner-position and dual-normalization questions in MCD-00 and
MCD-OWNER-1. Then implement only accepted dependency-ready rows through the
smallest coherent monad/Kleisli/opposite-comonad/adjunction tranche, retaining
whole higher action, the corrected owner-aligned
KleisliCut(g,f*) -> (KleisliCut(g,f))* orientation, the theorem-level raw
composition view, trust negatives, and proportional Lambdapi evidence. Revise
the plan when probes
reject an assumption. Keep free-syntax decidability and TypeScript surfaces
deferred unless a concrete consumer reopens them. Work only in the authorized
dedicated branch/worktree. Do not commit, push, merge, publish, release,
rewrite history, delete branches, or remove worktrees without separate user
authorization.
```
