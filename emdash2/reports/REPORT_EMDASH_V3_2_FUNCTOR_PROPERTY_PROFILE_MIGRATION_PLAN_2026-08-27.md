# Emdash v3.2 Functor Property-Profile Migration Plan

Date: 2026-08-27 (America/Toronto)

Plan-ID: `FUNCTOR-PROPERTY-PROFILES-V3.2`

Status: **active implementation plan**.

Branch: `goal/functor-property-profiles-v3.2`

Worktree: `/home/user1/emdash1-functor-property-profiles-v1`

Baseline: `1dce023` (`close omega pseudo profile correction`).

Depends-On:
`REPORT_EMDASH_V3_2_INTRINSIC_FUNCTOR_PROFILES_AND_GRAY_GRAPH_REDESIGN_PLAN_2026-08-26.md`,
`emdash3_2_gray_profiles.lp`, `emdash3_2_readable_pseudofunctors.lp`, and
their active Gray, cubical, and ordinal-simplex consumers.

Authority chain: active `emdash3_2*.lp` source; `emdash2/AGENTS.md`;
`EMDASH_FOUNDATIONS.md`; current status/SOP and canonical syntax; this living
plan; linked decision responses; raw archive.

Infinity-Codex-Origin: session
`019ffe39-2eb9-7080-88e3-06b77d69b8d1`, response
`0151_2026-08-27T08-31-25Z_01a04256-5135-7ec3-bd6a-56e85e7dc463.md`.

Infinity-Codex-Decision-Response:
`infinity-codex:019ffe39-2eb9-7080-88e3-06b77d69b8d1:01a04256-5135-7ec3-bd6a-56e85e7dc463`.

Side-Task-Ledger: `FPP-00`, `FPP-AUDIT-1`, `FPP-PSEUDO-2`,
`FPP-STRICT-SHAPE-3`, `FPP-STRICT-GRAY-4`, `FPP-STRICT-SIMPLEX-5`,
`FPP-DOC-6`, and `FPP-CLOSE-7`.

## 1. Objective

Replace two temporary classifier/code facades by properties of already-formed
ambient functors:

1. replace `ReadablePseudoFunctorProfile(F)` by `IsPseudoFunctor(F)`, whose
   field is fixed-forward `OmegaEquivAlong` for the existing readable
   compositor;
2. replace primitive `StrictFunctorData(A,B)` codes by the semantic package
   `Sigma F : Functor(A,B), IsStrictFunctor(F)`;
3. retain one evidence-bearing stable view `strict_functor(F,p)` so selected
   strict computations can see the certificate without a second code grammar;
4. migrate Gray closure/cubes and ordinal-simplex consumers to those packages;
5. preserve whole and iterated action; and
6. leave the generic global strict functoriality/naturality rewrite migration
   to a separate later goal.

## 2. Governing Invariants

> A property constrains coherence already extracted from internal action. It
> never supplies a parallel compositor, unitor, naturality square, or higher
> coherence cell.

> `IsStrictFunctor` evidence is the proof-carrying code. No permanent
> `StrictFunctorCode`/`StrictFunctorData` syntax exists beside it.

> Computational strictness may use a stable evidence-bearing inclusion/view,
> but that view is not another mathematical functor object or code universe.

The global strict cuts remain temporarily active. They may create documented
prototype overlaps, but this plan neither moves nor deletes them and does not
claim noncollapsed generic lax endpoints.

## 3. Pseudo Property

Under the current normal-lax identity convention:

```text
IsPseudoFunctor(F)
  := Pi X Y Z g f,
       OmegaEquivAlong(
         Hom_cat(B,F[X],F[Z]),
         readable_pseudo_post_cell(F,g,f)).
```

The property is fixed-forward: its indexed arrow is exactly the readable
reframe of `fapp1_compositor`. The current endpoint ladder remains the
documented strict-prototype adapter selected in the predecessor plan.

Rename supplied closure capabilities by mathematical content:

```text
identity_is_pseudo
comp_is_pseudo
cubical_src_is_pseudo
cubical_tgt_is_pseudo
cubical_arrow_is_pseudo.
```

They may remain opaque until their existing extracted unit/composite
prerequisites are implemented. Their opacity never permits an independent
forward cell because `IsPseudoFunctor` fixes that cell in its result type.

## 4. Strict Property And Package

The future-proof fixed-cell property uses an explicit endpoint path rather
than relying on the temporary global endpoint collapse:

```text
IsStrictCell_C(c : Hom_C(x,y))
  := Sigma p : x = y,
       c = path_to_hom(p).

IsStrictFunctor(F)
  := Pi X Y Z g f,
       IsStrictCell(
         fapp1_compositor(F,g,f)).
```

The ambient calculus is presently normal-lax, so unit preservation remains
judgmental and no independent unitor field is added. If a future fully lax
unit interface is introduced, strict-unit evidence must extend this property
in that later plan.

Semantic strict functors are ordinary dependent packages:

```text
StrictFunctor(A,B)
  := Sigma F : Functor(A,B), IsStrictFunctor(F).

strict_functor_intro(F,p) : StrictFunctor(A,B)
strict_functor_underlying(S) : Functor(A,B)
strict_functor_evidence(S) : IsStrictFunctor(underlying(S)).
```

One stable evidence-bearing view is permitted:

```text
strict_functor(S) : Functor(A,B).
```

Its point and hom actions expose `strict_functor_underlying(S)`. The existing
selected compositor-to-identity computation moves from
`strict_functor_carrier(oldCode)` to this package-indexed head. A whole
runtime fold that erases `S` before profile-local computation is not required.

## 5. Gray Category And Hom Profile

`GrayHom_lax(A,B)` remains the explicitly named strict-object/lax-arrow
profile:

```text
Obj(GrayHom_lax(A,B)) = StrictFunctor(A,B)

Hom_Gray(S,T)
  = Transf_cat(strict_functor(S),strict_functor(T)).
```

Its inclusion into ambient `Functor_cat(A,B)` is the whole owner of
`strict_functor`. This plan does not define the distinct category of strict
functors with strict transformations.

Current code constructors become ordinary package/evidence producers:

```text
strict_identity
strict_join_fst
strict_join_snd
strict_join_map
strict_gray_transf_graph
strict gray curry/uncurry observations.
```

Opaque `IsStrictFunctor` evidence is allowed as a clearly named temporary
capability. Later derivation may replace it without changing the package or
consumer types.

## 6. Explicitly Deferred Global Rule Migration

This plan does not alter the generic rules

```text
F[id] --> id
F[g] o F[f] --> F[g o f]
```

or their whole/component naturality and displayed analogues. A later plan will
move functoriality rules to `strict_functor(F,p)`, transformation naturality
rules to an evidence-bearing `strict_transfor(epsilon,q)`, and displayed rules
to their corresponding profile. Merely migrating functor objects is not a
substitute for that separate transformation-profile work.

## 7. Execution Ledger

| Row | State | Deliverable and acceptance boundary |
| --- | --- | --- |
| `FPP-00` | complete | Created `/home/user1/emdash1-functor-property-profiles-v1` on `goal/functor-property-profiles-v3.2` from clean validated baseline `1dce023`; bootstrapped its own pnpm link graph. No push, merge, publication, history rewrite, or cleanup is authorized. |
| `FPP-AUDIT-1` | complete | Exact lexical scope is nine pseudo-profile source/reviewer files and twenty strict-code source/reviewer files. The pseudo migration is a property/name change. The strict migration changes primitive codes into Sigma packages and must retain an evidence-bearing stable carrier view; it does not move global strict rules. |
| `FPP-PSEUDO-2` | complete, checkpoint `5d835b8` | `IsPseudoFunctor` is the transparent dependent product of fixed-forward `OmegaEquivAlong` evidence. The abstract profile wrapper and constructor/projection rule are removed; five supplied closure proofs and all cubical, square, recursive face-action and frame consumers use the property directly. Focused sources/reviewers are green; warning inventories remain exactly `1308 = 1149 critical + 159 replaceable`, strict LHS audits report zero candidates, and catalog/TOC/diff hygiene pass. Authority prose is consolidated in `FPP-DOC-6`. |
| `FPP-STRICT-SHAPE-3` | pending | Probe and promote `IsStrictCell`, `IsStrictFunctor`, transparent `StrictFunctor` package observations, and the stable `strict_functor` view. Preserve point/arrow action, exact intrinsic compositor ownership, selected strict identity computation, next action, subject reduction, warning inventory, and zero unreviewed LHS candidates. |
| `FPP-STRICT-GRAY-4` | pending | Change `GrayHom_lax` objects to strict packages; migrate identity, curry/uncurry, transformation graph, walking-square, Gray cube recursion/decoder, and focused reviewers. Retain strict-object/lax-arrow homs and whole inclusion action. |
| `FPP-STRICT-SIMPLEX-5` | pending | Replace strict join and identity codes in simplex shapes, tetrahedron faces, ordinal fillers/successors and their focused reviewers by ordinary functors paired with supplied/derived `IsStrictFunctor` evidence. Preserve all visible face and retained next-action computations. |
| `FPP-DOC-6` | pending | Synchronize AGENTS, Foundations, status/SOP, canonical syntax, README, report index, predecessor plans, examples and generated catalog. Record `IsPseudoFunctor` as normal-pseudo under the present unit convention, `IsStrictFunctor` as proof-carrying code, and the global strict-rule migration as deferred. |
| `FPP-CLOSE-7` | pending | Require focused sources/reviewers, exact warning and LHS audits, catalog/TOC/diff hygiene, and a clean checkpoint chain. Eagerly avoid long registered-source, examples, health and repository aggregates unless omission blocks classification. Complete only after no active source/reviewer uses `ReadablePseudoFunctorProfile`, `StrictFunctorData`, or `strict_functor_carrier`. |

## 8. Validation Policy

- Keep every Lambdapi invocation within 90 seconds.
- Use focused source/reviewer checks and owner-position probes.
- Compare exact warnings for any rule-bearing owner; warnings diagnose rather
  than automatically veto intended profile computation.
- Run strict LHS audits for every edited rule-bearing source.
- Regenerate/check the assertion catalog after reviewer changes.
- Run source TOC and exact diff hygiene.
- Avoid long aggregates unless their omission blocks a specific classification.

## 9. Git Policy

The user authorizes SOP-compliant local checkpoint commits on this dedicated
branch after bounded green tranches and synchronized ledger updates. Preserve
unrelated work and stage only owned paths.

Do not push, merge, publish, tag, create a PR, amend, rebase, reset, rewrite
history, delete branches, or remove worktrees without separate authorization.

## 10. Persistent-Goal Launch Prompt

> Continue the emdash v3.2 functor property-profile migration in
> `/home/user1/emdash1-functor-property-profiles-v1` on branch
> `goal/functor-property-profiles-v3.2`, delegating exact design, sequencing,
> acceptance, exclusions, proportional validation, documentation and Git
> discipline to
> `emdash2/reports/REPORT_EMDASH_V3_2_FUNCTOR_PROPERTY_PROFILE_MIGRATION_PLAN_2026-08-27.md`
> and its authority chain. Begin at `1dce023`. Replace
> `ReadablePseudoFunctorProfile` by fixed-forward `IsPseudoFunctor`; replace
> primitive `StrictFunctorData` codes by Sigma-packaged `IsStrictFunctor`
> evidence and one evidence-bearing stable `strict_functor` view; preserve
> intrinsic compositor ownership, whole/iterated action, Gray
> strict-object/lax-arrow semantics, cubical recursion and ordinal-simplex
> computations. Opaque closure evidence is allowed only when named honestly.
> Do not migrate the generic global strict functoriality, transformation
> naturality, or displayed strictness rules in this goal. Keep Lambdapi
> commands within 90 seconds, eagerly avoid long aggregates unless omission
> blocks classification, and use authorized bounded local checkpoints after
> green tranches and ledger synchronization. Do not push, merge, publish, tag,
> create a PR, rewrite history, delete branches, or remove worktrees.
