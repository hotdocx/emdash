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

Semantic strict functors are ordinary dependent packages behind one rigid
record-like classifier head:

```text
StrictFunctor(A,B)
  := Sigma F : Functor(A,B), IsStrictFunctor(F).

strict_functor_intro(F,p) : StrictFunctor(A,B)
strict_functor_underlying(S) : Functor(A,B)
strict_functor_evidence(S) : IsStrictFunctor(underlying(S)).
```

The outer `StrictFunctor(A,B)` symbol is injective and its carrier has one
runtime rule to the exact Sigma above. This preserves rigid `(A,B)` index
inversion on rewrite LHSs; it does not introduce another code syntax or hide
different mathematical data.

One stable evidence-bearing view is permitted:

```text
strict_functor(S) : Functor(A,B).
```

At a constructor-visible package its point and hom actions expose the packaged
carrier. An opaque package returned by higher action retains the
`strict_functor(S)` head instead of losing the evidence discriminator. The old
code-specific compositor-to-identity rewrite is retired: semantic strictness
is the `IsStrictCell` evidence equating the existing compositor with
`path_to_hom` of its stored endpoint path. Reflecting that proof back into
judgmental identity computation belongs to the separately deferred global/
profile-local rewrite migration. A whole runtime fold that erases `S` before
that future computation is not required.

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
| `FPP-STRICT-SHAPE-3` | complete, awaiting checkpoint | Promoted future-proof `IsStrictCell(c) := Sigma p:x=y, c=path_to_hom(p)`, transparent `IsStrictFunctor`, the rigid exact-Sigma `StrictFunctor(A,B)` facade, constructor/projections, and constructor-visible `strict_functor` point/whole-hom/capped-arrow action. Opaque higher-produced packages retain the stable view. The old blanket compositor-to-literal-identity rule is retired rather than renamed because it is not subject-reduction sound for arbitrary semantic evidence. The focused reviewer is green; `gray_profiles` retains exactly the baseline warning inventory `1308 = 1149 critical + 159 replaceable`, with zero strict LHS-audit findings. |
| `FPP-STRICT-GRAY-4` | complete, awaiting checkpoint | `GrayHom_lax` objects are strict packages while homs remain the ambient lax/coherent `Transf_cat` tower. Identity, raw curry/uncurry plus supplied strictness, coevaluation/evaluation, transformation-graph closure, walking square and variable-dimensional cube decoding use packages without a second code grammar. Package carrier/evidence projections and retained graph/cube action are green. The graph profile remains exactly `1311 = 1152 + 159`, with unchanged critical-pair structure and zero strict LHS-audit findings. |
| `FPP-STRICT-SIMPLEX-5` | complete, awaiting checkpoint | Join inclusions/maps and selected faces pair their ordinary carriers with supplied `IsStrictFunctor` evidence. `strict_join_map` acts on the packages' actual first projections, and `selected_face_func` is that actual carrier rather than the stable Gray-profile view; this preserves all whole coface equations while keeping the evidence package available separately. Simplex shapes, tetrahedron faces, ordinal filler/successor, dimensions three/four and focused reviewers are green. The simplex owner remains exactly `1328 = 1169 + 159`, with unchanged critical-pair structure and zero strict LHS-audit findings. |
| `FPP-DOC-6` | in progress | Synchronize AGENTS, Foundations, status/SOP, canonical syntax, README, report index, predecessor plans, examples and generated catalog. Record `IsPseudoFunctor` as normal-pseudo under the present unit convention, `IsStrictFunctor` as proof-carrying code, and the global strict-rule migration as deferred. |
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
