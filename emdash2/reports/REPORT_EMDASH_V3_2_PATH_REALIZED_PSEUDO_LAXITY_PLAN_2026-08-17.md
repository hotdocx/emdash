# Emdash v3.2 Path-Realized Pseudo-Laxity Plan

Date: 2026-08-17 (America/Toronto)

Plan-ID: `PATH-REALIZED-PSEUDO-LAXITY-V3.2`

Parent-Decision-Record:
`REPORT_EMDASH_V3_2_INTERNAL_LAXITY_AND_GROUPOIDAL_REALIZATION_CONTINUATION_PLAN_2026-08-17.md`,
row `ILGR-GRPD-1`

Depends-On: active `emdash3_2.lp`; the completed generic internal-laxity
surface `functord_laxity_transf` / `fapp1_compositor`; the active
`Path_cat_func` / `path_map_func` action; the native equality-valued
groupoidality extension; the completed groupoidal closure, Circle, and
WalkingEnd comparison modules; the active Foundations, current SOP, and
canonical-syntax report

Supersedes: no completed plan. It reopens only row `ILGR-GRPD-1` of the
parent decision record with the concrete `path_map_func` consumer.

Side-Task-Ledger: `PRPL-00`, `PRPL-PATH-1A`, `PRPL-PATH-1B`,
`PRPL-PATH-1C`, conditional `PRPL-FAMILY-2A`, `PRPL-PUBLIC-3A`, and
`PRPL-CLOSE-1`

Infinity-Codex-Origin: session
`019ffe39-2eb9-7080-88e3-06b77d69b8d1`; selected continuation response
`01a0105d-05fd-7b61-a7e4-76ea3c277d8b`

Infinity-Codex-Decision-Responses: response `0037`, archived at
`/home/user1/emdash1/emdash2/tmp/ai-responses/sessions/2026-08-14_019ffe392eb9/responses/0037_2026-08-17T15-41-01Z_01a0105d-05fd-7b61-a7e4-76ea3c277d8b.md`.
Active code and SOP, then this plan and its parent decision record, outrank
the archive.

Branch-And-Worktree: `goal/groupoidal-circle-v3.2` in
`/home/user1/emdash1-groupoidal-circle-v1`

Baseline: local completed internal-laxity decision checkpoint `d90cf80`,
descended from `main` baseline `86042df`

Status: **active bounded continuation**. `PRPL-00` and `PRPL-PATH-1A` are
complete. The first import probe checks the generic compositor directly as an
equality between paths and constructs its reverse with `eq_sym`; the paired
wrong-path probe fails at the retained `q` versus `q'` endpoint as expected.
`PRPL-PATH-1B` is the selected implementation row. Later rows remain
consumer-gated and must not broaden this tranche.

## 1. Objective

Demonstrate computationally that the generic laxity already extracted from
the ordinary/displayed internal-action calculus becomes pseudofunctorial
coherence when its codomain is a path category.

The first concrete consumer is deliberately elementary. Given groupoids
`A,B`, a raw map `h : A -> B`, and composable paths

```text
p : x = y,
q : y = z,
```

the existing functor

```text
path_map_func(h) : Path_cat(A) -> Path_cat(B)
```

has the generic compositor

```text
fapp1_compositor(path_map_func(h),q,p)
  : h[q] o h[p] ==> h[q o p].
```

Because its target hom-category is itself a `Path_cat`, this directed
2-cell decodes to an equality between paths in `B`. Its reverse is therefore
obtained by ordinary path symmetry. The result should exhibit the intended
three-way reading of the shared generic cell:

```text
arbitrary directed codomain  -> potentially noninvertible laxity cell;
Path-realized codomain       -> automatically invertible pseudo cell;
selected strict profile      -> cell specialized to identity/reflexivity.
```

This plan does not introduce a second pseudofunctor classifier or a duplicate
coherence hierarchy. It tests the existing generic owner at a concrete
groupoidal codomain.

## 2. Why this row is ready now

The completed parent plan deferred `ILGR-GRPD-1` until two conditions held:

1. the generic laxity cell had a whole, iterable owner; and
2. a concrete path-valued consumer had been selected.

The first condition is now met by `functord_laxity_transf`, the ordinary
post/pre surfaces, `fapp1_compositor`, and the checked recursive second
`homd_`/Sigma action. This plan supplies the second condition by selecting
`path_map_func`, whose object, capped-arrow, and full next-hom action already
compute through `Path_cat_func`.

Computational truncation remains important but still lacks a selected first
quotient or set-truncation consumer. Gray closure has a proposed `I tensor I`
consumer but depends on a profile boundary broader than this direct
specialization. Generic groupoidification needs both a new universal-property
consumer and the later truncation/profile decisions. The present slice is
therefore the smallest high-yield continuation of the completed laxity work.

## 3. Exact mathematical and computational target

Let

```text
F := path_map_func(A,B,h).
```

The existing action computes as

```text
F[x] = h(x),
F[p] = eq_ap(h,p),
F[q] = eq_ap(h,q),
```

and its full hom action is again a `path_map_func` on the equality type.
The generic compositor has formal endpoints at the active
`functord_transport_lhs_func` and `functord_transport_rhs_func` owners. Their
readable mathematical forms are expected to compare with

```text
source(h,q,p) :=
  eq_trans(eq_ap(h,p), eq_ap(h,q)),

target(h,q,p) :=
  eq_ap(h, eq_trans(p,q)).
```

The first probe must determine the exact status of each comparison:

- definitional/runtime computation;
- proof-time comparison;
- an existing propositional bridge such as `path_comp_eq_trans` combined
  with the generic strict endpoint comparisons; or
- a genuinely missing, narrowly consumer-justified observation.

No new rewrite or unification rule is authorized merely to make the readable
formula shorter. The formal generic owners remain canonical unless the
focused consumer proves that a projection erases necessary structure.

Once the compositor is typed as a path

```text
alpha(h,q,p) : source = target,
```

its pseudo inverse is simply

```text
alpha(h,q,p)^-1 := eq_sym(alpha(h,q,p)).
```

The first acceptance boundary is the existence and typing of this reverse
path, not a new record containing inverse laws. The usual groupoid laws are
already owned by equality/path induction.

## 4. Mandatory reuse and gap audit

This matrix records the initial source scan. Exact probe results may refine
the final column, but implementation must update the matrix before promoting
any new public owner.

| Desired observation | Existing owner or evidence | Present status and decision |
| --- | --- | --- |
| Path category formation and recursive homs | `Path_cat`; `Path_cat_func` | Primitive category head plus an internal functor with computing object and next-hom action. Reuse directly. |
| Raw map acting on paths | `path_map_func`; `eq_ap` | Transparent first action of `Path_cat_func`; object, capped path, and full next-hom action are already checked. Reuse directly. |
| Path composition and HoTT transitivity | `comp_fapp0(Path_cat,...)`; `path_comp_eq_trans`; `eq_trans` | Categorical composition remains the directed owner; agreement with `eq_trans` is propositional. Do not install a reverse runtime fold. |
| Generic lax compositor | `fapp1_compositor`; `tapp1_post_laxity_cell`; `functord_laxity_transf`; `fdapp1_int_cell` | Transparent projection chain from the whole internal action. This is the sole compositor owner. |
| Formal compositor endpoints | `functord_transport_lhs_func`; `functord_transport_rhs_func`; their `*_agrees` paths | Stable whole endpoints with existing comparisons to readable strict-natural/functorial routes. Probe the exact Path specialization before adding anything. |
| Invertibility of the realized cell | `Hom_cat(Path_cat(B),...)` recursive reduction; `eq_sym` | The cell is an equality between paths, hence has a canonical reverse. No separate pseudo-inverse primitive is expected. |
| Groupoidality of literal path categories | `path_cat_is_groupoidal`; `Core_incl_func`; `path_to_hom` | Existing coherent internal groupoidality. It validates the interpretation but should not be forced into the literal equality probe if direct decoding suffices. |
| General groupoidal arrow-to-path selection | `groupoidal_arrow_to_path_func`; `groupoidal_arrow_to_path` | Available downstream for nonliteral groupoidal categories. Defer unless a later generalized consumer needs it. |
| Iterable higher action | full next-hom action of `path_map_func`; `tapp0_hom_fapp0`; existing recursive second `homd_`/Sigma probe | Whole action exists. Retain one concrete next observation; do not replace it with a capped point rule. |
| Path-valued displayed family | `path_lift_func`; `path_lift_fapp0` | Transparent semantic construction with fibre, whole transport, capped action, and retained higher projections. A readable `PathFamily_catd` alias is optional, not a prerequisite. |
| Structured transport versus primitive J | `path_cat_structured_transport`; `path_cat_ind_eqr_transport`; `path_cat_structured_transport_agrees_ind_eqr`; `path_cat_path_ind_app*` | Existing propositional comparison. Reuse if the optional family consumer is selected. |
| Dependent path versus displayed hom | `PathOver`; `SigmaPathView`; `homd_`; `homd_int` | Both orientations exist, but no general whole variance-correct equivalence is active. Keep it deferred unless the selected family consumer cannot proceed without it. |
| Concrete realized family precedent | `ProductPathFamily_catd` in `emdash3_2_groupoidal_closure.lp` | Exact `path_lift_fapp0(..., lambda z. Path_cat(P z))` pattern already exists. Prefer a transparent generalization if later needed. |
| Represented path composition | `Rep_catd_func`; `path_comp_sec`; `path_comp_func` | Useful later associator specialization, but not the simplest first consumer and not a gate for this tranche. |
| Recursive three-arrow evidence | completed no-associativity `homd_`/Sigma probe family under `tmp/probes/` | Confirms the generic tower retains the base associator and dependent filler. Reuse as evidence; do not promote a capped tetrahedron head. |
| Strict endpoint comparisons | global functoriality/naturality and associativity comparisons in `emdash3_2.lp` | Prototype infrastructure may compare endpoints, but no rule collapses `fapp1_compositor` itself. Record every actual dependency used by the Path probe. |

### Audit verdict

The initial consumer is expressible entirely from active owners. No primitive
`PseudoFunctor`, `path_map_compositor`, groupoidal compositor, or inverse-cell
record is justified before the focused probe. The likely public result, if a
name materially improves downstream use, is a transparent Path-specialized
view and its `eq_sym` reverse—not a new computation rule.

## 5. Execution ledger

| Row | Status | Deliverable and acceptance boundary |
| --- | --- | --- |
| `PRPL-00` | complete | Freeze this focused plan; link it from the parent decision record and report index; complete the initial owner-reuse/gap matrix; record branch, baseline, exclusions, and proportional validation. |
| `PRPL-PATH-1A` | complete | The ignored `path_map_pseudo_laxity.lp` probe specializes `fapp1_compositor` to `path_map_func`, types its formal codomain as equality between paths, and constructs the reverse with `eq_sym`. The paired `path_map_pseudo_laxity_wrong_path_negative.lp` fails at the retained `q` versus `q'` endpoint. No active rule or primitive was needed. |
| `PRPL-PATH-1B` | in progress | Compare the two formal endpoints with the readable `eq_ap`/`eq_trans` source and target through existing owners. Promote only transparent aliases or narrowly justified propositional observations; do not select a second runtime normal form. |
| `PRPL-PATH-1C` | pending | Retain one next-hom/higher action showing that the Path specialization remains iterable. Stop at the first useful recursive observation; no complete simplicial, pentagon, or all-coherence claim. |
| `PRPL-FAMILY-2A` | deferred | If and only if a concrete follow-on consumer needs it, expose a transparent `PathFamily_catd(P)` facade over `path_lift_fapp0` and reuse the structured-transport/right-J comparison. Do not redesign `path_lift` or force a whole `PathOver`--`homd_` equivalence. |
| `PRPL-PUBLIC-3A` | pending | Decide from probe evidence whether the result belongs as transparent names/assertions in `emdash3_2.lp`, a narrow groupoidal extension module, or documentation-only evidence. New stable heads/rules require owner-position and warning audits. |
| `PRPL-CLOSE-1` | pending | Synchronize affected checks, Foundations/SOP/canonical syntax, this ledger, report index, catalog/health only where changed, and create a reviewable local checkpoint after proportional gates. |

One row may be `in progress` at a time. A failed readable-endpoint comparison
does not authorize a broad kernel migration: record the exact stuck owner,
try the existing propositional comparison path, and either narrow the public
claim or document the missing prerequisite.

### Initial implementation evidence

The quiet positive probe completed in about two seconds. It establishes all
of the following without modifying an active source:

```text
path_map_compositor_lhs(h,q,p) : h(x) = h(z)
path_map_compositor_rhs(h,q,p) : h(x) = h(z)

path_map_compositor_path(h,q,p)
  : path_map_compositor_lhs(h,q,p)
      = path_map_compositor_rhs(h,q,p)

path_map_compositor_inverse(h,q,p)
  : path_map_compositor_rhs(h,q,p)
      = path_map_compositor_lhs(h,q,p).
```

The first path is definitionally the existing generic
`fapp1_compositor(path_map_func(h),q,p)` after recursive `Path_cat` decoding;
the inverse is definitionally `eq_sym` of that path. The negative probe asks
for the same compositor at `q` while independently indexing its right formal
endpoint by `q'`; Lambdapi leaves exactly that `q`/`q'` equality obligation
unsolved. This is the intended endpoint-rejection evidence.

The interrupted broad `make check` baseline is not closure evidence and will
not be resumed. Before it was stopped, the authoritative `emdash3_2.lp` target
completed green repeatedly; the parent checkpoint supplies the current full
170-target health snapshot. Subsequent implementation uses focused probes and
affected targets only.

## 6. Focused implementation sequence

### Phase A — formal Path decoding

Create an ignored import probe that:

1. instantiates `fapp1_compositor` at
   `path_map_func A B h` and paths `p,q`;
2. types the result directly as an equality between its two formal path
   endpoints;
3. constructs the reversed equality with `eq_sym`; and
4. includes a nearby wrong-endpoint negative probe.

This phase establishes the central pseudo-laxity claim independently of any
pretty endpoint theorem.

### Phase B — readable endpoint comparison

Unfold only the public transparent aliases and inspect both formal endpoints.
Attempt to assemble comparisons from:

- the object and capped action of `path_map_func`;
- generic whole strict functoriality/naturality comparisons;
- `path_comp_eq_trans`; and
- ordinary equality congruence/transitivity.

If the formal endpoints already convert, retain assertions rather than adding
a named theorem. If they agree only propositionally and a downstream consumer
needs the readable form, add one transparent theorem assembled from existing
paths. Do not orient it as a runtime rewrite.

### Phase C — one recursive observation

Inspect the next hom action of the Path-valued compositor or the nearest whole
owner that contains it. The acceptance test is that the result remains
available through generic `fapp*`/`tapp*` or `homd_` action, not that every
boundary face is projected or that a classical pentagon is reconstructed.

### Phase D — conditional family facade

Only after Phases A--C identify a concrete need, test the transparent alias

```text
PathFamily_catd(P)
  := path_lift_fapp0
       A Cat_cat
       (lambda x. Path_cat(P(x))).
```

The probe must cover the fibre, whole transport functor, capped action, and
one retained higher action. Existing `ProductPathFamily_catd` and structured
transport/J comparisons are the reference implementation. If any projection
stalls, first locate the missing existing `path_lift` projection; do not make
`piapp*`, `path_lift`, or a displayed hom primitive solely for readability.

## 7. Acceptance boundary

The bounded goal is complete when all of the following hold:

1. the generic compositor of `path_map_func` is checked as an equality
   between paths at its formal endpoints;
2. its canonical reverse is checked through `eq_sym`, making the pseudo
   interpretation computationally explicit;
3. the relationship to the readable `eq_ap`/`eq_trans` endpoints is recorded
   at its actual definitional/proof-time/propositional strength;
4. one higher/whole observation confirms that the specialization was not
   capped before iteration;
5. positive and negative focused probes distinguish the intended endpoints;
6. no duplicate pseudofunctor hierarchy, compositor rule, or inverse record
   has been introduced;
7. any promoted source surface has focused diagnostics and proportional SOP
   evidence; and
8. this ledger and affected architecture documents describe exactly what is
   computational, proof-time, propositional, or deferred.

If Phase A shows that the entire result is already a direct typing consequence
of active owners, a documentation-and-checks-only implementation is a valid
and desirable completion. Code volume is not an acceptance criterion.

## 8. Explicit exclusions and stop conditions

This goal does **not** include:

- a complete simplicial object, face/degeneracy API, nerve, Segal theorem,
  pentagon suite, or all-dimensional coherence theorem;
- a generic `PathOver`--`homd_` whole equivalence without a selected consumer;
- a Gray or Crans--Gray tensor, strict-object/lax-arrow profile migration, or
  `I tensor I` interchanger;
- a computational truncation reflector or sorted universe of `n`-types;
- a generic groupoidification reflector or adjunction;
- global relocation/removal of the prototype's strict functoriality,
  naturality, or associativity comparisons;
- changes to Circle, WalkingEnd, schemes, or unrelated mathematical modules;
- book/article expansion, npm publication, browser deployment, or sibling
  repository work; or
- push, merge, rebase, amend, reset, release, publication, branch/worktree
  deletion, or other external Git mutation.

Stop and update the plan rather than broadening the implementation if:

- the first Path specialization requires changing the generic compositor
  owner;
- a proposed rule cannot be validated at its intended owner position;
- an endpoint comparison depends circularly on the result being claimed;
- a warning or subject-reduction delta cannot be localized;
- the higher observation requires a new complete coherence framework; or
- the optional family alias would force a redesign of `path_lift` or `piapp*`.

## 9. Validation and checkpoint policy

Use the smallest gate that owns each change:

- `scripts/probe.sh tmp/probes/<name>.lp` for the import consumer;
- a full-file owner-position probe only if a new rule or stable head is
  proposed;
- warning comparison and strict LHS audit only for a promoted rule/head;
- the affected kernel/module and central diagnostics after source promotion;
- affected reviewer examples only if the public reviewer surface changes;
- catalog refresh only when registered assertions or areas change;
- health refresh only when maintained source/example content changes enough
  to stale its snapshot; and
- lightweight report reference, heading, TOC, and exact-diff checks for
  documentation-only edits.

Do not rerun `make check`, `make examples`, `make ci`, `check:all`, or another
long aggregate merely for reassurance. The completed parent checkpoint carries
current 170-target health evidence; this plan should carry that evidence
forward until a changed cross-module boundary makes an aggregate genuinely
necessary.

Local checkpoint commits are permitted only after a bounded row is green,
the ledger is synchronized, and the exact staged diff is reviewed. This plan
does not authorize push, merge, publication, history rewriting, or worktree
cleanup.
