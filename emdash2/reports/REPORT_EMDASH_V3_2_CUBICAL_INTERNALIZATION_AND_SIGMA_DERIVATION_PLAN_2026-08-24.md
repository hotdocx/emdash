# Emdash v3.2 Cubical Internalization And Sigma Derivation Plan

Date: 2026-08-24 (America/Toronto)

Plan-ID: `CUBICAL-INTERNALIZATION-SIGMA-DERIVATION-V3.2`

Status: **completed corrective implementation plan**.

Supersedes: no completed plan. It corrects the foundational interpretation of
the completed intrinsic-semicubical prototype while preserving its evidence.

Corrects: the foundational-completion interpretation of
`REPORT_EMDASH_V3_2_CUBICAL_ARROW_AND_SEMICUBICAL_CODES_PLAN_2026-08-23.md`.
That plan remains implementation evidence for the square orientation,
`{L,R,*}` code grammar, variable-dimensional action, and recursive frame; it
does not establish the generic `homdc_int` or a Sigma-derived lax-arrow
category.

Depends-On: `emdash3_2.lp`, especially `hom_int`, `hom_con_int`, `homd_`,
`homd_int`, `CommaFib_catd`, `SelfComma_catd`, `Sigma_cat`, `Sigma_func`,
`FibrewiseSigma_catd`, and the whole internal-action calculus; the completed
cubical dependent-hom and intrinsic semicubical branches through checkpoint
`bfd5f05630f22f8deecce657789cfc331b5feb0e`; and the current Foundations,
canonical syntax, SOP, report index, and persistent-goal Git workflow.

Side-Task-Ledger: `CINT-00`, `CINT-AUDIT-1`, `CINT-COMMA-2`,
`CINT-HOMDC-DESIGN-3`, `CINT-HOMDC-4`, `CINT-TOTAL-5`, `CINT-LAXARROW-6`,
`CINT-MIGRATE-7`, `CINT-VARDIM-8`, `CINT-ADEQUACY-9`, `CINT-FACADE-10`,
`CINT-DOC-11`, and `CINT-CLOSE-12`.

Infinity-Codex-Origin: session
`019ffe39-2eb9-7080-88e3-06b77d69b8d1`; decisive corrective response
`0126_2026-08-24T06-43-31Z_01a0327f-7b41-7913-81fa-1242bf0c6d45.md`.

Infinity-Codex-Decision-Responses: `infinity-codex:019ffe39-2eb9-7080-88e3-06b77d69b8d1:01a0327f-7b41-7913-81fa-1242bf0c6d45`.

Branch: `goal/cubical-internalization-v3.2`

Worktree: `/home/user1/emdash1-cubical-internalization-v1`

Baseline: completed experimental intrinsic-semicubical checkpoint
`bfd5f05630f22f8deecce657789cfc331b5feb0e`.

Active code, this plan, and measured probes outrank archived conversation.

Semantic-Adequacy-Continuation:
`REPORT_EMDASH_V3_2_CUBICAL_YONEDA_AND_GRAY_CUBE_ADEQUACY_PLAN_2026-08-25.md`.
That plan packages the representable/Yoneda object maps and then compares the
native levels with literature-standard Gray tensor powers of the walking
arrow, after an explicit lax/oplax orientation audit.

## 1. Corrective Objective

Restore the same foundations-first architecture that governs the simplicial
development:

```text
internal hom owner
  -> variance-correct displayed/comma family
    -> existing Sigma totalization
      -> recursively iterable shapes.
```

For cubical structure, the foundational owner is `homdc_int`. Focused probes
have now shown that it need not be a new primitive: the variance-correct owner
is a transparent specialization of the existing `homd_int` after one inner
Sigma total and one pointwise opposite. A shape-specific primitive
`CubicalArrow_cat` is not the desired foundation. The target dependency path
is:

```text
Sigma_cat / Op_catd / homd_int
  -> homdc_int
  -> homdc_ and its fixed fibres
    -> variance-correct comma/two-sided family
      -> existing Sigma_cat / FibrewiseSigma_catd
        -> LaxArrow_cat(C)
          -> CubicalLevel(C,n)
            -> existing CubeFaceCode action and semicubical nerve.
```

The completed branch demonstrated that the final three layers are feasible.
This plan must derive their category-theoretic foundation rather than retain an
independent primitive arrow category and opaque whole-nerve packaging.

## 2. Variance Settlement

Let

```text
E : K1^op -> Catd(K2).
```

For endpoint objects

```text
u : E[x1][x2]
v : E[y1][y2]
```

and forward side arrows

```text
a : Hom_K1(x1,y1)
b : Hom_K2(x2,y2),
```

the selected square filler is

```text
Hom_{E[x1][y2]}
  (E[x1][b](u), E[a^op][y2](v)).
```

This formula already solves the mixed-variance problem locally. Its whole
internalization must solve the same problem before any total category is
formed.

Raw uncurrying alone gives

```text
uncurry(E) : K1^op * K2 -> Cat.
```

Applying ordinary `Sigma_cat` directly to that family produces a category of
elements whose first base arrow is reversed. For `E = hom_int(id_C)`, this is
twisted-arrow-shaped and is not automatically the desired forward lax-arrow
category. Therefore this plan must not define `TwoSidedSigma(E)` merely as an
opaque name for `Sigma(uncurry(E))` and then claim the variance is solved.

The correct uncurrying is comma/two-sided: source transport uses `b`, target
transport uses `a^op`, and the final hom is formed in the cross fibre. This is
the role of `homdc_int`.

## 3. Derived `homdc_int` Boundary

The owner-position probe selected the following transparent construction. For

```text
E : K1^op -> Catd(K2),
```

define the inner edge family and its pointwise opposite by

```text
EdgeFamily_E(x1) := Sigma_cat K2 (E[x1])
D_E              := Op_catd(EdgeFamily_E).
```

Thus an object of `EdgeFamily_E(x1)` is `(x2,u)`. The mixed-variance owner is

```text
homdc_int(E) := homd_int(id_D_E)

  : Functord(EdgeFamily_E,Homd_target_catd(D_E))
```

over the base `K1^op`. The pointwise opposite is essential:
`Op_catd(D_E)` reduces back to `EdgeFamily_E`, while the endpoint Hom in
`D_E` reverses once more to the selected forward lax cell.

Variance forces the canonical projection order to be target edge first:

```text
target K1 endpoint y1
  -> target edge (y2,v)
    -> source K1 endpoint x1
      -> source edge (x2,u)
        -> side arrow a : x1 -> y1
          -> category of pairs (b,alpha).
```

The final category is

```text
homdc_int(E)
  [y1][(y2,v)][x1][(x2,u)][a]
    = Hom_{EdgeFamily_E(x1)}
        ((x2,u),EdgeFamily_E[a^op](y2,v)).
```

Generic Sigma-Hom computation then exposes its objects as

```text
(b,alpha),

b     : Hom_K2(x2,y2),
alpha : Hom_{E[x1][y2]}
          (E[x1][b](u),E[a^op][y2](v)).
```

This is the earlier source-first schematic telescope, but expressed in the
only projection order that preserves its mixed variance as one existing whole
internal action. It neither flattens the endpoints into a product nor invents
a new record.

The focused probe also establishes

```text
homdc_int(E)[...][a]
  = Op_cat(homdc_inner_total_func(E,...)[a])
```

definitionally. Hence the current fixed-endpoint theory is recovered with the
precise pointwise opposite required by the canonical target-first owner; it is
not a competing primitive.

Acceptance requires:

1. `homdc_int` is the transparent `homd_int(id_D_E)` construction above;
2. fixing endpoints and `a` recovers the pointwise opposite of the existing
   `homdc_inner_total_func`, while its Sigma object projection recovers
   `homdc_` and `homdc_fibre`;
3. fixing `a` exposes the expected `homd_int`-shaped slice without a new
   parameter-action primitive;
4. each remaining endpoint/side parameter retains its next hom action;
5. the `hom_int(id_C)` instance computes to
   `Hom_{Hom_C(x1,y2)}(b o u,v o a)`;
6. the opposite/twisted orientation remains distinct.

The former proposed prerequisite `homd_parameter_func` is therefore not a
foundational blocker. If later consumers need the independent assignment
`FF |-> homd_int(FF)`, it remains a derived comparison/API task rather than the
source of cubical structure.

## 4. Sigma-First Totalization Policy

No independent primitive `TwoSidedSigma_cat` is planned initially.

The exact variance-correct total selected by the probe is

```text
TwoSidedSigma_cat(E)
  := Op_cat(
       Sigma_cat (Op_cat K1)
         (Op_catd(EdgeFamily_E))).
```

Its objects compute to `(x1,(x2,u))`. A Hom from `(x1,(x2,u))` to
`(y1,(y2,v))` is generated by the same `homd_int(id_D_E)` endpoint used above,
so a visible object computes to `(a,(b,alpha))` in the selected lax direction.
This formula is nested ordinary Sigma plus two semantically required opposite
placements; it is not a second total-category theory.

For visible endpoint objects, the desired Hom is already an iterated ordinary
Sigma:

```text
Hom((x1,x2,u),(y1,y2,v))
  = Sigma(a : Hom_K1(x1,y1)),
    Sigma(b : Hom_K2(x2,y2)),
      homdc_int(E)[x1,x2,u,y1,y2,v,a,b].
```

The implementation should build the necessary displayed/comma family and then
reuse:

- `Sigma_cat` for total categories and Hom-Sigma computation;
- `Sigma_func` and `sigma_map_func` for whole maps;
- `Sigma_proj1_func` for endpoint/face projections;
- `FibrewiseSigma_catd` for nested displayed totals;
- existing Sigma identity/composition and higher hom action.

If consumer measurements later require a stable `TwoSidedSigma_cat(E)` head,
it may be introduced only as a facade over that derived Sigma expression. Its
objects, Homs, identities, composition, maps, and projections must delegate to
the existing owners; it must not create a second independent category theory.

## 5. Specialized Comma-Total Candidate

The current kernel already derives conventional comma fibres:

```text
CommaFib_catd(T) : Catd(B)
CommaFib_catd(T)[y] = (T downarrow y).
```

The first mandatory probe was

```text
LaxArrowCandidate(C)
  := Sigma_cat C (CommaFib_catd(id_C)).
```

Objects should compute, up to tuple order, to

```text
(y,(x,u : Hom_C(x,y))).
```

Here the outer `Sigma` coordinate `y` is the target of the represented edge,
whereas the comma-fibre coordinate `x` is its source.  The provisional
`CubicalArrow_cat` stores the same visible data in the opposite tuple order,
`(x,(y,u))`.  Reassociating or swapping a dependent package is harmless only
when the corresponding whole source and target projection functors, their hom
actions, and the square orientation are transported with it.  The probe must
therefore distinguish an exact computational presentation from a merely
equivalent presentation whose horizontal/vertical roles have been exchanged.

For two visible arrows `u:x1->x2` and `v:y1->y2`, its Hom must be inspected
without adding a bridge. The selected successful orientation is

```text
Sigma(a : Hom_C(x1,y1)),
Sigma(b : Hom_C(x2,y2)),
  Hom_{Hom_C(x1,y2)}(b o u,v o a).
```

The probe classifies the existing comma total as the **oplax** presentation:

```text
alpha : v o a ==> b o u.
```

Its outer Sigma projection computes to the target endpoint and to side `b` on
visible arrows. It is therefore useful semantic/opposite evidence but is not
the selected computational lax-arrow owner. In the original three-way audit,
the possible verdicts were:

- exactly this lax orientation;
- the opposite/oplax orientation, correctable transparently by existing `Op`
  owners; or
- a genuinely different twisted-arrow construction.

Its verdict has three strengths:

1. **definitional owner:** visible objects, source/target projections, square
   coordinates, and their next actions reduce in the selected orientation;
2. **typed equivalent presentation:** an explicit whole reordering/opposite
   functor is required, so the comma total can justify semantics but is not
   itself the final computational owner; or
3. **wrong construction:** it has the twisted or role-swapped variance and
   cannot serve as the lax-arrow total.

Only the first verdict would have permitted the literal definition
`LaxArrow_cat(C) := Sigma_cat C (CommaFib_catd(id_C))`.  The second and third
verdicts require the total derived from `homdc_int`; they must not be repaired
by an endpoint-specific rewrite.

It must also inspect identity, pasting, source/target projections, and one next
hom action. No new rule or category head may be added merely to make the first
probe pass.

## 6. Lax Arrow And Migration Policy

The mathematical constructor should be named by what it is:

```text
LaxArrow_cat(C).
```

Preferred definitions, in order, are:

```text
LaxArrow_cat(C)
  := TwoSidedSigma_cat(hom_int(id_C)).
```

The rejected literal comma definition remains a negative/orientation check.
`homdc_int` is the internal action used by the generic Hom rule of this
two-sided total, so the public arrow category follows from the self-contained
internal-hom/Sigma theory rather than from a coincidental pre-existing comma.

Only after the derived source is green may

```text
CubicalArrow_cat(C)
```

remain as a transparent readability alias or be retired. The current primitive
head, its rules, examples, and checkpoints must remain intact until the
replacement has:

1. matching visible objects and lax-square Homs;
2. matching source/target object and arrow action;
3. matching identity and square pasting;
4. profile-aware functorial lifting;
5. a retained next hom action;
6. explicit noncollapse from the opposite/twisted orientation.

No destructive rewrite of the completed branch is permitted. Migration uses
new modules and correcting commits; deletion is the final consequence of a
green comparison, not the starting tactic.

## 7. Arbitrary Dimension And Combinatorial Adequacy

The existing internal data remain valuable:

```text
CubicalLevel(C,0)       = C
CubicalLevel(C,n+1)     = current CubicalArrow(CubicalLevel(C,n))
CubeFaceCode(p,n)       = set-classified {L,R,*} words
cube_face_action_func   = variable-dimensional restriction
SemiCubePlus_cat        = internal augmented semicube category.
```

After `LaxArrow_cat` is derived, these definitions must be retargeted—not
recreated dimension by dimension—and revalidated at arbitrary `n,p`.

The adequacy boundary has two strengths:

### 7.1 Required semicubical adequacy

- every `CubeFaceCode(p,n)` acts on the derived levels;
- identity and structural substitution agree as whole paths;
- the recursive `2n` immediate boundary uses new source/target plus star-lifted
  older faces;
- dimensions one through three recover edges, four-edge squares, and six-face
  cubes from the derived total;
- another hom action remains available.

### 7.2 Selected representable comparison

Use the existing Yoneda/presheaf infrastructure to define the standard
representable semicube at `n` over `SemiCubePlus_cat`. Establish a selected
comparison between its face combinatorics and the native boundary action. A
global theorem identifying every semicubical set with a native nerve is not
required.

Comparison with `GrayHom_lax(WalkingArrow,C)` or Gray tensor powers is a later
semantic certification once the Sigma-derived construction is stable. It must
not define the foundation.

## 8. Explicit Nonclaims

This corrective goal does not initially claim:

- a complete cubical type theory;
- degeneracies, connections, reversals, coordinate permutations, or Kan
  filling;
- equivalence of every semicubical diagram with the nerve of one category;
- a full Crans--Gray monoidal theory;
- removal of all historical strict endpoint cuts;
- automatic positivity/productivity checking;
- global normalization, confluence, canonicity, or consistency.

Those exclusions do not weaken the required generic `homdc_int`, Sigma-derived
lax-arrow category, or arbitrary-dimensional semicubical face action.

## 9. Execution Ledger

| Row | State | Deliverable and acceptance boundary |
| --- | --- | --- |
| `CINT-00` | complete | Created `goal/cubical-internalization-v3.2` at exact baseline `bfd5f05` in `/home/user1/emdash1-cubical-internalization-v1`; bootstrapped its own pnpm link graph; promoted this corrective plan and cross-linked both parent plans; the deepest unchanged semicubical source checks green under 90 seconds; selected focused validation and safe migration policy. |
| `CINT-AUDIT-1` | complete | Audited the completed branch against the parent plan and decision response. Confirmed that arbitrary-`n` codes/action are real, while generic `homdc_int`, Sigma derivation, full combinatorial adequacy, and a constructed whole nerve remain absent. Classified primitive `CubicalArrow_cat` as a useful lax-arrow prototype rather than the definitive foundation. |
| `CINT-COMMA-2` | complete | The typed owner probe shows `Sigma_cat C (CommaFib_catd(id_C))` stores edges as `(target,(source,u))`, projects target/`b`, and selects the oplax cell `v o a ==> b o u`. It is not the selected lax owner and no bridge, rule, unifier, or category head was added. Generic Sigma owns its identity/composition/higher action. |
| `CINT-HOMDC-DESIGN-3` | complete | Selected `EdgeFamily_E := Sigma_func(K2) o E`, `D_E := Op_catd(EdgeFamily_E)`, and transparent `homdc_int(E) := homd_int(id_D_E)` over `K1^op`. Its canonical target-edge-first projection at `a` is definitionally the pointwise opposite of the existing fixed-endpoint inner total, and a typed constructor exposes `(b,alpha)` in the selected lax direction. The former `homd_parameter_func` is not a prerequisite. |
| `CINT-HOMDC-4` | complete | `emdash3_2_cubical_internalization.lp` implements transparent `homdc_int := homd_int(id_D_E)` and its fixed-`a` projection `homdc_at`. The reviewer checks the exact pointwise-opposite relation to the earlier inner total, the generic `(b,alpha)` cross-fibre square, both whole endpoint actions, identity boundaries, composite boundaries, and retained Hom action. The oplax comma probe supplies the opposite noncollapse. No new internal-hom primitive, square, unifier, or dimension-specific rule was added. |
| `CINT-TOTAL-5` | complete | The transparent `homdc_total_cat := Op_cat(Sigma_cat(Op K1,D_E))` has visible `(x1,(x2,u))` objects and `(a,(b,alpha))` arrows in the selected lax direction. Derived source and target endpoint functors compute on objects and visible square arrows to `a` and `b`. The missing `b` reading was traced to generic `sigma_proj1_family_funcd`; two owner-position rules now give its constructor-visible action and pointwise-opposite specialization with no cubical endpoint/dimension. Generic category identity and composition retain the expected endpoint identities/composites and another Hom action. Their full nested constructor terms deliberately remain at canonical Sigma/internal-action owners rather than folding to the provisional hand paste. Warning count remains `1290`, both affected sources have zero LHS candidates, and focused old/new reviewers are green. |
| `CINT-LAXARROW-6` | complete | `LaxArrow_cat(C) := homdc_total_cat(hom_int(id_C))`, `lax_edge`, and derived `lax_square` are active. `CubicalArrow_cat`, `cubical_edge`, `cubical_square`, and both endpoint functors are now transparent readability aliases. Visible square sides compute; generic identity/composition have the expected endpoint boundaries; the existing coherent `CubicalArrow_func` remains a functor on these derived categories, maps visible squares through generic next-Hom action plus profiled compositors, and retains another Hom action. |
| `CINT-MIGRATE-7` | complete | Removed primitive ownership and all object/Hom/endpoint rules from `CubicalArrow_cat`; removed its two specialized identity/composition rules after the alias probe showed they introduced exactly two extra critical-pair warnings. The readable identity/paste helper terms remain typed but are no longer competing runtime normal forms. Focused category, composition, and mapped-square sources/reviewers are green at the inherited warning boundary. |
| `CINT-VARDIM-8` | complete | Because every successor level already refers to the public `CubicalArrow_cat` name, its transparent migration retargets the existing genuine `nat_elim` recursion without changing code grammar. Focused source and reviewer checks are green for square level, variable levels, arbitrary `{L,R,*}` face action, whole semicubical nerve, and recursive frames. The deepest warning-enabled frames consumer matches the completed-branch baseline exactly (`1310` versus `1310`), including dimensions one through three and the generic `2n` boundary. |
| `CINT-ADEQUACY-9` | complete | `emdash3_2_semicubical_representables.lp` defines `StandardSemicube(n)` as Yoneda on `SemiCubePlus_cat`; its `p`-level computes to `Hom(p,n)=Path(CubeFaceCode(p,n))`. The Hom action of `semicubical_nerve_func` is the whole decoder to native restriction functors, the existing action path compares every decoded face with `cube_face_action_func`, and another Hom action remains. This is a uniform selected comparison at arbitrary `p,n`, not a claim that every semicubical set is a native nerve or that degeneracies/connections/Kan structure exist. The rule-free source/reviewer are green with warning count `1310` and zero LHS candidates. |
| `CINT-FACADE-10` | complete | `emdash3_2_cubical.lp` is a rule-free canonical import facade over recursive frames and representable adequacy. Its concise dependency map names the `homdc_int`/Sigma foundation, profiled lifting, levels, code/action/nerve/frames, and Yoneda decoding; it owns no symbol or duplicate theory. |
| `CINT-DOC-11` | complete | Synchronized Foundations, current status/SOP, canonical notation, root and `emdash2` READMEs, nested AGENTS authority inventories, report index, source/metrics registries, focused reviewer examples, and static health source metrics. The documents now distinguish the fixed-boundary `homdc_` view, derived target-first `homdc_int`, outer opposite-Sigma total, transparent `CubicalArrow_cat` facade, generic identity/composition normal forms, arbitrary-dimensional `{L,R,*}` action, and Yoneda representable decoding. Health was refreshed with `--no-check`; no broad aggregate was run. |
| `CINT-CLOSE-12` | complete | Audited all scoped rows and exact worktree state. Checkpoints are `bdf421c` (plan), `5d2fc67` (derived internal hom/total), `cf02336` (varying Sigma projection action), `9caf732` (identity/composition boundaries), `07ad671` (transparent facade migration), `0e06e93` (representable decoding/facade), and `a45b032` (authority synchronization), followed by this plan-only closure checkpoint. Focused owning sources/reviewers, unchanged warning comparisons, zero-candidate LHS audits, report/header/TOC/reference/catalog/static-health checks, script syntax, and diff hygiene are green. The long registered/example/CI/repository aggregates were deliberately not run. No push, merge, publication, tag, PR, history rewrite, branch deletion, or worktree removal was performed. |

## 10. Validation And Git Policy

- Keep every Lambdapi command bounded to 90 seconds.
- Start with ignored focused probes at the real owner position.
- Prefer typed `eq_refl` when testing proof-time unification; conversion-only
  assertions do not classify a unifier.
- Follow LHS minimality and subject-reduction guards for every rule.
- Compare warnings for every new stable head/rule; warnings diagnose but do not
  automatically veto a mathematically selected computation.
- Run owning source/reviewer and nearest static audits during a tranche.
- Eagerly avoid registered/example/health/repository aggregates unless their
  omission blocks classification of changed behavior.
- Preserve all existing work and staged/unstaged boundaries.
- The dedicated branch/worktree and SOP-compliant local checkpoint commits are
  authorized under the user's standing checkpoint instruction; commit only a
  bounded green tranche with synchronized ledger and exact staged diff.
- Do not push, merge, publish, tag, create a PR, amend/rebase/reset, delete a
  branch, or remove a worktree without separate explicit authorization.

## 11. Persistent-Goal Launch Prompt

> Continue the emdash v3.2 cubical internalization and Sigma-derivation work in
> `/home/user1/emdash1-cubical-internalization-v1` on branch
> `goal/cubical-internalization-v3.2`, delegating exact mathematics,
> sequencing, evidence, exclusions, validation, migration, Git discipline,
> and completion to
> `emdash2/reports/REPORT_EMDASH_V3_2_CUBICAL_INTERNALIZATION_AND_SIGMA_DERIVATION_PLAN_2026-08-24.md`
> and its authority chain. Begin at `bfd5f05`. Treat the transparent
> `homdc_int(E) := homd_int(id_(Op_catd(EdgeFamily_E)))` construction as the
> mixed-variance foundational owner; derive the two-sided total through the
> selected nested Sigma/opposite formula; do not retain primitive `CubicalArrow_cat`
> as the final foundation without a measured derivation failure. Preserve the
> completed arbitrary-dimensional code evidence while migrating it only after
> a derived lax-arrow replacement is green. Keep all Lambdapi commands within
> 90 seconds and eagerly avoid broad aggregates. SOP-compliant local checkpoint
> commits on this dedicated branch are authorized after bounded green tranches
> and synchronized ledger. Do not push, merge, publish, tag, create a PR,
> rewrite history, delete branches, or remove worktrees. Do not mark the goal
> complete until every scoped row is implemented, rejected with durable
> evidence, or explicitly deferred behind a concrete prerequisite and all
> affected authorities are synchronized.

## 12. Post-Completion Declaration Clarification

This section records the literal declarations behind the shorter
`EdgeFamily`/two-sided-Sigma prose. It is a clarification of the completed
implementation, not a new primitive design.

### 12.1 How `homdc_int` is transparently derived

Start with a mixed-variance family:

```text
E : K1^op -> Catd(K2).
```

Thus `E[x1] : K2 -> Cat` and `E[x1][x2] : Cat`.

The prose name

```text
EdgeFamily_E[x1] := Sigma(x2 : K2), E[x1][x2]
```

is implemented by the literal symbol `homdc_edge_catd`:

```text
homdc_edge_catd(E) := Sigma_func(K2) o E.
```

An object of `homdc_edge_catd(E)[x1]` is `(x2,u)` with
`u : E[x1][x2]`. For `E := hom_int(id_C)`, this fibre is
`Hom_C(x1,x2)`, so `(x2,u)` is literally an edge `u : x1 -> x2`. The name
`EdgeFamily_E` comes from that specialization. It is not a source symbol and
is unrelated to the older `Edge_catd_func`, the pointwise-opposite
representable used by the presheaf-family calculus.

The next declaration is

```text
D_E := homdc_op_edge_catd(E)
     := Op_catd(homdc_edge_catd(E)).
```

Thus `D_E[x1] = EdgeFamily_E[x1]^op`. This pointwise opposite is the essential
variance adjustment.

The code then declares

```text
homdc_int(E) := homd_int(id_D_E),
```

literally

```text
homdc_int(E)
  := homd_int(id_funcd(homdc_op_edge_catd(E))).
```

This is “derived transparently” because `homdc_int` is a transparent
`symbol ... := ...`: it has no primitive cubical constructor and owns no
rewrite or unification rule. Unfolding it produces the already-existing
stable `homd_int` owner at an identity displayed functor. Because
`Op_catd(Op_catd(X))` reduces to `X`, its source family is again
`homdc_edge_catd(E)`.

The outer base is `K1^op`, so variance forces the canonical projection order:

```text
target y1
  -> target edge (y2,v)
    -> source x1
      -> source edge (x2,u)
        -> a : x1 -> y1.
```

At that projection the ordinary `homd_int` formula gives

```text
Hom_{D_E[x1]}(D_E[a^op](y2,v),(x2,u)).
```

Since `D_E[x1] = EdgeFamily_E[x1]^op`, this is

```text
Hom_{EdgeFamily_E[x1]}
  ((x2,u),EdgeFamily_E[a^op](y2,v)).
```

Ordinary Sigma-Hom computation then exposes an object as

```text
b     : x2 -> y2
alpha : E[x1][b](u) -> E[a^op][y2](v).
```

For `E = hom_int(id_C)`, the two endpoints reduce to `b o u` and `v o a`, so
the filler is the selected directed lax cell

```text
alpha : b o u ==> v o a.
```

The literal readable endpoint of this projection is `homdc_at`.

### 12.2 How the two-sided Sigma and `LaxArrow_cat` are derived

The general two-sided total is

```text
TwoSidedSigma(E)
  := (Sigma(x1 : K1^op),
        (Sigma(x2 : K2), E[x1][x2])^op)^op.
```

The implementation names this transparent expression `homdc_total_cat`, not
`TwoSidedSigma_cat`:

```text
homdc_total_cat(E)
  := Op_cat(
       Sigma_cat(K1^op,homdc_op_edge_catd(E))).
```

A future readable `TwoSidedSigma_cat(E)` would therefore be only a transparent
alias of `homdc_total_cat(E)`. It would not own another object, Hom, identity,
composition, or higher-action theory.

Objects are `(x1,(x2,u))` with `u : E[x1][x2]`. An arrow from
`(x1,(x2,u))` to `(y1,(y2,v))` consists of

```text
a     : x1 -> y1
b     : x2 -> y2
alpha : E[x1][b](u) -> E[a^op][y2](v).
```

The outer opposite turns the base arrow `y1 -> x1` in `K1^op` into the
forward `a : x1 -> y1`; the inner opposite and the Sigma-Hom reversal produce
the forward `b` and the selected direction of `alpha`.

The ordinary lax-arrow category is the specialization

```text
LaxArrow_cat(C)
  := homdc_total_cat(hom_int(id_C)).
```

Its objects are arrows of `C`, and its arrows are the lax squares above.
Finally,

```text
CubicalArrow_cat(C) := LaxArrow_cat(C)
```

is a literal transparent readability/compatibility alias. The dependency is
therefore:

```text
ordinary Sigma + pointwise opposite + homd_int
  -> homdc_int
  -> homdc_total_cat
  -> LaxArrow_cat
  -> CubicalArrow_cat  // transparent alias.
```

## 13. Follow-Up Cubical Adequacy Distinction

Two useful statements must remain distinct.

### 13.1 Geometric/computadic cube observation

```text
H : Functor(CubeShape(n),C)
  |-> native_cube(H) : Obj(CubicalLevel_cat(C,n)).
```

This compares an independently presented geometric cube diagram with the
native iterated-lax-arrow cell. It is the stronger independent validation, but
requires a correct free lax/Gray cube shape. The Cartesian power of the
walking arrow generally describes strictly commuting cubes and must not be
silently substituted for the required lax shape. No `CubeShape(n)` or such
observation is currently implemented.

### 13.2 Representable/Yoneda realization

```text
eta : Hom_Psh(StandardSemicube(n),N_cube(C))
  |-> eta[n](id_n) : Obj(CubicalLevel_cat(C,n)).
```

Here `N_cube(C)[n] = CubicalLevel_cat(C,n)`. A map from the representable
standard semicube assigns a native cell to every face code, coherently under
face substitution. By Yoneda this is another presentation of an already
native `n`-cube, not an independent geometric cube model.

The current implementation has `StandardSemicube(n)`, the native whole nerve,
and a decoder sending each face code to its restriction functor. It does not
yet package the object maps

```text
X |-> (the Yoneda section StandardSemicube(n) -> N_cube(C))
eta |-> eta[n](id_n),
```

nor their beta/eta comparison. Generic `fib_cov_transf` and evaluation at
`cube_face_identity(n)` supply the expected ingredients.

The recommended order for a later goal is:

1. package these two cubical Yoneda object maps and a selected point beta;
2. only then select and validate an independent free lax cube shape and its
   object-level geometric observation;
3. defer whole mapping-category equivalences until the object operations and
   their computational projections are stable.

The simplicial ordinal observation already supplies the more substantive
geometric direction at object level:

```text
H : Functor(DirectedSimplex_cat(n),C)
  |-> ordinal_dependent_simplex_observation(H).
```

A simplicial Yoneda object operation would still be useful for symmetric
whole-face packaging, but first requires a whole native dependent-simplex
semisimplicial nerve. It is therefore a later coherence/organization task,
not a prerequisite for the already-implemented ordinal-to-dependent-simplex
decoder.
