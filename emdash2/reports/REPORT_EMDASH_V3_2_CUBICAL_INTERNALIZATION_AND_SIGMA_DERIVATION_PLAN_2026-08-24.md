# Emdash v3.2 Cubical Internalization And Sigma Derivation Plan

Date: 2026-08-24 (America/Toronto)

Plan-ID: `CUBICAL-INTERNALIZATION-SIGMA-DERIVATION-V3.2`

Status: **active corrective implementation plan**.

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

## 1. Corrective Objective

Restore the same foundations-first architecture that governs the simplicial
development:

```text
internal hom owner
  -> variance-correct displayed/comma family
    -> existing Sigma totalization
      -> recursively iterable shapes.
```

For cubical structure, the new primitive—if a primitive is required—is
`homdc_int`. A shape-specific primitive `CubicalArrow_cat` is not the desired
foundation. The target dependency path is:

```text
homdc_int
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

## 3. Primitive `homdc_int` Boundary

The whole owner must internalize, in a documented projection order,

```text
source K1 endpoint
  -> source K2 endpoint and object
    -> target K1 endpoint
      -> target K2 endpoint and object
        -> side arrow a
          -> side arrow b
            -> filler category.
```

Schematically, its fully evaluated observation is

```text
homdc_int(E)
  [x1][x2][u][y1][y2][v][a][b]
    =
  Hom_{E[x1][y2]}
    (E[x1][b](u),E[a^op][y2](v)).
```

Exact `Catd`/`Functord` nesting must be selected from owner-position probes;
the schematic telescope is not permission to invent a flat record or erase
variance under products. Acceptance requires:

1. the existing transparent `homdc_` is a projection or transparent
   specialization of `homdc_int`, not an independent competing theory;
2. fixing endpoints recovers the existing whole functor in `a` and displayed
   functor in `b`;
3. fixing `a` exposes the expected `homd_int`-shaped slice, with a typed whole
   comparison if the stable owners differ;
4. each remaining endpoint/side parameter retains its next hom action;
5. the `hom_int(id_C)` instance computes to
   `Hom_{Hom_C(x1,y2)}(b o u,v o a)`;
6. the opposite/twisted orientation remains distinct.

If a transparent construction from current `homd_int` cannot retain the
parameter action, a primitive `homdc_int` is justified at this internal-hom
layer. It must own projection/action rules, not merely be an opaque synonym.
The former proposed prerequisite `homd_parameter_func` may then become a
derived slice/comparison rather than a foundational blocker.

## 4. Sigma-First Totalization Policy

No independent primitive `TwoSidedSigma_cat` is planned initially.

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

The first mandatory probe is

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

The probe must classify whether the existing comma total yields:

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

Only the first verdict permits the literal definition
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
  := Sigma_cat C (CommaFib_catd(id_C))
```

when the comma orientation is exact, or

```text
LaxArrow_cat(C)
  := derived two-sided Sigma total of homdc_int(hom_int(id_C))
```

when the generic internalization is required to obtain the correct action.

This ordering is a probe strategy, not a commitment that the pre-existing
comma total outranks `homdc_int`.  The primitive/internal owner remains
`homdc_int`; the comma probe asks whether the active Sigma/comma calculus
already supplies its correctly oriented total as a specialization.  If it
supplies only an equivalent role-swapped category, that comparison is useful
evidence but the public computational arrow category must still be derived
from the `homdc_int` family in the intended source/target order.

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
| `CINT-COMMA-2` | pending | Probe `Sigma_cat C (CommaFib_catd(id_C))` at object, Hom, identity, composition, source/target, and next-action levels; classify it as the exact definitional owner, a typed equivalent but role-swapped presentation, or a genuinely wrong lax/oplax/twisted construction, without adding a bridge. |
| `CINT-HOMDC-DESIGN-3` | pending | Select the exact nested `Catd`/`Functord` type of primitive `homdc_int`, its projection order, and its rules after owner-position probes. Show how it subsumes or derives the former `homd_parameter_func` prerequisite. |
| `CINT-HOMDC-4` | pending | Implement `homdc_int`; derive or transparently route `homdc_` and `homdc_fibre`; validate generic cross-fibre computation, both side actions, endpoint action, higher action, identity-Hom square, and opposite noncollapse. |
| `CINT-TOTAL-5` | pending | Construct the variance-correct comma/two-sided displayed family and totalize it through existing Sigma owners. Add no independent primitive `TwoSidedSigma`; if a measured facade is required, document and validate its delegation boundary. |
| `CINT-LAXARROW-6` | pending | Define Sigma-derived `LaxArrow_cat(C)` and compare it with the current primitive `CubicalArrow_cat` on visible objects, Homs, identity/pasting, source/target, mapped squares, and next action. |
| `CINT-MIGRATE-7` | pending | Retarget `CubicalLevel` and current cubical clients to the derived lax-arrow owner; retire or reduce primitive `CubicalArrow_cat` to a transparent alias only after focused downstream evidence is green. Preserve checkpoint history and negatives. |
| `CINT-VARDIM-8` | pending | Revalidate arbitrary-variable-dimension `{L,R,*}` action, whole identity/composition, `2n` frames, and dimensions one through three against the derived levels. Replace opaque nerve packaging where the new internal action permits an actual construction. |
| `CINT-ADEQUACY-9` | pending | Add standard representable semicubes and a selected internal comparison with native face/boundary action; state the exact remaining boundary to full cubical sets, degeneracies/connections, and Kan structure. |
| `CINT-FACADE-10` | pending | Add one rule-free canonical cubical import facade and concise layer map without merging semantic modules or duplicating owners. |
| `CINT-DOC-11` | pending | Correct Foundations, status/SOP, canonical syntax, README, AGENTS/source registries, report index, examples, catalog, and proportional evidence. Remove ambiguous claims that generic `homdc_int` was completed. |
| `CINT-CLOSE-12` | pending | Audit every scoped row, checkpoint complete/deferred evidence, and hand off exact commits and prerequisites. No push, merge, publication, tag, PR, history rewrite, branch deletion, or worktree removal without separate authority. |

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
> and its authority chain. Begin at `bfd5f05`. Treat primitive `homdc_int` as
> the mixed-variance foundational owner; derive any two-sided total through
> existing Sigma/comma machinery; do not retain primitive `CubicalArrow_cat`
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
