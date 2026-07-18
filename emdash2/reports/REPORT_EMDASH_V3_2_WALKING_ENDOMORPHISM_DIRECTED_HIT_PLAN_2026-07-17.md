# EMDASH v3.2 Walking Endomorphism Directed-HIT And Nat Normal-Form Plan

Date: 2026-07-17
Last reviewed: 2026-07-18
Plan-ID: EMDASH-V3-2-WALKING-ENDOMORPHISM-DIRECTED-HIT-2026-07-17
Depends-On: REPORT_EMDASH_V3_2_EQUALITY_VALUED_OMEGA_EQUIVALENCE_REREDESIGN_PLAN_2026-07-17; REPORT_EMDASH_V3_2_OBSERVATIONAL_EQUALITY_TRUNCATION_UNIVALENCE_REDESIGN_PLAN_2026-07-13; REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26; EMDASH_FOUNDATIONS; emdash3_2.lp; emdash3_2_nat_arithmetic.lp; emdash3_2_eq1_hom_action.lp; emdash3_2_eq1_evidence_property.lp; emdash3_2_checks.lp
Supersedes: none
Side-Task-Ledger: #side-task-ledger
Infinity-Codex-Origin: current-session-walking-endomorphism-review-and-user-clarification-2026-07-17
Infinity-Codex-Decision-Responses: infinity-codex:019f6bd3-8405-7d31-8ced-8a6b127c1499:e08b19e4-e4ef-41f3-bee3-87086450d411; infinity-codex:019f6bd3-8405-7d31-8ced-8a6b127c1499:019f7269-46dc-7942-8438-6110fb05cfdb
Status: **selected theorem-first directed-HIT/BNat MVP implemented, synchronized, and validated; broader initiality and generic directed-HIT work deferred**
Review baseline: `394cf3bc369ddcdb4da74aaf5fdc0557de515532`
Implementation baseline: `8fd9bdfac53b018b77f20ecec24f85efe44febc9`
Parent plan: `REPORT_EMDASH_V3_2_EQUALITY_VALUED_OMEGA_EQUIVALENCE_REREDESIGN_PLAN_2026-07-17.md`, especially deferred task `EVOGJ-H2-READINESS`
Current implementation owners: reusable Nat prerequisites in
`emdash3_2_nat_arithmetic.lp`; walking HIT/model/comparison in
`emdash3_2_walking_end_hit.lp`

## Status And Authority

This report is the adopted bounded sub-plan of the completed selected-MVP
equality-valued omega-equivalence overlay. It activates a concrete review of
that plan's deferred representative-HIT question without reopening or
superseding the completed equality, univalence, groupoidality, structured-J,
evidence-property, or finite-truncation work.

The authority order remains the repository order in `AGENTS.md`. In
particular:

1. `emdash3_2.lp` remains the active computational kernel;
2. the native EQ1 extension modules retain their current one-way dependency
   direction;
3. this report is only the living design and decision ledger for the walking
   endomorphism experiment;
4. the parent July 17 report remains the completed equality/groupoidality
   overlay and the July 13 report remains the retained ledger for unaffected
   H0, truncation, dimension, directed, former-action, and long-term H2 work.

The review and implementation baselines were clean and
`EMDASH_TYPECHECK_TIMEOUT=60s make check` passed on 2026-07-17 before semantic
probes. The commits are historical provenance only and never authorize a
reset or rollback. The measured implementation result is recorded below.

## Current Implementation Checkpoint

The earlier composition-owner blocker has been resolved by correcting the
acceptance boundary, not by adding a family of constructor-specific runtime
bridges.  The active `emdash3_2_walking_end_hit.lp` now implements the selected
MVP:

- a native inductive `WalkingWord_grpd`, intentionally distinct from Nat;
- `WalkingEnd_cat`, with one object, word-valued hom, identity, and
  constructor-directed composition;
- a primitive directed-HIT eliminator
  `walking_end_ind_sec(D,u,ell) : Obj(Pi_cat D)`;
- judgmental point beta and a primitive **propositional** generator beta;
- the nondependent recursor as the constant-`Catd` specialization of that
  eliminator;
- a derived loop-square equality using the loop beta twice and the global
  Kosta-Došen strict cut, with no second composite-action runtime owner;
- the separate one-object Nat model `BNat_cat`;
- a transparent open theorem `bnat_comp_nat_add`, while runtime composition
  retains its semantic head on an open left operand;
- a recursor-derived structured encoder and a structured decoder, each
  compared transparently with the corresponding word/Nat function;
- both arbitrary inverse laws by free-word and Nat induction;
- `TypeEquiv` and native `OmegaEquiv_EQ1` packages for
  `Hom(WalkingEnd,base,base) ~= Nat`;
- internal local-discreteness/`OneCat` evidence; and
- derived loop nonidentity and noninvertibility, with downstream diagnostics
  showing that alleged internal groupoidality yields `Empty_grpd`.

The crucial revised decision is:

```text
point beta       runtime/judgmental
generator beta   equality evidence
composite action global strict functoriality only
arbitrary arrow  WalkingWord induction
```

This is the directed analogue of the ordinary intensional Circle boundary.
The [HoTT/Coq Circle implementation](https://github.com/HoTT/HoTT/blob/master/theories/Spaces/Circle.v)
exposes its loop computation as an equality theorem
(`Circle_ind_beta_loop`), while the
[Cubical Agda Circle presentation](https://github.com/agda/cubical/blob/master/Cubical/HITs/S1/Base.agda)
can make the loop clause compute because its path-composition environment does
not also install Emdash's oppositely oriented strict-functor cut as a
competing rewrite. Those systems are inspiration and comparison evidence
only; neither is an implementation template for this Lambdapi calculus.

The decisive owner-position probe is
`tmp/probes/wehit_circle_style_owner.lp`.  Its quiet run passes in
`logs/probes/wehit_circle_style_owner-20260718-010514.log`; its warning run is
`logs/probes/wehit_circle_style_owner-20260718-010608.log`; and the promoted
owner check is `logs/probes/emdash3_2_walking_end_hit-20260718-014905.log`.
The latter has `977` unjoinable critical pairs and `157` replaceable pattern
variables: exactly six more critical pairs than the kernel baseline, three
from the constructor-directed `WalkingEnd` composition and the same three
from `BNat`.  There is no eliminator/action critical-pair family.  Strict LHS
audit of the promoted module has zero unreviewed clauses.

Despite its chronological proximity to older `wehit_mvp_owner` experiments,
`wehit_circle_style_owner.lp` is the **post-Coq/Agda theorem-first** probe: its
`cs_*` prefix means "Circle style." The older raw-beta/recursive-action
candidates are `wehit_mvp_owner.lp`, `wehit_word_stable_action.lp`, and
`wehit_word_stable_precomp_action.lp`. The Circle-style file is ignored
owner-position evidence, not a second implementation authority; active names
and current behavior are owned only by `emdash3_2_walking_end_hit.lp`.

The six warnings were also tested as typed consumers rather than accepted by
count alone. Identity/pre/postcomposition boundary cases compare directly.
The successor/precomposition case is the associativity square
`k o (g o F[h]) = (k o g) o F[h]`; it is not a desired runtime join. The new
generic theorem `hom_precomp_along_postcomp_assoc` stages the existing stable-
head comparison around `comp_assoc`, avoiding reliance on unification-rule
transitivity. All six WalkingEnd/BNat consumers pass in
`logs/probes/walking_comp_hom_action_consumers-20260718-013636.log`. No
category-specific action theorem or rewrite was needed.

Selected-MVP consolidation on 2026-07-18 passes the complete reviewer-example suite,
strict LHS audits for both the base kernel and the WalkingEnd owner, catalog,
TOC/reference/header/diff checks, refreshed health, and `make ci`. The catalog
contains 1,977 classified diagnostics (1,739 positive and 238 negative) with
zero unclassified entries. Health passes 54 tracked modules/examples; the
WalkingEnd reviewer example contains 20 executable statements. The final CI
metrics phase passes all 54 targets in 140.465 seconds. The warning inventory
remains `971/157` for the base kernel and the measured `977/157` for the
WalkingEnd owner; the six additional pairs are exactly the typed-consumer-
checked constructor-composition pairs described above.

The active diagnostics deliberately contain both sides of the boundary:

- a typed inhabitant of the generator beta;
- a typed derived loop-square equality;
- a negative conversion check showing that raw generator action does not
  reduce to the supplied arrow; and
- arbitrary transparent word/Nat round-trip proofs, together with negative
  conversion checks showing that open round trips are propositional rather
  than proof-erased runtime equations.

The 2026-07-18 post-completion consolidation is also closed. The reusable Nat
slice is a 116-line/6-symbol/1-rule module; the walking owner is now
803 lines/48 symbols/13 rules/2 unifiers and contains no inline assertions.
The permanent suite has 1,978 classified diagnostics across 72 areas (1,739
positive and 239 negative), including both open round-trip conversion
controls. All 55 modules/examples pass. Warning inventories remain `971/157`
for the kernel and Nat module and `977/157` for the walking owner; strict LHS
audits have zero unreviewed clauses. The refreshed health report is current,
and synchronized local CI passes with 128.448 seconds of measured checking
time.

Both one-object sources expose the same reusable proof-time identity pattern:
`walking_functor_zero_view` and `bnat_functor_zero_view` compare action on the
normalized zero word with target identity. The concrete encoder and decoder
zero proofs route through those generic source views; no encoder-specific or
decoder-specific unification rule remains.

### Why the formerly blocked runtime requirement was rejected

The former plan required both point and generator beta as raw runtime
projection rewrites.  Combined with the existing strict rule

```text
F[g] o F[f]  ->  F[g o f],
```

this gave the loop square two normal-form paths: generator beta first exposed
`f o f`, while strictness first exposed the section action on
`loop o loop`.  Requiring those raw terms to join was stronger than the
ordinary intensional Circle interface and created a second authority for
composite action.

An explicit `WalkingWord` "spiral" plus the narrow proof-time comparison
`D[zero](u) == u` repaired closed base/loop/loop-square examples; see
`logs/probes/wehit_mvp_owner-20260718-003850.log`.  It still could not make the
open provenance equation `F[g] o f == F[g o loop]` judgmental after generator
beta erased the fact that `f` came from `F[loop]`.  This was useful evidence:
the missing endpoint variable was not the fundamental issue once arbitrary
directed arrows had their own word induction.

A stable precomposition/action head also made selected equations pass, but it
overlapped every target-specialized generic action owner and added 88
critical pairs; the warning evidence is
`logs/probes/wehit_word_stable_precomp_action-20260718-004346.log`.  It was
rejected rather than promoted.  The earlier recursive-action candidate and
direct composition-to-addition candidate remain useful historical evidence
below, but neither is part of the selected architecture.

### Trust and completeness boundary

`walking_end_ind_sec` and its generator beta are primitive HIT interface, in
the same sense that an inductive or higher-inductive eliminator and its beta
law belong to a foundational presentation.  They are not standalone
round-trip or Hom-classification axioms.  The eliminator returns a structured
section for every `Catd` motive, the ordinary recursor is definitionally
routed through it, and the encoder materially uses that recursor.  The arrow
syntax and its eliminator separately provide the directed freeness principle
needed for arbitrary composite arrows; unlike groupoidal J, directed arrow
induction cannot reduce every arrow to identity.

The decoder is a primitive structured functor head because Emdash functors
are semantic objects rather than record literals.  Its only special law is
propositional generator beta.  The full capped action is not assumed: it is
proved by Nat induction to agree with `nat_to_walking_word`.  Likewise, the
hom equivalence is packaged only after both transparent inverse proofs.

This operational MVP does **not** prove an external model, global confluence,
normalization, canonicity, a general directed-HIT schema, or categorical
initiality at all higher transfors.  It does prove the requested internal
dependent-elimination interface, the concrete Hom-to-Nat correspondence, and
the selected computational observations without declaring Hom to be Nat.

## Historical Blocked Checkpoint (Superseded Decision Evidence)

At the earlier 2026-07-17 checkpoint, only one independent prerequisite slice
was promoted in `emdash3_2_walking_end_hit.lp` (and was later relocated
verbatim to `emdash3_2_nat_arithmetic.lp` during post-completion
consolidation):

- `nat_add` with zero, successor, and open right-unit computation;
- transparent `nat_add_assoc` by native Nat induction;
- internal `unit_is_contr`, `unit_is_prop`, and `empty_is_prop` terms;
- `nat_is_set : IsSetGrpd Nat_grpd` by nested Nat induction over the active
  observational equality classifiers.

The retained slice has permanent diagnostics and the reviewer example
`examples/walking_endomorphism_nat_prerequisites.lp`. Its full owner-position
warning probe retains the baseline `971` unjoinable critical pairs and `157`
replaceable pattern variables, and the strict LHS audit retains zero
unreviewed clauses. The decisive log is
`logs/probes/wehit_nat_owner_full-20260717-214902.log`.

The synchronized blocked checkpoint passes `make check`, all reviewer
examples, catalog/TOC/reference/header checks, health generation, and full
local CI. The generated catalog contains 1,931 classified diagnostics (1,697
positive and 234 negative), health covers 53 files/examples, and the final CI
typecheck phase reports 368.847 seconds total. These gates validate the
retained slice and the consistency of the documentation; they do not convert
the downstream hard blocker into an implemented HIT.

At that superseded checkpoint, the selected directed-HIT MVP was **not**
complete. Two early computational gates appeared to expose the same missing
composition-owner architecture.

### Blocker A: constructor beta versus generic strict functoriality

The exact dependent eliminator shape typechecks. Because `piapp0` and
`piapp1_fapp0` are transparent definitions, the stable constructor owners are
terminal component evaluation and `fdapp1_int_cell`, respectively. Both
individual runtime betas pass and are warning-neutral in the full owner copy;
see `logs/probes/wehit_ind_shape_owner_full-20260717-211309.log` and the
warning run
`logs/probes/wehit_ind_shape_owner_full-20260717-211320.log`.

That local success is insufficient. In a constant motive, the expression

```text
comp(section[loop], section[loop])
```

has two operational paths. Constructor beta first leaves `comp(f,f)`, while
the generic strict-functor cut first leaves `section[loop o loop]`. The latter
has no arrow-induction computation, so the two terms have no common runtime
normal form. The smallest failing assertion is retained in
`logs/probes/wehit_dependent_composition_boundary-20260717-213738.log`; the
two distinct normal forms are printed in
`logs/probes/wehit_dependent_composition_compute-20260717-213839.log`.

The same failure appears through the ordinary constant-motive recursor. A
narrow base/loop observer adapter computes at each constructor, but its
generator-square composition assertion fails. A stable recursive action head
made that one assertion pass in
`logs/probes/wehit_ind_shape_owner_full-20260717-212712.log`, but its general
composition rule overlaps the existing semantic composition owners and raises
the warning inventory from `971/157` to `999/158`; see
`logs/probes/wehit_ind_shape_owner_full-20260717-212723.log`. Adding the
resulting family of constructor-specific bridges would be exactly the ad hoc
design this plan is intended to avoid. A narrowly typed proof-time composition
equation also failed to discharge the closed generator square after
constructor reduction; the final attempt is
`logs/probes/wehit_rec_unif_owner_full-20260717-214215.log`.

This is a normalization/representation blocker, not a mathematical
inconsistency and not a failure to type the eliminator. It invalidates the
earlier computational assumption that the returned section's ambient
functoriality alone supplies generated-composite computation once a generator
beta is installed.

### Blocker B: a transparent `BNat_cat` composition owner

The proposed object, hom, identity, and direct composition-to-addition rules
all typecheck and the Nat/unit/associativity assertions pass in
`logs/probes/wehit_nat_bnat_owner_full-20260717-214725.log`. With warnings
enabled, however, the general rule

```text
comp_fapp0(BNat_cat,g,f) -> nat_add(f,g)
```

creates 18 new unjoinable critical pairs, raising `971/157` to `989/157`; see
`logs/probes/wehit_nat_bnat_owner_full-20260717-214757.log`. The first is the
generic strict-functor cut into `BNat_cat`; the remainder include existing
postcomposition, precomposition, transfor, displayed, and definitional-
isomorphism composition owners. Reducing the target composition to addition
erases the generic semantic head before those paths can join. A stable
`bnat_comp` followed by an unconditional fold to addition has the same final
problem; leaving it opaque would not meet the computational model criterion.

### Required prerequisite and retained alternatives

The smallest credible prerequisite is a reusable free-arrow/composition
interface that does all of the following:

1. gives generated arrows an inductive or otherwise canonical presentation;
2. defines dependent and nondependent action on that presentation;
3. rejoins generator beta with identity, composition, and the existing
   higher hom-action owners at one semantic owner;
4. supplies an eta/arrow-induction principle for arbitrary generated arrows;
5. does not identify the HIT hom with Nat before the comparison proof.

An explicit internal `WalkingWord` syntax distinct from `Nat_grpd` is one
candidate, but it is not yet selected: its dependent action and higher path
functor must be probed before it can be called the HIT rather than another
model. The other candidate is a broader kernel-level registration/refactor of
category-specific composition computation so generic functor/transfor/hom
owners remain authoritative. A proof-time-only `BNat` comparison or explicit
evaluation operation is useful as a weaker interface, but does not satisfy
this plan's runtime normal-form claim.

That checkpoint's conclusion is retained as rejected-decision evidence.  The
selected theorem-first architecture above implements `WalkingEnd_cat`,
`BNat_cat`, encode/decode, and both round trips without the proposed generic
composition-registration layer.  No Hom-to-Nat rewrite, bodyless round trip,
or 18-rule patch family has been installed.

## Executive Decision

The first representative categorical higher-inductive experiment should be
the **walking endomorphism**, also called the free one-object category on one
directed generator. Write it provisionally as:

```text
WalkingEnd_cat : Cat
walking_base   : Obj(WalkingEnd_cat)
walking_loop   : Hom(WalkingEnd_cat, walking_base, walking_base).
```

The generator is directed and is not assumed invertible. Its freely generated
endomorphisms are the powers

```text
id, walking_loop, walking_loop^2, ...,
```

and their expected normal-form monoid is `(Nat,+,zero)`.

The endpoint of this plan is **not** obtained by declaring

```text
Hom_cat(WalkingEnd_cat,walking_base,walking_base)
  -> Path_cat(Nat_grpd).
```

That rewrite would be a useful implementation of a known model, but it would
make the desired correspondence true by declaration. The required endpoint
is instead:

1. an actual primitive or otherwise justified directed-HIT presentation with
   object and arrow constructors;
2. a dependent eliminator into structured `Catd` motives;
3. judgmental point computation, propositional generator computation, and
   derived composite-action laws through the one generic strict owner;
4. a separate transparent Nat normal-form model `BNat_cat`;
5. encode/decode operations derived from the eliminator, Nat recursion, and
   the ordinary functor/section calculus;
6. derived round trips showing that the endomorphism classifier of the HIT is
   equivalent to `Nat_grpd`;
7. computational observations sending identity to zero, the generating loop
   to one, and composition to addition.

This makes the example a real test of elimination and initiality rather than
an abbreviation for a preselected hom-category.

## Why This Is The Right First Representative HIT

The walking endomorphism is the directed analogue of the free monoid on one
generator. It is simpler than the groupoidal Circle because it needs:

- no inverse-loop constructor;
- no word cancellation or group completion;
- no integer normal form;
- no proof that positive and negative powers cancel;
- no prior identification of all directed arrows with paths or equivalences.

Finite words in one generator have canonical length, hence the expected
normal form is Nat. A later groupoid completion should send

```text
BNat -> BInt
```

and provides a natural bridge toward the free groupoid on one loop and the
usual Circle loop-space comparison. That later construction is explicitly
outside this plan.

The example also complements the active primitive `Join_cat(A,B)`. The join
contains a directed cross cell from a left region to a right region and has a
nondependent recursor. The walking endomorphism instead tests cyclic
iteration and dependent elimination. `Join_cat(Unit,Unit)` is a walking arrow
with two distinguished endpoints, not the walking endomorphism; identifying
those endpoints would require a directed coequalizer/quotient or attachment
construction not presently active.

## Current Foundations Relevant To The Plan

The active implementation already supplies most of the ambient language:

- `Nat_grpd`, native `zero`/`succ`, `nat_elim`, recursive observational
  equality, and a retained registered successor action;
- `Cat`, `Obj`, `Hom_cat`, `id`, and generic `comp_fapp0`;
- ordinary functors with iterable `fapp0`, `fapp1_func`, and
  `fapp1_fapp0` action;
- Cat-valued directed families `D : Catd K`, fibre categories, base-arrow
  transport, section categories `Pi_cat D`, section evaluation, and section
  action `piapp1_fapp0`;
- Sigma total categories and dependent homs;
- `Path_cat`, `Core_incl_func`, equality-valued omega-equivalence, and
  internal groupoidality;
- `PathOut` and its structured path-induction section;
- the primitive directed Join and its nondependent recursor.

The active kernel still does **not** provide the following generic facilities.
The one-way walking-plan extension now supplies the concrete walking
endomorphism, Nat model, Nat arithmetic/sethood, and the specialized
comparison without moving them into the kernel:

- a general functor constructor
  `Path_cat(A) -> Path_cat(B)` from a raw function and its higher action;
- a dependent eliminator or semantic initiality theorem for `Join_cat`;
- a generic directed-HIT schema;
- a general free-category or directed-HIT universal-property schema.

These absences are prerequisites or investigation gates, not permission to
replace the desired construction by unrelated axioms.

## Mathematical Specification

### 1. The HIT presentation

The intended object is the free strict directed category generated by:

```text
base : Obj(WalkingEnd_cat)
loop : Hom(WalkingEnd_cat,base,base),
```

with no equation identifying `loop` with `id`, no inverse generator, and no
nonidentity higher generator. Identities, composites, and their strict
functorial higher structure come from the ambient Emdash category kernel.

The phrase "no nonidentity higher generator" does not by itself prove local
discreteness. The implementation must eventually derive or transport the
appropriate `IsDiscreteCat`/`IsNCat(cat_one,...)` evidence from the Nat
normal-form result rather than assume that all higher cells disappear.

### 2. The dependent eliminator

The native Emdash formulation should use a structured motive, not a raw
meta-level family. For

```text
D : Catd(WalkingEnd_cat)
```

the constructor data are:

```text
u : Obj(Fibre_cat(D,base))

ell_D : Hom_(Fibre_cat(D,base))(
          D[loop](u),
          u).
```

Here `D[loop]` is the existing `catd_transport_func` action. The eliminator
should return a section:

```text
walking_end_ind_sec(D,u,ell_D)
  : Obj(Pi_cat(D)).
```

In current kernel notation, the loop datum can use the exact source endpoint
already exposed by `piapp1_src_obj` or the equivalent application of
`catd_transport_func`. Do not introduce a second displayed-arrow
classification merely for this HIT.

The selected constructor computations are:

```text
walking_end_ind_sec(D,u,ell_D)[base]
  -> u

walking_end_ind_sec(D,u,ell_D)[loop]
  = ell_D.
```

The first observation is judgmental through the stable terminal-component
projection. The second is an inhabitant of the displayed generator equality
classifier comparing `piapp1_fapp0(ind,loop)` with `ell_D`. This revised
acceptance decision is deliberate and permanent for the selected intensional
MVP: raw generator action must remain stuck so that generic strict
functoriality is the sole runtime composite-action owner.

Mathematically there is no extra relation on the generator, so no independent
algebra law is requested from the user. Computationally, `WalkingWord`
supplies induction over arbitrary generated directed arrows. Composite action
is then proved from generator beta plus strict functoriality; it is not
installed as another normalization family.

### 3. Derived nondependent recursor

For a target category `C`, object `x : Obj(C)`, and endomorphism
`f : Hom(C,x,x)`, specialize the dependent eliminator to the constant motive:

```text
Const_catd(WalkingEnd_cat,C).
```

The existing proof-time comparison

```text
Pi_cat(Const_catd(K,C)) == Functor_cat(K,C)
```

should make the resulting section readable as:

```text
walking_end_rec_func(C,x,f)
  : Functor(WalkingEnd_cat,C).
```

Type acceptance through the `Pi_cat(Const_catd)`/`Functor_cat` comparison
does not by itself guarantee that an ordinary `fapp0` or `fapp1_fapp0`
projection computes on the section term. Probe the two ordinary-functor
observers separately. If an explicit named adapter/wrapper is needed, its
body must route through `walking_end_ind_sec`, and its projection bridges must
join with the `piapp0`/`piapp1_fapp0` route. Do not infer observer computation
merely from successful proof-time type comparison.

Required computations are:

```text
walking_end_rec_func(C,x,f)[base] -> x
walking_end_rec_func(C,x,f)[loop] = f.
```

The readable recursor routes definitionally through the dependent eliminator;
it is not an independent primitive with duplicate semantic authority.  The
loop equation is `walking_end_rec_beta_loop` and raw action remains stuck.

### 4. Initiality and uniqueness

At object level, functors out of the HIT should be determined by an object and
an endomorphism. The full categorical universal property is more accurately
an equivalence between `Functor_cat(WalkingEnd_cat,C)` and a category of
endomorphism objects whose arrows are intertwiners, not merely the informal
classifier `Sigma x, Hom_C(x,x)`.

The initial operational milestone does not construct that entire category
equivalence.  The selected concrete free presentation instead exposes
`walking_word_elim`, the induction principle for every generated directed
arrow.  It proves the reverse Nat round trip transparently.  Full uniqueness
of functors at all transfor levels remains a separate strengthening.

This is not a standalone round-trip capability: the proof body is native word
induction and the encoder itself is produced by the dependent eliminator's
constant-motive specialization.  A future abstract HIT interface lacking an
explicit free-arrow presentation would still need a corresponding arrow-eta
or extensionality principle.

Three more abstract proof presentations remain candidates for that future
strengthening:

1. a displayed logical-relation motive over `WalkingEnd_cat`, discharged by
   `walking_end_ind_sec`;
2. a transfor between the endofunctors
   `walking_decode_func o walking_encode_func` and `id_func`, generated from
   their agreement on the base and loop;
3. a structured motive over `PathOut_cat(WalkingEnd_cat,base)` whose objects
   are arbitrary outgoing arrows and whose target property is the desired
   arrow round trip.

These are alternative presentations of the same freeness argument. They were
not required for this explicit one-generator free-word MVP.

## The Separate Nat Normal-Form Model

### 1. `BNat_cat`

Construct a separate transparent one-object category, provisionally:

```text
BNat_cat : Cat
bnat_obj : Obj(BNat_cat).
```

Its intended computation is:

```text
Obj(BNat_cat)                  -> Unit_grpd
bnat_obj                       -> tt
Hom_cat(BNat_cat,_,_)          -> Path_cat(Nat_grpd)
id_(BNat_cat)                  -> zero
comp_(BNat_cat)(n,m)           -> nat_add(n,m)
bnat_generator                 -> succ(zero).
```

The exact addition order must follow the convention that
`comp_fapp0(g,f)` means `g o f`. Choose and document one recursion orientation
before promotion. Since powers of one generator commute mathematically, this
example alone can conceal a variance error; diagnostics must inspect open
normal forms and not appeal only to commutativity of addition.

This category is the explicit semantic/computational model. It is legitimate
for its hom classifier to reduce to Nat because it is not the HIT whose
freeness is being tested.

The object/identity/composition rules initially make the model transparent at
objects and 1-arrows. Its higher composition action is still the generic
`comp_prod_func`/`comp_prod_fapp1*` action of the ambient kernel. Before the
comparison is called fully computational, Phase 4 must either relate that
action to the selected path action of `nat_add` or explain why Nat
discreteness makes the generic owner sufficient. Do not describe an opaque
BNat-specific higher action as if addition functoriality had been derived.

### 2. Nat arithmetic and truncation

Add or derive, in a suitable library owner:

```text
nat_add zero n       -> n
nat_add (succ m) n   -> succ(nat_add m n)
```

or the deliberately selected opposite recursion orientation. Prove or expose
the unit and associativity facts required by the selected category
presentation without adding a second global category-law calculus.

Separately prove:

```text
nat_is_set : IsSetGrpd(Nat_grpd)
```

from Nat induction, constructor equality, and the active Empty/Unit
truncation facts. Constructor-level equality computation is strong evidence
but is not itself an inhabitant of `IsSetGrpd Nat_grpd`.

The sethood theorem supports the precise statement that
`Path_cat(Nat_grpd)` is discrete and that `BNat_cat` is locally discrete. Do
not call the hom a set internally before this evidence exists.

## Encode, Decode, And The Required Nat Correspondence

### 1. Encoding generated arrows

Use the derived recursor with target `BNat_cat`, sending:

```text
base |-> bnat_obj
loop |-> succ(zero),
```

to obtain:

```text
walking_encode_func : Functor(WalkingEnd_cat,BNat_cat).
```

Its endomorphism action is:

```text
walking_encode(p)
  := walking_encode_func[p]
  : Nat.
```

The selected observations are:

```text
walking_encode(id)          =  zero
walking_encode(loop)        =  succ(zero)
walking_encode(g o f)       =  nat_add(walking_encode(g),walking_encode(f))
```

`walking_functor_zero_view`, `walking_end_rec_beta_loop`, and
`walking_encode_comp_view` derive these equations from generic strict
functoriality plus the selected `BNat_cat` normal form. There is no duplicated
encode-specific preservation rewrite.

### 2. Decoding Nat normal forms

Define powers transparently by Nat recursion, publicly named
`nat_to_walking_word`:

```text
nat_to_walking_word(zero)   := id
nat_to_walking_word(succ n) := loop o nat_to_walking_word(n)
```

with the exact composition orientation synchronized with `nat_add`.

The comparison ideally packages this as:

```text
walking_decode_func : Functor(BNat_cat,WalkingEnd_cat),
```

whose arrow action is propositionally identified with
`nat_to_walking_word`. A capped raw function is insufficient for the final
result because the functor must remain iterable at higher homs.

### 3. Round trips

The easy round trip should be derived by Nat induction:

```text
walking_word_to_nat(nat_to_walking_word(n)) = n.
```

The decisive HIT round trip is:

```text
nat_to_walking_word(walking_word_to_nat(p)) = p
```

for arbitrary

```text
p : Hom(WalkingEnd_cat,base,base).
```

This proof materially uses `walking_word_elim`, the structured induction
theorem for arbitrary generated arrows.  Together with the recursor-derived
encoder, this satisfies the concrete freeness gate. A direct global axiom, an
opaque round-trip theorem with no body, or a hom-to-Nat rewrite inserted
before the proof would not satisfy the plan.

After both round trips, package the result first through the active native
groupoid-equivalence interface, for example an
`OmegaEquiv_EQ1(Grpd_cat,Hom(...),Nat_grpd)`, and derive a `TypeEquiv`
comparison only as useful library surface. Do not introduce a new decoder.

### 4. Stronger comparison

A category-level equivalence between `WalkingEnd_cat` and `BNat_cat` is a
desirable strengthening after the hom equivalence is active. It is not a
substitute for the explicit hom encode/decode computations, and it should be
derived from the same functors rather than asserted independently.

## `PathMap`, `ObsAction`, And Higher Functoriality

### Current distinction

`ObsAction(f)` starts from a raw function `f : τ A -> τ B` and stores one
selected action on paths plus a pointwise comparison with `eq_ap(f)`.
Structured groupoidal J starts from an already functorial `Catd` motive. One
does not replace the other.

A reusable constructor of the schematic form

```text
path_map_func(f) : Functor(Path_cat(A),Path_cat(B))
```

would be useful for the transparent `walking_decode_func`, for other
path-category-valued models, and eventually for presenting raw-function
action through ordinary functor machinery. It is not currently active.

### Why it is not a trivial wrapper

An iterable functor needs a full hom-action functor at every dimension. A
single `ObsAction(f)` supplies only the selected first path operation and its
agreement with semantic `eq_ap`; it does not automatically supply an
`ObsAction` tower for the action map itself.

A naive rule

```text
path_map_func(f)[p] -> eq_ap(f,p)
```

must also join with generic strict functor identity and composition. In
particular, the two reductions of

```text
path_map_func(f)[q] o path_map_func(f)[p]
```

must agree when generic functoriality folds first and when both actions expose
their selected path terms first. Since `Path_cat` deliberately retains
generic `comp_fapp0` rather than reducing all path composition to `eq_trans`,
this is a real owner/normal-form question.

### Selected specialized boundary

The implementation assessed the intended fork:

1. a general raw-function-to-`Path_cat` functor remained disproportionate and
   retained the known recursive higher-action/composition questions;
2. broad stable action/precomposition heads were rejected after the measured
   88-critical-pair increase;
3. the MVP selected a semantic structured functor
   `walking_decode_func : Functor(BNat_cat,WalkingEnd_cat)` with object beta,
   propositional generator beta, and a Nat-inductive theorem identifying its
   complete capped action with `nat_to_walking_word`.

Selection criteria are:

- full `fapp1_func` iterability, not merely capped action;
- identity and composition joining at the first two hom levels;
- no opaque higher-action capability;
- no assumption that proof-time comparison is transitively propagated;
- no forced replacement of the real Nat/PathRecord `ObsAction` consumers;
- a public API reusable by later standard-library constructions.

The selected term remains iterable because its public type is an ordinary
Emdash functor; generic `fapp1_func` supplies its higher semantic action. The
plan does not claim that a raw function automatically generates that functor,
or that `ObsAction` is subsumed. A reusable `path_map_func` remains deferred
standard-library/kernel research, not an MVP prerequisite.

### Relationship to Join

`PathMap` is not a prerequisite for the existing Join recursor: Join already
consumes ordinary functors and an internally natural cross cell. It may help
future path-category-valued Join models or motives, but it does not supply the
missing dependent Join eliminator.

The genuinely reusable contribution to Join is the dependent-HIT pattern:

```text
structured Catd motive
  + displayed constructor data
  -> Pi_cat section
  + constructor computation.
```

After the walking endomorphism succeeds, a separate Join follow-up can ask
for sections over the two inclusions plus a displayed lift of the internally
natural cross cell. Do not expand this plan into that larger task.

## Composition Ownership And The Hom Actions

`comp_fapp0` is the semantic operation for ordinary categorical composition.
The walking endomorphism and `BNat_cat` must expose their selected
category-specific computation through that owner.

The families

```text
hom_postcomp_*
hom_precomp_along_*
hom_int
hom_con
```

are iterable functorial presentations of postcomposition, precomposition,
and represented hom variation. They are not alternative definitions of the
underlying category composition. Consequently:

1. first establish the selected `comp_fapp0(BNat_cat,...)`/Nat computation;
2. let generic `hom_postcomp*` and `hom_precomp*` expose the resulting action;
3. test their visible projections as consumers;
4. add no `BNat_cat`- or walking-specific hom-action rule whose only content
   is ordinary composition/functoriality;
5. add a specialized bridge only if a stable projection erases the generic
   owner and both reduction orders have been measured.

### Selected constructor-directed composition

The direct open rule `comp(BNat,g,f) -> nat_add(g,f)` was rejected because it
erased the semantic composition head too early. The selected presentation
recurses only when a constructor is visible:

```text
comp(BNat,zero,f)    -> f
comp(BNat,g,zero)    -> g
comp(BNat,succ(g),f) -> succ(comp(BNat,g,f)).
```

`WalkingEnd` uses the same constructor-directed shape on `WalkingWord`.
`nat_add` recurses on its left input in the same orientation, and
`walking_word_to_nat_comp` proves that word composition maps to
`nat_add(length(g),length(f))`. Open composition retains `comp_fapp0`; it is
not silently normalized to an arithmetic head.

The owner probe tested both reduction orders for:

- `g o id` and `id o f` against the generic unit rewrites;
- triple composition against the generic proof-time associativity equation;
- opposite composition;
- the action of an arbitrary functor out of `BNat_cat`;
- visible `hom_postcomp_fapp0` and `hom_precomp_along_fapp0` consumers;
- open Nat terms, not only closed numerals.

The selected rules use `_` for recoverable endpoints and add only the six
documented constructor/generic-owner critical pairs. The two narrowly typed
zero-action `unif_rule`s are validated by typed `eq_refl` views and are never
described as runtime Nat normalization.

## Auxiliary Univalence And Groupoidality Tests

These are useful sub-tasks because they test that the completed parent design
preserves the distinction between arrows, paths, and equivalences.

### Nonidentity

After the Nat equivalence is derived, prove computationally:

```text
walking_loop != id.
```

Under encoding this is `succ(zero) = zero`, whose classifier reduces to
`Empty_grpd`. Do not install nonidentity as a primitive axiom.

### Noninvertibility

Derive that `walking_loop` has no native equality-valued omega-equivalence
evidence. An alleged inverse encodes to a Nat whose composite with one would
equal zero; the relevant Nat successor/zero equality is empty.

The exact theorem may be exposed as a function from

```text
OmegaEquivAlong_EQ1(WalkingEnd_cat,base,base,walking_loop)
```

to `Empty_grpd`, using the active inverse/law projections. It must not rely on
legacy D0 decoders.

### Nongroupoidality

Derive a negative groupoidality theorem by applying alleged
`IsGroupoidalCat_EQ1(WalkingEnd_cat)` evidence to the generating loop and then
using noninvertibility. This is a stronger architecture test than merely
omitting a groupoidality constructor.

### Object-level univalence sanity

The category can still be object-univalent: it has one object, and the Nat
model should show that its only invertible endomorphism is zero. The test must
confirm that object univalence does not turn every endomorphism into an
equivalence. In particular, the path/core inclusion reaches the identity
arrow but not `walking_loop`.

### Directed dimension

After Nat sethood and the hom equivalence are active, attempt to derive that
the model and then the HIT are ordinary one-categories in the active
`IsNCat(cat_one,...)` sense. If truncation transport across the derived
category/hom equivalence is missing, record that theorem as a separate
reusable prerequisite rather than adding one-off evidence to the HIT.

## Module And Ownership Strategy

Begin in a one-way extension module, provisionally:

```text
emdash3_2_walking_end_hit.lp
```

which imports the active kernel and, only when needed, the native EQ1
extensions. The active kernel must never import this experimental module.
Keep the HIT presentation, Nat model, and comparison in one module during the
architecture phase; split them only after the dependency boundary is stable.
Do not combine a file split with a rewrite-normal-form migration.

Post-completion consolidation applies that boundary literally: reusable Nat
addition, associativity, Unit/Empty proposition evidence, and Nat sethood now
live in `emdash3_2_nat_arithmetic.lp`. The walking module imports them while
retaining `WalkingWord`, both one-object categories, the eliminator,
encode/decode, equivalence packages, and directed negative results. The usual
unqualified arithmetic spellings remain transitively available to clients of
the walking module; their module-qualified owner intentionally moves. No
rule, unifier, theorem body, or runtime normal form changed in the split.

The selected public surface is:

```text
WalkingWord_grpd
walking_word_elim
WalkingEnd_cat
walking_base
walking_loop
walking_end_ind_sec
walking_end_ind_beta_loop
walking_end_rec_func
walking_end_rec_beta_loop

BNat_cat
bnat_obj
bnat_generator
nat_add
bnat_comp_nat_add
walking_word_to_nat
nat_to_walking_word
walking_encode_func
walking_encode_comp_view
walking_decode_func
walking_decode_comp_view
walking_hom_nat_type_equiv
walking_hom_nat_omega_equiv_EQ1.
```

The API uses "walking endomorphism" or `BNat` rather than "directed Circle",
because the latter suggests an invertible topological loop.

Permanent executable diagnostics belong in `emdash3_2_checks.lp` only after
the module is adopted into the ordinary check graph. Reviewer-facing
mathematical statements should live in a focused example such as:

```text
examples/walking_endomorphism_hit.lp
```

## Phased Implementation Plan

### Phase 0: adoption and exact interface probes — completed

1. Explicitly adopt or revise this proposal before editing active semantic
   owners.
2. Re-read current authorities and inspect staged/unstaged work.
3. Remeasure bounded check, warning, audit, catalog, and example baselines.
4. Probe the exact `Catd` loop-lift type and both `Pi_cat` projection betas in
   an owner-position full-file copy.
5. Probe constant-motive specialization through the existing direct
   `Pi_cat(Const_catd)`/`Functor_cat` comparison.
6. Separately probe ordinary `fapp0`/`fapp1_fapp0` observations of the
   constant-motive result; type acceptance is not observer computation.
7. Record the owner-position distinction between judgmental point beta and
   propositional generator beta.

Exit criterion: the dependent eliminator signature typechecks in isolation,
both proposed projection owners are identified, and the generator equality is
an explicit HIT beta rather than an opaque composite-action theorem.

### Phase 1: Nat monoid and discreteness prerequisites — completed

1. Define selected Nat addition transparently.
2. Add computation diagnostics for both constructors and open terms.
3. Derive unit and associativity statements needed by the category model.
4. Prove `IsSetGrpd Nat_grpd`.
5. Expose only the minimal reusable arithmetic/truncation API required by the
   comparison.

Exit criterion: Nat addition computes, its laws are derived without global
proof erasure, and Nat sethood is an internal term.

### Phase 2: transparent `BNat_cat` model — completed

1. Add the one-object category and object/hom projections.
2. Select constructor-directed native composition from focused probes.
3. Add identity, generator, and composition computation.
4. Test both generic-unit orders, associativity, opposite, functor action,
   postcomposition, and precomposition consumers.
5. Derive local discreteness/one-category evidence where current closure
   theorems suffice.

Exit result: `BNat_cat` is a coherent computational category model with Nat
arrow normal forms, generic higher composition still owned by the ambient
calculus, internal local-discreteness evidence, and no category-specific
post/precomposition rules. The three constructor-owner overlaps are measured
and recorded rather than multiplied into an action bridge family.

### Phase 3: HIT constructors and dependent eliminator — completed at the revised beta boundary

1. Add `WalkingEnd_cat`, `walking_base`, and `walking_loop` without a Hom-to-
   Nat rule.
2. Add the single dependent eliminator owner returning a `Pi_cat` section.
3. Promote judgmental base beta and propositional loop beta after
   owner-position critical-pair checks.
4. Add negative controls showing that no object eta, loop identity, inverse,
   or Nat hom classification is silently available.
5. Derive the constant-motive recursor through the eliminator.

Exit result: the actual HIT constructors, structured dependent eliminator,
judgmental point beta, explicit loop-beta witness, derived recursor, and
derived loop-square law are executable. The raw loop action remains a
negative conversion control.

### Phase 4: path-map/higher-action fork — completed at specialized boundary

1. Probe the generic `Path_cat` functor constructor and its first two hom
   actions.
2. Test identity and composition in both reduction orders.
3. Determine the precise relationship with semantic `eq_ap` and retained
   `ObsAction`; do not claim full registry subsumption from one projection.
4. If the generic route is unstable or disproportionate, implement the
   smallest honest specialized higher-action owner needed for
   `walking_decode_func` and record the generalization gate.

Exit result: the documented specialized `walking_decode_func` is an iterable
semantic functor. Its generator beta is explicit and its arbitrary capped
action is proved by Nat induction. Generic `PathMap` and `ObsAction`
subsumption remain explicitly deferred.

### Phase 5: encode, powers, and decode — completed

1. Derive `walking_encode_func` from the HIT recursor.
2. Define `walking_power` by Nat recursion.
3. Package powers as `walking_decode_func` through the selected Phase-4
   architecture.
4. Check identity, generator, successor/power, and composition formulas.
5. Preserve generic functoriality as the owner of encode/decode preservation.

Exit criterion: both comparison directions are iterable functors or otherwise
have an explicitly equivalent structured presentation; capped functions alone
are not the final boundary.

### Phase 6: round trips and hom equivalence — completed

1. Prove encode-after-power by Nat induction.
2. Derive power-after-encode for arbitrary generated arrows from native
   `WalkingWord` induction.
3. Retain displayed-logical-relation, endofunctor-transfor, and structured
   `PathOut` presentations as future abstract-initiality strengthenings.
4. Keep full functor/transfor extensionality outside the concrete Hom
   equivalence boundary.
5. Package the hom equivalence in native EQ1 form and derive the optional
   `TypeEquiv` view.
6. Add closed and open computational examples.

Exit criterion: both arbitrary round trips have transparent bodies, the hom
equivalence is active, and no prior Hom-to-Nat rewrite made either theorem
tautological.

### Phase 7: selected univalence and dimension consumers — completed; full initiality deferred

1. Record full functor/transfor uniqueness as a strengthening beyond the
   explicit free-word Hom result.
2. Defer category-level equivalence with `BNat_cat` and the category of
   endomorphism algebras.
3. Prove loop nonidentity, loop noninvertibility, and category
   nongroupoidality.
4. Check object-level univalence/core behavior.
5. Derive OneCat/local-discreteness evidence or record the exact missing
   equivalence-invariance theorem.

Exit result: the example consumes native EQ1 packaging, proves the loop
nonidentity/noninvertibility/nongroupoidality tests, and derives OneCat
evidence without collapsing directed arrows into paths.

### Phase 8: consolidation and next-scope decision — completed

1. Synchronize active code, checks, reviewer example, Foundations, current
   status, this ledger, report index, catalog, and health report.
2. Run warning summary, strict LHS audit, examples, catalog, health, and CI.
3. Decide whether the next bounded objective is dependent Join elimination,
   a generic directed-HIT schema, groupoid completion toward `BInt`, or
   continued deferral.
4. Do not begin the next objective in the same semantic migration.

Exit criterion: all promoted claims have executable evidence and every
remaining gap has an exact owner/prerequisite.

## Implemented First Slice And Revised Decision

The original slice exposed the raw loop-beta/composite-action conflict. A
later explicit-word probe showed that arbitrary directed arrows have the
required induction structure, while comparison with standard Circle
interfaces showed that raw loop beta was an unnecessarily strong acceptance
condition. The theorem-first revision is now promoted.

The realized first slice is:

1. owner-position probe of the exact dependent eliminator type;
2. native non-Nat `WalkingWord` syntax and `WalkingEnd_cat` composition;
3. `walking_end_ind_sec` returning `Pi_cat D`;
4. base projection beta through `piapp0`;
5. a propositional loop beta at `piapp1_fapp0`;
6. constant-motive recursor, point computation, loop theorem, and derived
   loop-square theorem;
7. negative assertions that the hom does not reduce to Nat and the loop does
   not reduce to identity;
8. warning/LHS comparison, BNat comparison, both round trips, and bounded
   active checks.

This slice answers the central feasibility question positively: the current
`Catd`/section/action kernel can host a structured dependent eliminator for a
genuine directed arrow constructor when the generator beta is propositional
and composite runtime action remains globally owned. Generic `PathMap` was
not used to conceal or implement that boundary.

## Probe And Diagnostic Matrix

| Area | Positive requirement | Negative/control requirement |
| --- | --- | --- |
| HIT formation | base and loop typecheck | no Hom-to-Nat conversion |
| dependent motive | loop lift has exact `D[loop](u) -> u` endpoint | raw family is not silently accepted as `Catd` |
| base beta | `piapp0(ind,base)` computes to `u` | unrelated section projection does not fold |
| loop beta | `walking_end_ind_beta_loop` inhabits the exact displayed equality | raw generator/arbitrary action does not fold to the lift |
| recursor | constant motive yields `Functor(W,C)` | no independent primitive recursor body |
| Nat model | id/loop/comp expose 0/1/addition | open terms do not collapse by commutativity |
| category units | both generic/category-specific orders join | no duplicate global unit rule |
| associativity | typed generic associativity survives Nat exposure | no claim that proof-time firing is runtime normalization |
| path map | specialized decoder remains an iterable Functor | capped `eq_ap` alone is not called a functor package |
| encode | point computes; loop/comp laws are derived | no encode-specific duplicate functor laws |
| decode | zero/successor action laws are derived | no claim that a raw function generated the semantic functor |
| round trips | both arbitrary directions have bodies | no prior Hom rewrite or bodyless theorem |
| nonidentity | encoded loop/identity equality reaches Empty | loop is not declared unequal axiomatically |
| nongroupoidality | alleged evidence yields Empty | absence of constructor alone is not a proof |
| Join relation | dependency remains one-way/conceptual | no claim `Join(Unit,Unit)=WalkingEnd` |

## Feasibility Assessment

| Deliverable | Mathematical feasibility | Current computational feasibility | Assessment |
| --- | --- | --- | --- |
| Nat addition and powers | standard | `nat_add`, associativity, and transparent word powers promoted | complete |
| `Nat_grpd` sethood | standard | nested native Nat induction now supplies an internal term | complete |
| transparent `BNat_cat` | standard one-object monoid category | constructor-directed composition preserves the generic head on open arrows | complete; three measured owner overlaps |
| dependent eliminator formation | standard induction principle for the free category | exact `Catd`/`Pi_cat` signature active | complete at MVP interface |
| base constructor beta | standard | stable terminal-component runtime owner | complete |
| loop constructor beta | standard intensional HIT equality | primitive exact equality evidence; no raw action rewrite | complete at selected boundary |
| derived constant recursor | standard | definitionally routes through the dependent eliminator; loop square derived | complete |
| generic `PathMap` | standard functorial action of functions on paths | recursive higher action and generic composition diamonds remain unresolved | deferred; not an MVP blocker |
| specialized power functor | standard monoid functor | semantic Functor head plus Nat-inductive action agreement | complete at specialized boundary |
| encode-after-decode | Nat induction | transparent Nat proof | complete |
| decode-after-encode | free-arrow induction | transparent WalkingWord proof | complete |
| native hom equivalence | follows from round trips | `TypeEquiv` and native EQ1 packages compute on forward map | complete |
| loop noninvertibility | elementary free-word argument | native inverse-law projections reach Empty | complete |
| nongroupoidality | follows immediately | active `IsGroupoidalCat_EQ1` consumer exposes loop evidence | complete in diagnostics |
| full functor-category initiality | classical | requires an endomorphism-algebra category and coherent extensionality | medium/low; strengthening |
| generic directed-HIT schema | mathematically plausible | beyond one constructor and current Join staging | deferred research/architecture |

Overall, the mathematical target is sound and the selected small extension is
computationally feasible. What was infeasible was the stronger demand for a
raw generator-action rewrite alongside the existing strict-functor cut, and
the direct open collapse of semantic BNat composition to addition. Explicit
free-arrow syntax, propositional generator beta, constructor-directed
composition, and theorem-level comparisons form a coherent alternative.
Remaining work concerns generic abstraction and external metatheory, not the
selected concrete Hom-to-Nat MVP.

## Risks And Mitigations

### Risk 1: the Nat model is mistaken for the HIT

Mitigation: keep `WalkingEnd_cat` and `BNat_cat` distinct until encode/decode
and both round trips are derived. Retain a negative Hom-conversion assertion.

### Risk 2: a primitive recursor is presented as dependent induction

Mitigation: the primary owner returns a section for arbitrary structured
`Catd` motives and consumes a displayed loop lift. The nondependent recursor
must be a constant-motive specialization.

### Risk 3: beta is only stated propositionally

Mitigation: the point beta remains runtime; the exact generator beta is a
public equality witness, and loop-square/composite laws are derived. Retain a
negative raw-action conversion test so documentation cannot silently turn
the theorem into a computation claim.

### Risk 4: functor uniqueness is assumed

Mitigation: make the reverse Nat round trip an acceptance gate. The concrete
MVP discharges it by native free-arrow induction. Full functor/transfor
uniqueness remains explicitly deferred rather than inferred from the Hom
round trip.

### Risk 5: one `ObsAction` is mistaken for an omega-functor

Mitigation: retain `ObsAction` unchanged. The specialized decoder is declared
as an ordinary semantic functor and its complete first action is compared by
Nat induction; no raw-function-to-functor constructor is claimed.

### Risk 6: category-specific composition duplicates hom-action owners

Mitigation: use constructor-directed `comp_fapp0` computation, keep open
composition at the semantic head, and treat post/precomposition as consumers
of generic actions. The six resulting owner overlaps are measured; no
duplicate action bridges are installed.

### Risk 7: Nat commutativity hides variance

Mitigation: inspect open normal forms, document the `g o f` addition order,
and retain a later two-generator free-category test if variance needs a
noncommutative witness.

### Risk 8: univalence accidentally groupoidalizes the category

Mitigation: derive explicit loop noninvertibility and nongroupoidality while
checking that object-level univalence/core behavior remains coherent.

### Risk 9: an implementation extension is promoted directly into the kernel

Mitigation: start in a one-way module, validate the public consumer, and move
an owner only when its dependency and normal-form role are stable.

### Risk 10: operational success is overstated as metatheory

Mitigation: this plan claims a checked Lambdapi presentation and derived
computations, not an external consistency, normalization, canonicity, or
semantic-model proof. Those remain the parent's deferred metatheory track.

## Side-Task Ledger

| Task ID | Initial status | Purpose | Dependency | Status-changing result |
| --- | --- | --- | --- | --- |
| `WEHIT-ARCH-REVIEW` | **completed 2026-07-17** | select representative HIT and honest acceptance boundary | completed parent MVP | walking endomorphism selected; explicit Nat model separated from HIT; dependent elimination and derived round trips required |
| `WEHIT-ADOPT` | **completed 2026-07-17** | explicitly adopt/revise this plan for implementation | architecture review | user handoff fixed baseline `8fd9bdf...`; active state and all proportional baselines remeasured |
| `WEHIT-IND-SHAPE` | **completed/revised 2026-07-18** | type exact `Catd` motive, loop lift, section result, and beta interface | adoption | exact signature and point beta active; loop beta selected as equality evidence after Circle-interface comparison; loop square derived |
| `WEHIT-NAT-ADD` | **completed/promoted 2026-07-17** | transparent Nat monoid operations and laws | adoption | constructor/open unit computation and transparent associativity active with no warning/audit delta |
| `WEHIT-NAT-SET` | **completed/promoted 2026-07-17** | internal `IsSetGrpd Nat_grpd` proof | Nat equality/truncation kernel | nested Nat-induction proof, permanent diagnostics, and reviewer example pass |
| `WEHIT-COMP-OWNER` | **resolved by revised boundary 2026-07-18** | preserve the single generic composite-action owner | measured HIT and BNat failures | explicit `WalkingWord` induction selected; raw loop beta/direct open addition rejected; constructor composition adds only six measured owner pairs |
| `WEHIT-BNAT-MODEL` | **completed/promoted 2026-07-18** | separate transparent one-object Nat category | Nat addition/sethood and revised composition owner | constructor-directed identity/composition, generator, local discreteness, and OneCat evidence active |
| `WEHIT-HIT-INTRO` | **completed/promoted 2026-07-18** | add HIT category, base, and directed loop without Hom-to-Nat conversion | explicit WalkingWord syntax | native word hom and nonidentity directed generator active |
| `WEHIT-HIT-IND` | **completed at propositional-loop-beta boundary 2026-07-18** | dependent eliminator, runtime point beta, equality generator beta | HIT introductions | structured `Catd` section interface active; raw loop action retained as negative conversion control |
| `WEHIT-REC` | **completed/promoted 2026-07-18** | derive nondependent recursor from constant motive | dependent eliminator | body routes through `walking_end_ind_sec`; loop beta and loop-square equality have explicit terms |
| `WEHIT-PATH-MAP` | **completed at specialized boundary; generic constructor deferred 2026-07-18** | honest structured reverse comparison | Nat model and comparison consumer | `walking_decode_func` is iterable; generator beta plus Nat-inductive action agreement active; `ObsAction` unchanged |
| `WEHIT-ENCODE` | **completed/promoted 2026-07-18** | recursor-derived functor from HIT to Nat model | recursor and `BNat_cat` | point computation, generator beta, successor and arbitrary word-length agreement active |
| `WEHIT-DECODE` | **completed/promoted 2026-07-18** | Nat-power functor from model to HIT | Nat recursion and specialized path-map fork | object beta, generator beta, zero/successor and arbitrary Nat agreement active |
| `WEHIT-ROUNDTRIP-NAT` | **completed/promoted 2026-07-18** | encode after power | transparent functions | native Nat-induction proof |
| `WEHIT-ROUNDTRIP-HIT` | **completed/promoted 2026-07-18** | power after encode for arbitrary generated arrow | WalkingWord induction | native free-arrow induction proof; open conversion remains negative |
| `WEHIT-HOM-EQUIV` | **completed/promoted 2026-07-18** | native EQ1 hom equivalence and TypeEquiv view | both round trips | transparent inverse package and computational forward observers active |
| `WEHIT-INITIALITY` | **deferred strengthening** | functor uniqueness/category-of-algebras comparison | Hom round trip and transfor extensionality | concrete free-arrow result does not overclaim full higher functor-category initiality |
| `WEHIT-NONIDENTITY` | **completed/promoted 2026-07-18** | prove loop differs from identity | WalkingWord no-confusion | alleged equality is an Empty inhabitant |
| `WEHIT-NONINVERTIBLE` | **completed/promoted 2026-07-18** | prove loop has no equivalence evidence | constructor composition and EQ1 projections | alleged left inverse law reaches Empty |
| `WEHIT-NONGROUPOIDAL` | **completed diagnostic 2026-07-18** | prove category is not groupoidal | noninvertibility and active groupoidality API | alleged global evidence yields loop evidence then Empty |
| `WEHIT-ONECAT` | **completed/promoted 2026-07-18** | derive ordinary one-category dimension | Nat/WalkingWord sethood | both path homs have `IsDiscreteCat`; both one-object categories have `IsNCat(cat_one,...)` |
| `WEHIT-JOIN-FOLLOWUP` | deferred separate plan | use dependent-HIT pattern to reassess Join elimination | completed walking HIT | new bounded plan; no implementation in this task |
| `WEHIT-GROUPOID-COMPLETION` | deferred separate plan | compare `BNat` with free invertible loop/`BInt` | completed walking HIT | separately reviewed architecture |
| `WEHIT-CONSOLIDATE` | **completed 2026-07-18** | synchronize code, examples, reports, and gates | implemented selected MVP | 1,977-check catalog, 54-target health, warnings/audits, all examples, and full local CI pass |
| `WEHIT-POST-CONSOLIDATE` | **completed 2026-07-18** | stabilize the post-MVP module and report boundary | completed selected MVP | reusable Nat prerequisites extracted; inline assertions centralized with the missing second round-trip negative; 1,978 checks/72 areas and all 55 targets pass; warnings remain kernel/Nat `971/157` and walking `977/157`; audits, health, examples, and 128.448s CI pass |

## Validation And Synchronization Protocol

Implementation follows `AGENTS.md` and the current SOP. In particular:

- inspect staged and unstaged changes separately on every continuation;
- relocate all symbols with `rg` and never rely on report line numbers;
- run a bounded baseline before semantic edits;
- probe every rewrite/unification candidate in an intended-owner-position
  temporary full-file copy;
- use `_` for recoverable inferred LHS slots unless a measured guard is
  documented;
- test both reduction orders for every constructor/projection bridge;
- validate proof-time rules with typed `eq_refl` and retain runtime negative
  controls;
- keep generic `fapp*`, `tapp*`, `piapp*`, and hom-action owners authoritative
  for ordinary functoriality/naturality;
- add one focused sanity assertion for every new rule;
- run `make check` in the inner loop, `make examples` for public milestones,
  and warning/audit/catalog/health/CI gates before substantive handoff;
- synchronize this ledger, the parent H2 row, report index, current status,
  Foundations, examples, catalog, and health report when implementation facts
  change;
- never use `--no-sr-check` for a promoted candidate.

## Completion And Blocker Policy

This report began as a proposed design document. The selected concrete MVP is
now implemented and meets the completion conditions below; that completion
does not include the explicitly deferred generic schema, categorical
initiality, Join follow-up, or groupoid completion.

The directed-HIT implementation is complete only when:

1. the HIT and Nat model remain independently presented;
2. the dependent eliminator, judgmental point beta, and propositional
   generator beta are active;
3. the nondependent recursor is derived from that eliminator;
4. encode and decode retain iterable higher structure;
5. both arbitrary round trips are proved without an earlier Hom-to-Nat rule;
6. the native hom equivalence is packaged;
7. required positive/negative examples and all proportional gates pass;
8. claims about nonidentity, noninvertibility, nongroupoidality, dimension, or
   full initiality are made only when their corresponding rows are discharged.

All eight conditions pass at the selected theorem-first boundary. The plan is
therefore complete for the concrete walking-endomorphism/BNat MVP. Further
work must begin from one of the deferred rows as a new bounded objective
rather than silently strengthening the generator beta or composition normal
forms in this completed slice.

A hard blocker must record:

- the exact desired term, rule, or theorem;
- the smallest failing owner-position probe and retained log;
- whether the failure is typing, subject reduction, normalization,
  nontermination, overlap, performance, representation, extensionality, or
  missing mathematics;
- the precise prerequisite expected to change the result;
- independent dependency-ready work that remains.

The 2026-07-17 checkpoint met this policy for the then-apparent
`WEHIT-COMP-OWNER` blocker. Subsequent probes resolved it by revising the raw
beta requirement and selecting explicit free-arrow induction. The rejected
logs remain decision evidence; they are no longer a terminal blocker.

The generic `PathMap` candidate is not a blocker because the specialized
structured decoder and its Nat-inductive action agreement pass. The reverse
HIT round trip is discharged by explicit free-arrow induction. A future
abstract HIT without native arrow syntax would again need a reusable
extensionality/arrow-induction theorem.

## Future Handoff Requirement

After consolidation, a future handoff should treat this selected concrete MVP
as retained work, not resume the superseded `WEHIT-COMP-OWNER` blocker. A new
bounded plan may select dependent Join elimination, generic directed-HIT
abstraction, generic `PathMap`, categorical initiality, or groupoid completion
toward `BInt`. It must preserve the theorem-first beta boundary and must not
replace the derived Hom comparison by a direct Hom-to-Nat rewrite.
