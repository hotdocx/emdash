# EMDASH v3.2 Walking Endomorphism Directed-HIT And Nat Normal-Form Plan

Date: 2026-07-17
Last reviewed: 2026-07-17
Plan-ID: EMDASH-V3-2-WALKING-ENDOMORPHISM-DIRECTED-HIT-2026-07-17
Depends-On: REPORT_EMDASH_V3_2_EQUALITY_VALUED_OMEGA_EQUIVALENCE_REREDESIGN_PLAN_2026-07-17; REPORT_EMDASH_V3_2_OBSERVATIONAL_EQUALITY_TRUNCATION_UNIVALENCE_REDESIGN_PLAN_2026-07-13; REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26; EMDASH_FOUNDATIONS; emdash3_2.lp; emdash3_2_eq1_hom_action.lp; emdash3_2_eq1_evidence_property.lp; emdash3_2_checks.lp
Supersedes: none
Side-Task-Ledger: #side-task-ledger
Infinity-Codex-Origin: current-session-walking-endomorphism-review-and-user-clarification-2026-07-17
Infinity-Codex-Decision-Responses: infinity-codex:019f6bd3-8405-7d31-8ced-8a6b127c1499:e08b19e4-e4ef-41f3-bee3-87086450d411; infinity-codex:019f6bd3-8405-7d31-8ced-8a6b127c1499:019f7269-46dc-7942-8438-6110fb05cfdb
Status: **adopted; warning-neutral Nat prerequisite slice implemented; selected directed-HIT/BNat MVP blocked on composition-owner coherence**
Review baseline: `394cf3bc369ddcdb4da74aaf5fdc0557de515532`
Implementation baseline: `8fd9bdfac53b018b77f20ecec24f85efe44febc9`
Parent plan: `REPORT_EMDASH_V3_2_EQUALITY_VALUED_OMEGA_EQUIVALENCE_REREDESIGN_PLAN_2026-07-17.md`, especially deferred task `EVOGJ-H2-READINESS`
Current implementation owner: `emdash3_2_walking_end_hit.lp`

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

## Implementation Checkpoint And Hard Blocker

The plan was adopted on 2026-07-17. One independent prerequisite slice is
promoted in `emdash3_2_walking_end_hit.lp`:

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

The selected directed-HIT MVP is **not** complete. Two early computational
gates independently expose the same missing composition-owner architecture.

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

Until one of these prerequisites is implemented, `WalkingEnd_cat`, its beta
rules, `BNat_cat`, encode/decode, and the round trips remain unpromoted. The
ignored full-file probes and logs are evidence only. No Hom-to-Nat rewrite,
bodyless round trip, or 18-rule patch family has been installed.

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
3. runtime constructor computation at the selected base and loop owners;
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

The active kernel does **not** currently provide the following. The first
implementation checkpoint now supplies Nat addition and Nat sethood in the
one-way walking-plan extension rather than moving them into the kernel:

- a general functor constructor
  `Path_cat(A) -> Path_cat(B)` from a raw function and its higher action;
- a dependent eliminator or semantic initiality theorem for `Join_cat`;
- a generic directed-HIT schema;
- the walking endomorphism or its universal property.

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

The required constructor computations are:

```text
walking_end_ind_sec(D,u,ell_D)[base]
  -> u

walking_end_ind_sec(D,u,ell_D)[loop]
  -> ell_D.
```

The first observation is through `piapp0`; the second is through
`piapp1_fapp0`. Both are intended runtime constructor betas at their semantic
projection owners. A proof-time comparison can be used temporarily to
diagnose a projection-order join, but a final implementation that only states
both betas propositionally must not claim the selected computational HIT
milestone without an explicit revised acceptance decision.

Mathematically there is no extra relation on the generator, so no independent
algebra law should be requested from the user. Computationally, the first
owner-position probes showed that a section declaration plus one generator
beta is not enough: the implementation still needs an internal arrow-
induction/composition owner making the generated identity/composite actions
join with generic strict functoriality. That missing computation is an
implementation prerequisite, not additional mathematical constructor data.

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
walking_end_rec_func(C,x,f)[loop] -> f.
```

The readable recursor must route through the dependent eliminator; it must not
be an independent primitive with duplicate semantic authority.

### 4. Initiality and uniqueness

At object level, functors out of the HIT should be determined by an object and
an endomorphism. The full categorical universal property is more accurately
an equivalence between `Functor_cat(WalkingEnd_cat,C)` and a category of
endomorphism objects whose arrows are intertwiners, not merely the informal
classifier `Sigma x, Hom_C(x,x)`.

The initial operational milestone need not construct that entire category
equivalence, but it must derive enough eta/uniqueness from dependent
elimination to prove the reverse Nat round trip. If two functors out of
`WalkingEnd_cat` agree on `base` and `loop`, the implementation needs a
derived equality/transfor or another structured induction principle strong
enough to compare their action on every generated arrow.

If the proposed dependent eliminator cannot derive this, that is evidence
that the HIT interface is incomplete. The response is to refine the
eliminator/eta interface or document the exact extensionality prerequisite,
not to postulate the desired reverse round trip as a standalone capability.

Three existing-architecture proof presentations should be assessed before
adding new infrastructure:

1. a displayed logical-relation motive over `WalkingEnd_cat`, discharged by
   `walking_end_ind_sec`;
2. a transfor between the endofunctors
   `walking_decode_func o walking_encode_func` and `id_func`, generated from
   their agreement on the base and loop;
3. a structured motive over `PathOut_cat(WalkingEnd_cat,base)` whose objects
   are arbitrary outgoing arrows and whose target property is the desired
   arrow round trip.

These are alternative presentations of the same freeness argument. Prefer
the one that reuses current `Catd`, section, transfor, and `PathOut` owners
with the least new trusted computation.

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
comp_(BNat_cat)(n,m)           -> nat_add(m,n)
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

Required computation includes:

```text
walking_encode(id)          -> zero
walking_encode(loop)        -> succ(zero)
walking_encode(g o f)       -> nat_add(walking_encode(f),walking_encode(g))
```

The identity and composition equations should be inherited from generic
strict functoriality plus the selected `BNat_cat` normal form. Do not add
duplicated encode-specific preservation rules unless a measured projection
order erases the generic owner.

### 2. Decoding Nat normal forms

Define powers transparently by Nat recursion:

```text
walking_power(zero)   := id
walking_power(succ n) := loop o walking_power(n)
```

with the exact composition orientation synchronized with `nat_add`.

The comparison ideally packages this as:

```text
walking_decode_func : Functor(BNat_cat,WalkingEnd_cat),
```

whose arrow action is `walking_power`. A capped raw function is insufficient
for the final result because the functor must remain iterable at higher homs.

### 3. Round trips

The easy round trip should be derived by Nat induction:

```text
walking_encode(walking_power(n)) = n.
```

The decisive HIT round trip is:

```text
walking_power(walking_encode(p)) = p
```

for arbitrary

```text
p : Hom(WalkingEnd_cat,base,base).
```

This proof must materially use the HIT eliminator, its derived eta/initiality,
or a structured induction theorem obtained from it. A direct global axiom,
an opaque round-trip theorem with no body, or a hom-to-Nat rewrite inserted
before the proof does not satisfy the plan.

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

### Architecture fork

Probe, in this order:

1. a generic semantic `path_map_func(f)` whose higher action recursively uses
   the existing `eq_ap` hierarchy and preserves the generic composition head;
2. a stable selected-action head with an explicit higher-action story and a
   theorem relating its first projection to `ObsAction`;
3. a specialized `bnat_power_func` or Nat-discreteness construction if the
   general constructor is disproportionate to the first HIT comparison.

Selection criteria are:

- full `fapp1_func` iterability, not merely capped action;
- identity and composition joining at the first two hom levels;
- no opaque higher-action capability;
- no assumption that proof-time comparison is transitively propagated;
- no forced replacement of the real Nat/PathRecord `ObsAction` consumers;
- a public API reusable by later standard-library constructions.

The generic path-map constructor is therefore a **comparison-phase
prerequisite candidate**, not a prerequisite to declaring the HIT or its
dependent eliminator. If the generic candidate fails, a specialized derived
functor is an acceptable bounded alternative provided its higher action is
honest and the report records why it cannot yet be generalized.

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

### Direct addition versus a stable composition head

Two operational candidates remain open:

```text
comp_fapp0(BNat_cat,g,f) -> nat_add(f,g)
```

or

```text
comp_fapp0(BNat_cat,g,f) -> bnat_comp(g,f)
bnat_comp(g,f)           -> selected nat_add normal form.
```

The SOP preference is semantic definition before primitive head. Select the
stable intermediary only if owner-position evidence shows that direct
exposure of addition loses a necessary category/functor projection or creates
a nonjoining critical pair.

The focused probe must test both reduction orders for:

- `g o id` and `id o f` against the generic unit rewrites;
- triple composition against the generic proof-time associativity equation;
- opposite composition;
- the action of an arbitrary functor out of `BNat_cat`;
- visible `hom_postcomp_fapp0` and `hom_precomp_along_fapp0` consumers;
- open Nat terms, not only closed numerals.

Write recoverable inferred LHS category/endpoints as `_` unless a measured
subject-reduction or performance guard requires otherwise. Validate any
`unif_rule` with typed `eq_refl`, retain runtime negative controls, and never
use a proof-time equation as if it were a runtime Nat normal form.

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

The likely public surface is:

```text
WalkingEnd_cat
walking_base
walking_loop
walking_end_ind_sec
walking_end_rec_func

BNat_cat
bnat_obj
bnat_generator
nat_add
walking_power
walking_encode_func
walking_decode_func
walking_hom_nat_equiv_EQ1.
```

Names are provisional and must be checked against the current catalog before
promotion. Prefer "walking endomorphism" or `BNat` over "directed Circle" in
the public API, because the latter suggests an invertible topological loop.

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
7. Record whether runtime beta is feasible at both constructor projections.

Exit criterion: the dependent eliminator signature typechecks in isolation,
both proposed projection owners are identified, and no opaque theorem has
been added to simulate a failed beta.

### Phase 1: Nat monoid and discreteness prerequisites — completed

1. Define selected Nat addition transparently.
2. Add computation diagnostics for both constructors and open terms.
3. Derive unit and associativity statements needed by the category model.
4. Prove `IsSetGrpd Nat_grpd`.
5. Expose only the minimal reusable arithmetic/truncation API required by the
   comparison.

Exit criterion: Nat addition computes, its laws are derived without global
proof erasure, and Nat sethood is an internal term.

### Phase 2: transparent `BNat_cat` model — blocked on composition registration

1. Add the one-object category and object/hom projections.
2. Select direct-addition or stable-composition ownership from focused probes.
3. Add identity, generator, and composition computation.
4. Test both generic-unit orders, associativity, opposite, functor action,
   postcomposition, and precomposition consumers.
5. Derive local discreteness/one-category evidence where current closure
   theorems suffice.

Exit criterion: `BNat_cat` is a coherent computational category model with
Nat arrow normal forms, an explicitly recorded generic higher-composition
owner, and no category-specific duplication of generic hom actions. Full
comparison with selected Nat path action remains Phase 4 work.

### Phase 3: HIT constructors and dependent eliminator — blocked after local beta

1. Add `WalkingEnd_cat`, `walking_base`, and `walking_loop` without a Hom-to-
   Nat rule.
2. Add the single dependent eliminator owner returning a `Pi_cat` section.
3. Promote base and loop projection betas after owner-position critical-pair
   checks.
4. Add negative controls showing that no object eta, loop identity, inverse,
   or Nat hom classification is silently available.
5. Derive the constant-motive recursor through the eliminator.

Exit criterion: the actual HIT constructors, dependent elimination, both
runtime constructor betas, and derived recursor are executable. A primitive
nondependent recursor alone does not meet this phase.

### Phase 4: path-map/higher-action fork — downstream blocked

1. Probe the generic `Path_cat` functor constructor and its first two hom
   actions.
2. Test identity and composition in both reduction orders.
3. Determine the precise relationship with semantic `eq_ap` and retained
   `ObsAction`; do not claim full registry subsumption from one projection.
4. If the generic route is unstable or disproportionate, implement the
   smallest honest specialized higher-action owner needed for
   `walking_decode_func` and record the generalization gate.

Exit criterion: a reusable generic path-map functor or a documented
specialized alternative supplies the full iterable action needed by the
comparison, with no opaque higher-action capability.

### Phase 5: encode, powers, and decode — downstream blocked

1. Derive `walking_encode_func` from the HIT recursor.
2. Define `walking_power` by Nat recursion.
3. Package powers as `walking_decode_func` through the selected Phase-4
   architecture.
4. Check identity, generator, successor/power, and composition formulas.
5. Preserve generic functoriality as the owner of encode/decode preservation.

Exit criterion: both comparison directions are iterable functors or otherwise
have an explicitly equivalent structured presentation; capped functions alone
are not the final boundary.

### Phase 6: round trips and hom equivalence — downstream blocked

1. Prove encode-after-power by Nat induction.
2. Derive power-after-encode for arbitrary HIT arrows from dependent
   elimination/eta/initiality.
3. Probe the displayed-logical-relation, endofunctor-transfor, and structured
   `PathOut` presentations before selecting a new owner.
4. If the second proof exposes missing functor/transfor extensionality, isolate
   and implement the smallest reusable theorem rather than assuming the
   round trip.
5. Package the hom equivalence in native EQ1 form and derive the optional
   `TypeEquiv` view.
6. Add closed and open computational examples.

Exit criterion: both arbitrary round trips have transparent bodies, the hom
equivalence is active, and no prior Hom-to-Nat rewrite made either theorem
tautological.

### Phase 7: initiality, univalence, and dimension consumers — downstream blocked

1. State the strongest derived functor uniqueness/eta theorem supported by
   Phase 6.
2. If feasible, package the category-level equivalence with `BNat_cat` or the
   category of endomorphism algebras.
3. Prove loop nonidentity, loop noninvertibility, and category
   nongroupoidality.
4. Check object-level univalence/core behavior.
5. Derive OneCat/local-discreteness evidence or record the exact missing
   equivalence-invariance theorem.

Exit criterion: the example is a meaningful consumer of the equality-valued
omega-equivalence design and does not collapse directed arrows into paths.

### Phase 8: consolidation and next-scope decision — blocked checkpoint complete

1. Synchronize active code, checks, reviewer example, Foundations, current
   status, this ledger, report index, catalog, and health report.
2. Run warning summary, strict LHS audit, examples, catalog, health, and CI.
3. Decide whether the next bounded objective is dependent Join elimination,
   a generic directed-HIT schema, groupoid completion toward `BInt`, or
   continued deferral.
4. Do not begin the next objective in the same semantic migration.

Exit criterion: all promoted claims have executable evidence and every
remaining gap has an exact owner/prerequisite.

## Recommended First Implementation Slice

Checkpoint result: steps 1--5 pass in isolation, but step 6 exposes the
composition blocker described above. The candidate HIT rules were therefore
not promoted. Independent Nat prerequisites were promoted while the required
composition owner remains open.

The first implementation slice should be deliberately smaller than the full
model:

1. owner-position probe of the exact dependent eliminator type;
2. temporary `WalkingEnd_cat`, base, and loop symbols with no Hom rules;
3. `walking_end_ind_sec` returning `Pi_cat D`;
4. base projection beta through `piapp0`;
5. loop projection beta through `piapp1_fapp0`;
6. constant-motive derived recursor and its two constructor computations;
7. negative assertions that the hom does not reduce to Nat and the loop does
   not reduce to identity;
8. warning/LHS comparison and bounded active check.

This slice answers the most important feasibility question first: whether the
current `Catd`/section/action kernel can host a computational dependent
eliminator for a genuine directed arrow constructor. Nat arithmetic,
`BNat_cat`, and `PathMap` should not be used to conceal a failure at this
boundary.

## Probe And Diagnostic Matrix

| Area | Positive requirement | Negative/control requirement |
| --- | --- | --- |
| HIT formation | base and loop typecheck | no Hom-to-Nat conversion |
| dependent motive | loop lift has exact `D[loop](u) -> u` endpoint | raw family is not silently accepted as `Catd` |
| base beta | `piapp0(ind,base)` computes to `u` | unrelated section projection does not fold |
| loop beta | `piapp1_fapp0(ind,loop)` computes to supplied lift | arbitrary arrow action does not fold to loop lift |
| recursor | constant motive yields `Functor(W,C)` | no independent primitive recursor body |
| Nat model | id/loop/comp expose 0/1/addition | open terms do not collapse by commutativity |
| category units | both generic/category-specific orders join | no duplicate global unit rule |
| associativity | typed generic associativity survives Nat exposure | no claim that proof-time firing is runtime normalization |
| path map | first two hom actions are iterable | capped `eq_ap` alone is not called a functor package |
| encode | id/loop/comp compute | no encode-specific duplicate functor laws |
| decode | zero/successor powers compute | no opaque higher-action field |
| round trips | both arbitrary directions have bodies | no prior Hom rewrite or bodyless theorem |
| nonidentity | encoded loop/identity equality reaches Empty | loop is not declared unequal axiomatically |
| nongroupoidality | alleged evidence yields Empty | absence of constructor alone is not a proof |
| Join relation | dependency remains one-way/conceptual | no claim `Join(Unit,Unit)=WalkingEnd` |

## Feasibility Assessment

| Deliverable | Mathematical feasibility | Current computational feasibility | Assessment |
| --- | --- | --- | --- |
| Nat addition and powers | standard | `nat_add` and associativity promoted; powers remain downstream | high; addition complete |
| `Nat_grpd` sethood | standard | nested native Nat induction now supplies an internal term | complete |
| transparent `BNat_cat` | standard one-object monoid category | direct composition exposure creates 18 new unjoinable generic-owner pairs | blocked pending reusable composition registration |
| dependent eliminator formation | standard induction principle for the free category | exact `Catd`/`Pi_cat` signature passes | formation high; not promoted alone |
| base constructor beta | standard | stable terminal-component owner passes locally | locally high; global HIT slice blocked |
| loop constructor beta | standard | individual stable owner passes, but its composite action does not join | blocked pending arrow-induction/composition owner |
| derived constant recursor | standard | type comparison and constructor observers pass separately; generator square does not | blocked with dependent owner |
| generic `PathMap` | standard functorial action of functions on paths | recursive higher action and generic composition diamonds are unresolved | medium |
| specialized power functor | standard monoid functor | can use Nat discreteness if generic PathMap is deferred | medium-high |
| encode-after-decode | Nat induction | ordinary eliminator computation | high |
| decode-after-encode | freeness/initiality | depends on adequacy of dependent eliminator and functor/transfor eta | medium; central gate |
| native hom equivalence | follows from round trips | active equality-valued inverse packaging exists | high after round trips |
| loop noninvertibility | elementary Nat argument | native inverse-law projections plus no-confusion available | medium-high after equivalence |
| nongroupoidality | follows immediately | active `IsGroupoidalCat_EQ1` consumer exposes loop evidence | medium-high after noninvertibility |
| full functor-category initiality | classical | requires an endomorphism-algebra category and coherent extensionality | medium/low; strengthening |
| generic directed-HIT schema | mathematically plausible | beyond one constructor and current Join staging | deferred research/architecture |

Overall, the mathematical target remains sound, but the initially proposed
"small natural extension" is not computationally feasible in the current
rewrite orientation without one additional reusable architecture component.
The blocker occurs earlier than the anticipated reverse arbitrary-arrow round
trip: constructor beta already fails to join at the square of the generator,
and the independent Nat model loses generic higher-action owners when its
composition reduces directly to addition. Nat arithmetic and sethood are
complete; all claims beyond them remain conditional on the explicit
free-arrow/composition prerequisite recorded above.

## Risks And Mitigations

### Risk 1: the Nat model is mistaken for the HIT

Mitigation: keep `WalkingEnd_cat` and `BNat_cat` distinct until encode/decode
and both round trips are derived. Retain a negative Hom-conversion assertion.

### Risk 2: a primitive recursor is presented as dependent induction

Mitigation: the primary owner returns a section for arbitrary structured
`Catd` motives and consumes a displayed loop lift. The nondependent recursor
must be a constant-motive specialization.

### Risk 3: beta is only stated propositionally

Mitigation: require runtime base and loop constructor betas at selected
projection owners for the computational HIT milestone. Record any revised
boundary explicitly rather than silently weakening the claim.

### Risk 4: functor uniqueness is assumed

Mitigation: make the reverse Nat round trip an acceptance gate. If current
dependent elimination cannot derive it, add a principled eta/extensionality
interface or report the missing theorem.

### Risk 5: one `ObsAction` is mistaken for an omega-functor

Mitigation: test `fapp1_func` at two levels and require an explicit recursive
higher-action account. Preserve existing registry consumers until a genuine
replacement exists.

### Risk 6: category-specific composition duplicates hom-action owners

Mitigation: define only `comp_fapp0(BNat_cat)` computation first. Treat
post/precomposition as consumers of generic actions and add no duplicate rules
without measured projection evidence.

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
| `WEHIT-IND-SHAPE` | **blocked after local pass 2026-07-17** | type exact `Catd` motive, loop lift, section result, and projection betas | adoption | exact signature and individual stable betas pass warning-neutral; constant-family generator-square composition fails to join (`...-213738.log`) |
| `WEHIT-NAT-ADD` | **completed/promoted 2026-07-17** | transparent Nat monoid operations and laws | adoption | constructor/open unit computation and transparent associativity active with no warning/audit delta |
| `WEHIT-NAT-SET` | **completed/promoted 2026-07-17** | internal `IsSetGrpd Nat_grpd` proof | Nat equality/truncation kernel | nested Nat-induction proof, permanent diagnostics, and reviewer example pass |
| `WEHIT-COMP-OWNER` | **hard prerequisite; open** | reusable free-arrow/category-specific composition registration that preserves all generic action owners | measured HIT and BNat failures | either an explicit non-Nat `WalkingWord` induction/eta interface or a generic kernel registration passes owner-position action/comp tests without bridge proliferation |
| `WEHIT-BNAT-MODEL` | **blocked 2026-07-17** | separate transparent one-object Nat category | Nat addition/sethood and `WEHIT-COMP-OWNER` | direct composition-to-addition typechecks but adds 18 unjoinable critical pairs (`...-214757.log`); candidate not promoted |
| `WEHIT-HIT-INTRO` | **not promoted; blocked** | add opaque HIT category, base, and directed loop | induction-shape probe and `WEHIT-COMP-OWNER` | declarations alone would not justify the computational HIT claim |
| `WEHIT-HIT-IND` | **blocked 2026-07-17** | dependent eliminator and base/loop runtime beta | HIT introductions and `WEHIT-COMP-OWNER` | local betas pass, but composed loop action has distinct normal forms; no active rule retained |
| `WEHIT-REC` | **blocked 2026-07-17** | derive nondependent recursor from constant motive | dependent eliminator and `WEHIT-COMP-OWNER` | type and isolated observers pass; narrow adapter fails composition; recursive action creates `999/158` warning inventory |
| `WEHIT-PATH-MAP` | downstream blocked architecture fork | reusable path-category map or honest specialized substitute | Nat model, comparison consumer, and `WEHIT-COMP-OWNER` | two-level iterability and identity/composition joins select implementation |
| `WEHIT-ENCODE` | downstream blocked | recursor-derived functor from HIT to Nat model | recursor and `BNat_cat` | base/loop/comp computations pass |
| `WEHIT-DECODE` | downstream blocked | Nat-power functor from model to HIT | Nat recursion and path-map fork | zero/successor/higher action pass |
| `WEHIT-ROUNDTRIP-NAT` | downstream blocked | encode after power | encode/decode | transparent Nat-induction proof |
| `WEHIT-ROUNDTRIP-HIT` | downstream central gate | power after encode for arbitrary HIT arrow | dependent elimination/eta | derived proof passes or exact extensionality prerequisite recorded |
| `WEHIT-HOM-EQUIV` | downstream blocked | native EQ1 hom equivalence and TypeEquiv view | both round trips | package observers and maps compute |
| `WEHIT-INITIALITY` | strengthening | functor uniqueness/category-of-algebras comparison | HIT round trip and transfor extensionality | strongest coherent theorem supported by active kernel |
| `WEHIT-NONIDENTITY` | auxiliary | prove loop differs from identity | hom equivalence | alleged equality maps to Empty |
| `WEHIT-NONINVERTIBLE` | auxiliary | prove loop has no equivalence evidence | encode and Nat laws | alleged inverse law maps to successor/zero contradiction |
| `WEHIT-NONGROUPOIDAL` | auxiliary | prove category is not groupoidal | noninvertibility and active groupoidality API | alleged global evidence yields loop evidence then Empty |
| `WEHIT-ONECAT` | auxiliary | derive ordinary one-category dimension | Nat sethood/hom equivalence | active closure/invariance theorem suffices or reusable gap recorded |
| `WEHIT-JOIN-FOLLOWUP` | deferred separate plan | use dependent-HIT pattern to reassess Join elimination | completed walking HIT | new bounded plan; no implementation in this task |
| `WEHIT-GROUPOID-COMPLETION` | deferred separate plan | compare `BNat` with free invertible loop/`BInt` | completed walking HIT | separately reviewed architecture |
| `WEHIT-CONSOLIDATE` | **completed at blocked checkpoint 2026-07-17** | synchronize code, examples, reports, and gates | retained Nat slice and blocker evidence | only warning-neutral retained work promoted; 53-file health, 1,931-check catalog, examples, and full CI pass; blocker remains explicit |

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

This report is complete as a first proposed design document when its target,
architecture fork, phases, acceptance criteria, and trust boundaries are
reviewable. That does not make the implementation complete.

The directed-HIT implementation is complete only when:

1. the HIT and Nat model remain independently presented;
2. the dependent eliminator and both constructor betas are active;
3. the nondependent recursor is derived from that eliminator;
4. encode and decode retain iterable higher structure;
5. both arbitrary round trips are proved without an earlier Hom-to-Nat rule;
6. the native hom equivalence is packaged;
7. required positive/negative examples and all proportional gates pass;
8. claims about nonidentity, noninvertibility, nongroupoidality, dimension, or
   full initiality are made only when their corresponding rows are discharged.

A hard blocker must record:

- the exact desired term, rule, or theorem;
- the smallest failing owner-position probe and retained log;
- whether the failure is typing, subject reduction, normalization,
  nontermination, overlap, performance, representation, extensionality, or
  missing mathematics;
- the precise prerequisite expected to change the result;
- independent dependency-ready work that remains.

The 2026-07-17 checkpoint meets this policy for `WEHIT-COMP-OWNER`: it records
the exact constant-family generator-square and `BNat_cat` rules, the smallest
failing owner-position logs, the normalization/overlap classification, the
free-arrow or generic composition-registration prerequisite, and the
independent Nat work that was completed and promoted. Consequently the task
is at a documented hard-blocker terminal condition, not at the plan's full
directed-HIT completion condition.

Failure of the generic `PathMap` candidate is not automatically a blocker:
the specialized Nat-discrete alternative must also be assessed. Failure of
the reverse HIT round trip after the intended dependent eliminator is more
fundamental; it blocks the Nat-correspondence completion claim until the
eliminator/eta interface is strengthened or a reusable extensionality theorem
is established.

## Future Handoff Requirement

An implementation handoff should name this report as the living bounded plan
and the completed July 17 equality-valued overlay as its parent authority. It
should resume at `WEHIT-COMP-OWNER`, using the retained eliminator-shape and
`BNat_cat` probes as acceptance tests; it should not redeclare the Nat hom
model, directly promote the locally passing loop beta, or start the Circle.
The plan remains revisable: owner-position evidence may change rule
orientation, module placement, or the selected path-map fork, but must not
weaken the actual dependent-elimination and derived-correspondence goal
without an explicit recorded decision.
