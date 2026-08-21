---
title: Functorial Type Theory: An Executable Architecture for Directed Dependency
authors: The emdash contributors
edition: overview research article
status: research draft
date: 2026-08-21
---

> **Research-draft status.** This article describes the checked emdash v3.2
> development and a bounded TypeScript reviewer. It is not a released
> foundation, a venue submission, or a claim that the full research programme
> is complete. The active Lambdapi sources remain the mathematical authority.

# Abstract

Dependent type theory makes substitution computational. Category theory makes
variation along arrows explicit. **Functorial Type Theory** asks what happens
when both principles inhabit one language: variables may range over objects
and arrows, dependent families carry transport, and functoriality and
naturality are internal operations that can normalize rather than external
proof obligations.

Emdash is an executable investigation of this idea. Its active Lambdapi
development contains an autonomous categorical or directed dependent type
theory of categories, Cat-valued families, reindexing, total categories,
section categories, dependent homs, functors, and transfors. Lambdapi's
dependent $\\lambda\\Pi$ framework supplies a complementary outer logical
layer. A small TypeScript implementation mirrors this separation: an explicit
locally nameless dependent Core checks and evaluates terms, while a typed
categorical frontend compiles usable binder notation to existing internal
categorical owners, and bounded typed declarations expand into ordinary
logical-framework declarations and rules.

Five computations summarize the architecture. First, for
$p:x\\to y$ and $q:y\\to z$, emdash forms the outgoing-arrow category

$$
\\mathrm{PathOut}_Z(x)
  = \\Sigma_{y:Z}\\,\\mathrm{Hom}_Z(x,y)
$$

and a canonical arrow
$\\rho_{x,y,p}:(x,\\mathrm{id}_x)\\to(y,p)$. Transporting a motive along
$\\rho$ gives a synthetic arrow-induction principle. Applied to the
representable composition motive, its checked normal form is $q\\circ p$.
Second, for a ring map out of $R$, the condition that $f\\in R$ becomes
invertible defines an ordinary sieve $D_R(f)$ before any representing open is
chosen. A supplied localization represents that sieve pointwise, finite
unit-ideal families generate the big Zariski topology, and a separate direct
cover completion constructs a Cat-valued sheafification reflector from
return, cover-indexed glue, and silent coherence. Third, localizing natural
numbers along successor gives an integer line, and an opaque groupoidal
Circle HIT carries a universal Integer cover. Encode/decode proves
$\mathrm{Hom}_{S^1}(\mathsf{base},\mathsf{base})\simeq\mathbb Z$; the directed
walking endomorphism maps to the Circle by the nonnegative inclusion, while
product paths admit both coherent sequential transport factorizations. More
generally, $\mathsf{Groupoidify}(C)$ is characterized by a whole equivalence
between groupoidal maps out and path-valued functors on $C$. A selected
strict-object/lax-arrow Gray closure then recovers a nonidentity walking-square
interchanger from the same internal laxity action. Fourth, face codes and
directed join supply ordinal simplexes, while iterated outgoing paths give
their dependent cells. One Nat recursion constructs their canonical source in
variable dimension, with faces and higher action checked through dimension
four. Fifth, the TypeScript
frontend accepts ordinary, natural, displayed-functorial, and
displayed-natural abstractions. It recursively factors variable occurrences
through weakening, pairing, evaluation, reindexing, totalization, and
internal action owners, then emits backend-neutral explicit Core. The same
checker accepts the result at object and arrow level; unsupported
factorizations fail closed.

The result is a working research artifact rather than a completed proof
assistant. It demonstrates a coherent design across mathematical kernel,
dependent logical framework, elaboration, checked computation, and a
client-side reviewer. Arbitrary dependency and variance graphs, whole-library
transfer, systematic groupoidal closure for every former, source-functorial
adjunction packaging for groupoidification, full Gray monoidality, a
commutative-ring lift and left-exactness theorem for constructed
sheafification, representation-independent schemes, and global metatheory
remain explicit research boundaries.

# 1. Why Categorical Variables Should Compute

In ordinary dependent type theory, a bound variable may occur anywhere in a
term, and the elaborator reconstructs applications and substitutions from
local typing information. In ordinary category-theoretic prose, the same
convenience is assumed for a richer notion of variable. A symbol may denote an
object, an arrow, a functor, or a natural family; an expression such as
$F(x)$ silently invokes the appropriate object or arrow action. Naturality is
usually discharged by saying that a construction is "functorial in $x$."

That phrase conceals an implementation choice. One can represent a
construction as a pointwise function plus externally supplied equations, or
one can represent it by an internal functorial object whose action and higher
action are already part of the term. Emdash chooses the latter whenever a
stable categorical construction is available. The aim is not to attach a
naturality proof to every pointwise definition. It is to elaborate readable
syntax into compositions of internal owners for which naturality follows from
the type and generic action calculus.

This makes normalization do mathematical work. A composite of represented-hom
actions is a cut; a rewrite that contracts it is cut elimination. A
transformation component is not merely a projection from an opaque proof of
naturality; it is an observable rung of an iterable hom tower. A dependent
total arrow is not only a pair of endpoints; it contains a base arrow and a
fibre arrow above transport.

The project therefore uses *dependent type theory* in two complementary
senses.

1. An **outer dependent logical framework** supplies $\\Pi$-types,
   $\\lambda$-abstraction, application, definitions, and conversion. Lambdapi
   provides this layer for the authoritative development. The TypeScript Core
   implements a bounded counterpart with dependent checking and
   $\\beta/\\delta$ computation.
2. An **inner categorical or directed dependent type theory** treats a
   category as a context or shape and a Cat-valued functor as a dependent
   category over it. Reindexing is substitution, a total category is
   dependent sum, a section category is dependent product, and dependent hom
   records transport over a directed base arrow.

Neither layer replaces the other. The outer framework hosts the inner
calculus; the inner calculus gives computational meaning to variables whose
variation is genuinely categorical. The current groupoidal/type-theoretic
universe supplies equality, J, dependent pairs, and dependent products as
well. A checked Circle/Integer encode--decode theorem and representative
product-transport closure connect these layers. Category-indexed
groupoidification now adds the target-side universal mapping property, while
its source action and packaged adjunction—and systematic closure for every
former—remain later work.

The same order of construction extends beyond binder syntax. A local
condition should first be stable under every change of stage; only afterward
should one ask whether one object represents all successful probes. Thus the
condition that a section becomes invertible is first an ordinary sieve. In
affine geometry a localization may represent it, and finite families of such
charts may generate a topology. Likewise, sheafhood is first a property of
restriction from whole sections to whole matching families; a sheafification
reflector is a further construction. These distinctions let categorical
semantics carry computation without importing an abstract modal layer or
silently assuming the classical existence theorems suggested by familiar
notation.

The central claim of this overview is deliberately narrower than a
foundational completeness theorem:

> A substantial directed dependent calculus, a sieve-to-sheafification
> application, a computational groupoidal-realization slice, a minimal outer
> dependent framework, and a recursive categorical-binder frontend already
> compose into one executable architecture.

The rest of the paper makes that claim concrete. Sections 2 and 3 describe the
two layers and the directed dependent constructors. Sections 4 and 5 derive
synthetic arrow induction and its composition normal form. Section 6 explains
how ordinary and displayed categorical binders compile. Section 7 follows the
result through explicit Core to the browser artifact. Sections 8 and 9 state
the local-to-global geometric application, free groupoidal realization, and
the broader programme's present limits.

# 2. A Two-Layer Executable Architecture

The authoritative implementation is a Lambdapi signature. It declares the
categorical owners and orients selected structural equations as rewrite rules.
Proof-time unification rules relate useful presentations when neither should
become the runtime normal form. Executable assertions in a separate checks
module exercise formation, reduction, comparison, and non-collapse cases.

The TypeScript implementation is not a second mathematical authority. It is a
small product kernel and elaboration target whose vocabulary is aligned with
reviewed Lambdapi owners. Its trusted representation is explicit Core:
applications have visible spines, binders are locally nameless, plicity and
variation metadata are retained, and terms can be traversed, frozen,
serialized, and compared structurally. A one-shot scoped builder restores
HOAS-like authoring ergonomics without storing JavaScript closures in Core.

The two input paths meet at one generic checker:

| Input | Deterministic expansion before checking |
| --- | --- |
| text or typed TypeScript terms | contextual occurrence analysis, typed categorical wiring, and backend-neutral explicit emdash Core |
| typed host declarations | validated expansion to ordinary LF declarations and rules |

Both paths are consumed by the small TypeScript dependent-LF checker and
bounded evaluator. Selected judgments may then be emitted to Lambdapi as a
deterministic conformance oracle; the active Lambdapi v3.2 source remains the
mathematical authority.

The outer TypeScript LF includes dependent $\\Pi$, annotated
$\\lambda$-terms, application, contextual metavariables, transparent
definitions, and bounded $\\beta/\\delta$ conversion. It deliberately rejects
`Type : Type`; object theories use decoded codes in the same style as the
Lambdapi development. The categorical layer does not add a new checker for
each owner. Reviewed declarations and runtime or proof-time rules are compiled
into the generic environment, after which ordinary LF inference, checking,
conversion, and rewriting process the term.

The declaration branch removes repetition in the outer framework rather than
adding categorical semantics. One convenience packages already typed
adjunction data, or a counit and whole hom transpose, as an indexed assumption
with proof-time agreements. A second expands one unparameterized,
nonrecursive, single-constructor dependent structure into an opaque carrier,
constructor, primitive projections, and ordered projection beta rules. Both
forms disappear before ordinary Core checking. Neither adds a trusted term
node, a runtime alias, general record eta or elimination, or a new Lambdapi
owner.

## 2.1 The outer dependent LF

The outer Core has only the generic syntax needed to host object theories:
sorts, free and bound variables, dependent products, lambdas, applications,
metavariables, and owner calls. A dependent product stores the domain and a
body under one binder. A lambda stores the same binder information and an
explicit body. Bound occurrences use indices, so alpha-equivalence is
structural and substitution is a total traversal rather than an invocation of
an opaque host-language function.

Inference and checking are bidirectional. A free owner is looked up in the
candidate environment; a call consumes its dependent product spine,
instantiating each codomain with the checked argument. A lambda is normally
checked against an expected product. An annotated lambda can also infer a
product, which is useful for direct construction and diagnostics. Implicit
parameters remain visible in Core even when a surface builder inserts them.

Conversion is deliberately bounded and evidence-producing. Weak-head
$\\beta$ instantiates a lambda body and preserves any remaining application
spine. Authorized transparent declarations unfold by $\\delta$ only after
their bodies have been checked against their declared types and their
dependency order has been validated. Metavariables are zonked before rigid
comparison, and Miller-pattern constraints are revisited as information
arrives. One shared budget prevents a conversion query from hiding an
unbounded reduction path; traces record whether progress came from
$\\beta$, $\\delta$, metavariable resolution, or a reviewed categorical
runtime rule.

This is enough to call the layer a minimal dependent logical framework, but
not enough to claim a new general-purpose foundation. It does not implement
an unrestricted user rewrite language, assume $\\mathrm{Type}:\\mathrm{Type}$,
or silently treat every declaration as transparent. Those exclusions are
part of the trusted boundary. The original TypeScript prototype had more
globally mutable conveniences, including holes, rewriting, and HOAS storage;
the renewed Core keeps the reusable algorithms while replacing global
authority and opaque binder bodies with explicit, profile-scoped data.

The scoped builder reconciles the explicit representation with an ergonomic
API:

```text
pi("x", A, x => B(x))
lam("x", A, x => body(x))
let_("x", value, x => body(x))
```

Each callback runs once. Its token is valid only during lowering and becomes a
bound index immediately. A foreign or escaped token is rejected. Thus the
authoring surface can look higher-order while the term that enters checking is
first-order, deterministic, and serializable.

## 2.2 Semantic owners and transfer

The inner theory enters TypeScript through a typed immutable transfer
representation. A declaration records its qualified owner, binder telescope,
result, visibility, optional body, and source evidence. Runtime rules and
proof-time comparisons are separate data classes. A policy overlay decides
which reviewed items are executable in a candidate profile; it is not inferred
merely because a Lambdapi symbol can be named.

That distinction mirrors the mathematical source. An opaque declaration
extends typing but cannot unfold. A transparent definition participates in
$\\delta$ conversion. A runtime rule selects an operational normal form. A
proof-time rule assists a rigid comparison without orienting runtime
evaluation. Compiled module interfaces preserve public, protected, and private
visibility rather than flattening every source declaration into one global
namespace.

The transferred profile is a dependency-closed selection rather than the
entire library. Its generic engines have handled opaque and transparent
declarations, grouped runtime rules, proof comparisons, source-ordered
modules, generated inductive owners, internal Pi, Sigma-transfor operations,
and profunctor fragments. A categorical operation is represented by a
semantic owner and argument schema, not a bespoke TypeScript AST tag with a
private evaluator branch. Thus, after mathematical review, extending the
profile is principally a typed-data and policy operation. This does not imply
that every remaining declaration can be imported as one batch or that a
parseable rewrite rule automatically acquires authority.

The public text adapter is intentionally later and thinner. It recognizes a
bounded mathematical syntax and resolves it into the same typed categorical
surface used by direct TypeScript construction. Parsing a string does not
create semantics. Expected types, classifier information, and the available
internal owners decide whether an application denotes an object action, an
arrow action, a displayed section component, a whole hom action, or a
supported higher component. The adapter fails with a source location when no
internal factorization exists.

This is also why Lambdapi remains useful after a browser-capable TypeScript
checker exists. The TypeScript runtime makes the demonstrated profile small,
inspectable, and client-side. Deterministic Lambdapi emission compares selected
judgments against the active source during development. The oracle is a
conformance route, not a production backend and not a substitute for the
TypeScript checker.

# 3. Directed Families, Totals, And Sections

Let $K$ be a category. A directed family over $K$ is a functor
$E:K\\vdash\\mathbf{Cat}$. It supplies a fibre category $E[k]$ for every
object $k$, but also transport along every base arrow:

$$
p:k\\to k'
\\qquad\\Longrightarrow\\qquad
E[p]:E[k]\\vdash E[k'].
$$

The arrow action is essential. A pointwise assignment of categories is not
yet a directed dependent type. In the kernel, the stable category of such
families is `Catd_cat K`; morphisms and higher morphisms are exposed by
`Functord_cat` and `Transfd_cat`. Their ordinary Cat-valued presentations are
available through controlled projections and proof-time comparisons, but the
stable displayed heads are retained so that higher action remains iterable.

Reindexing along $F:A\\vdash K$ is substitution:

$$
F^*E[a]=E[F[a]],
$$

implemented by `Pullback_catd`. The total category is the directed dependent
sum:

$$
\\Sigma_K E.
$$

Its objects are pairs $(k,u)$ with $u\\in E[k]$. An arrow
$(k,u)\\to(k',u')$ consists of

$$
p:k\\to k',
\\qquad
\\alpha:E[p](u)\\to u'.
$$

Thus the hom of a total category is organized by a dependent hom, not by an
ordinary product detached from transport. The owner `sigma_arrow` forms
$(p,\\alpha)$, and `sigma_transport_arrow(E,p,u)` uses the identity fibre
component to produce

$$
(k,u)\\longrightarrow(k',E[p](u)).
$$

The dependent product is the category of sections:

$$
\\Pi_K E.
$$

A section $s$ assigns $s[k]\\in E[k]$ and carries an action

$$
s[p]:E[p](s[k])\\to s[k'].
$$

The stable `Pi_cat` facade exposes section objects and the next displayed hom.
Evaluation and section action project through the generic displayed
application tower. They are not a second primitive function calculus.

## 3.1 Dependent hom as shared infrastructure

The common shape behind total arrows and section action is the dependent hom.
Given

$$
u\\in E[x],\\qquad v\\in E[y],\\qquad p:x\\to y,
$$

the fibre component of a directed arrow is

$$
\\mathrm{Hom}_{E[y]}(E[p](u),v).
$$

As $p$ varies this expression must itself carry action. Emdash packages it as
a Cat-valued construction over the base hom, with variance chosen so that
higher pre- and postcomposition normalize in the intended direction. The
public `homd_` and internalized `homd_int` owners are therefore more than
notation for a pointwise hom formula. They retain the object action, base
arrow action, and the next hom needed by later consumers.

This internalization avoids a common design trap. Suppose one defined a
displayed functor only by maps on fibre objects and fibre arrows and then
attached an external naturality square. Such a package would be awkward to
iterate: the next categorical dimension would have to unpack the square and
rebuild its action. In emdash, the relevant object is already a
`Functord_cat` or `Transfd_cat` term. Its action is observed through generic
`fapp*`, `tapp*`, and displayed internal-hom projections. Higher consumers
receive a first-class categorical term rather than a pointwise function plus
evidence.

The same principle explains several otherwise technical owners.
`sigma_map_func` turns a displayed functor into a functor between total
categories, with its fibre action ending in the displayed internal-hom
projection ladder. `sigma_pullback_total_func` maps the total of a reindexed
family back to the original total:

$$
\\Sigma_A(F^*D)\\longrightarrow\\Sigma_KD,
\\qquad
(a,u)\\longmapsto(F[a],u).
$$

Its arrow action sends $(p,\\alpha)$ to $(F[p],\\alpha)$. The construction is
asymmetric because one input is a family reindexed along a specified functor;
it is not a generic pullback of arbitrary total functors.

Likewise, section evaluation at an object and section action along an arrow
are related observations of one coherent section. The fixed-index
`piapp0` view is useful at the surface, while the generic displayed
application tower retains its arrow and higher action. This is why the
directed calculus deserves to be read as a DTT in its own terms: substitution,
context extension, dependent programs, and their directed action are part of
one computational structure.

These operations iterate to genuine dependent telescopes. If
$R:K\\vdash\\mathbf{Cat}$, then $\\Sigma_KR$ is the extended directed
context. A second family depending on both $k$ and $r\\in R[k]$ becomes a
family over this total category. The owners
`Sigma_catd_functord_catd` and `Sigma_transfd_funcd` internalize the
corresponding family and transformation uncurrying. Further `Sigma_cat` and
`Pi_cat` applications extend the telescope or form its dependent programs.

Independent displayed variables over one base use fibrewise products without
postulating a new primitive product-family head. For
$B,C:K\\vdash\\mathbf{Cat}$, write

$$
P(B,C)[k]=B[k]\\times C[k].
$$

The active presentation is built from ordinary product formation,
uncurrying, and the displayed family structure. Its projections, pairing,
swap, and diagonal support weakening, exchange, and contraction among
independent fibre siblings. This does **not** license swapping variables across
a genuine dependency edge. In a telescope

```text
k : K;
a : A[k];
b : B[(k,a)], c : C[(k,a)];
d : D[((k,a),(b,c))]
```

$b$ and $c$ share a base and may be paired or exchanged; $a$ cannot be moved
past data whose type depends on it. The distinction is the familiar
structural discipline of dependent type theory, now interpreted over objects
and arrows of a category.

# 4. Synthetic Arrow Induction

The mathematical anchor of v3.2 is a directed analogue of path induction.
Fix $x$ in a category $Z$. The covariant representable family is

$$
\\mathrm{Rep}_Z(x)[y]=\\mathrm{Hom}_Z(x,y).
$$

Its total category is the category of outgoing arrows:

$$
\\mathrm{PathOut}_Z(x)
  =\\Sigma_{y:Z}\\,\\mathrm{Hom}_Z(x,y).
$$

An object is a pair $(y,p)$ with $p:x\\to y$. The distinguished object is the
reflexive arrow

$$
\\iota_x=(x,\\mathrm{id}_x).
$$

Every outgoing arrow has a canonical total arrow from $\\iota_x$:

$$
\\rho_{x,y,p}:\\iota_x\\longrightarrow(y,p).
$$

It is not postulated as a new path constructor. It is ordinary Sigma
transport in the representable family:

$$
\\rho_{x,y,p}
  =\\mathrm{sigmaTransport}(\\mathrm{Rep}_Z(x),p,\\mathrm{id}_x).
$$

The endpoint is correct because representable action computes:

$$
\\mathrm{Rep}_Z(x)[p](\\mathrm{id}_x)=p.
$$

<div class="arrowgram">
{
  "version": 1,
  "nodes": [
    { "name": "base_x", "left": 130, "top": 250, "label": "$x$" },
    { "name": "base_y", "left": 520, "top": 250, "label": "$y$" },
    { "name": "total_x", "left": 130, "top": 90, "label": "$(x,\\mathrm{id}_x)$" },
    { "name": "total_y", "left": 520, "top": 90, "label": "$(y,p)$" },
    { "name": "fibre_id", "left": 130, "top": 410, "label": "$\\mathrm{id}_x$" },
    { "name": "fibre_p", "left": 520, "top": 410, "label": "$p$" }
  ],
  "arrows": [
    { "from": "base_x", "to": "base_y", "label": "$p$", "label_alignment": "over" },
    { "from": "total_x", "to": "total_y", "label": "$\\rho_{x,y,p}$", "label_alignment": "over" },
    { "from": "total_x", "to": "base_x", "label": "$\\pi_1$", "label_alignment": "right", "style": { "body": { "name": "dashed" } } },
    { "from": "total_y", "to": "base_y", "label": "$\\pi_1$", "label_alignment": "left", "style": { "body": { "name": "dashed" } } },
    { "from": "fibre_id", "to": "fibre_p", "label": "$\\mathrm{Rep}_Z(x)[p]$", "label_alignment": "over" },
    { "from": "base_x", "to": "fibre_id", "label": "$\\mathrm{fibre}$", "label_alignment": "right", "style": { "body": { "name": "dotted" } } },
    { "from": "base_y", "to": "fibre_p", "label": "$\\mathrm{fibre}$", "label_alignment": "left", "style": { "body": { "name": "dotted" } } }
  ]
}
</div>

Now let $E:\\mathrm{PathOut}_Z(x)\\vdash\\mathbf{Cat}$ be a motive and
$u\\in E[\\iota_x]$. Transport along the canonical arrow defines a section:

$$
\\mathrm{Ind}_x(E,u)[(y,p)]
  =E[\\rho_{x,y,p}](u).
$$

In kernel notation, `path_ind_sec(Z,x,E,u)` inhabits

$$
\\Pi_{q:\\mathrm{PathOut}_Z(x)}E[q].
$$

This is fixed-source arrow induction. It resembles identity elimination
because the reflexive outgoing arrow determines all components, but no
invertibility is assumed. The comparison from reflexivity to $(y,p)$ is a
directed arrow in a Sigma category.

The principal theorem internalizes the source $x$ as well. Precomposition by
$r:x\\to y$ gives

$$
\\mathrm{PathOut}_Z(r):
\\mathrm{PathOut}_Z(y)\\vdash\\mathrm{PathOut}_Z(x).
$$

$$
\\mathrm{PathOut}_Z(r)[z,q]=(z,q\\circ r).
$$

Consequently motives vary by pullback and sections vary by section pullback.
The source-indexed induction theorem is a displayed transformation

```text
PathInd(Z) :
  PathOutReflEval_Z => PathOutPi_Z
```

Its kernel owner is `PathInd_transfd(Z)`. At each $x$ it is the fixed-source
induction functor. Along an arrow $r$, its type already contains the
comparison between transporting initial data and pulling back the resulting
section. Naturality is therefore internal to one displayed transformation; it
is not an externally supplied square.

The fixed-source component can be pictured as motive transport:

<div class="arrowgram">
{
  "version": 1,
  "nodes": [
    { "name": "initial", "left": 110, "top": 110, "label": "$E[(x,\\mathrm{id}_x)]$" },
    { "name": "target", "left": 520, "top": 110, "label": "$E[(y,p)]$" },
    { "name": "u", "left": 110, "top": 300, "label": "$u$" },
    { "name": "transported", "left": 520, "top": 300, "label": "$E[\\rho_{x,y,p}](u)$" }
  ],
  "arrows": [
    { "from": "initial", "to": "target", "label": "$E[\\rho_{x,y,p}]$", "label_alignment": "over" },
    { "from": "u", "to": "transported", "label": "$\\mathrm{Ind}_x(E,u)[(y,p)]$", "label_alignment": "over" },
    { "from": "initial", "to": "u", "label": "$\\mathrm{element}$", "label_alignment": "right", "style": { "body": { "name": "dashed" } } },
    { "from": "target", "to": "transported", "label": "$\\mathrm{element}$", "label_alignment": "left", "style": { "body": { "name": "dashed" } } }
  ]
}
</div>

There are two different kinds of non-strictness here. First, changing the
source object acts contravariantly on `PathOut`, so the target section is
pulled back rather than transported by an identity. Second, an arbitrary
displayed functor need not preserve a transported Sigma arrow as a strict
cartesian map; its component-level comparison remains visible through the
displayed internal-hom action. The theorem packages the comparisons that are
actually justified. It does not obtain a stronger strictness principle by
calling the construction "induction."

There is also a totalized presentation over the Sigma category of sources and
motives. It is derived by applying `Sigma_transfd_funcd` to the telescope
theorem:

```text
PathInd_funcd(Z) = Sigma_transfd_funcd(PathInd_transfd(Z)).
```

The direction of ownership is significant. The displayed transformation is
primary because it retains the varying-source action. The total functor is a
useful derived view, not a second induction axiom.

# 5. Composition As A Checked Normal Form

Arrow induction earns its keep by computing a familiar operation. For
$p:x\\to y$, define a motive at $(y,p)$ by the functor category between
representables:

$$
\\mathrm{CompMotive}_x[(y,p)]
  =\\mathrm{Rep}_Z(y)\\vdash\\mathrm{Rep}_Z(x).
$$

At the reflexive outgoing arrow this is
$\\mathrm{Rep}_Z(x)\\vdash\\mathrm{Rep}_Z(x)$, so the initial datum is the
identity functor. Induction produces a section

$$
\\mathrm{pathCompSec}(x)
  =\\mathrm{Ind}_x(\\mathrm{CompMotive}_x,\\mathrm{id}).
$$

Its component at $p$ is a functor

$$
\\mathrm{pathComp}(p):
\\mathrm{Rep}_Z(y)\\vdash\\mathrm{Rep}_Z(x).
$$

Applying it to $q:y\\to z$ normalizes to composition:

$$
\\mathrm{pathComp}(p)[z][q]
  \\rightsquigarrow q\\circ p.
$$

## 5.1 The normalization route

The final equation is compact, but the checked route crosses several
abstraction boundaries. At a high level, evaluation performs the following
steps:

```text
PathInd_transfd(Z)
  ↓ component at x
PathInd_func(Z,x)
  ↓ component at CompMotive_x
path_ind_sec(Z,x,CompMotive_x,id)
  ↓ section component at (y,p)
CompMotive_x[rho_{x,y,p}](id)
  ↓ representable and Sigma-transport computation
path_comp_func(p)
  ↓ action at (z,q)
hom_postcomp_fapp0(id_Z,q,p)
```

Each arrow is owned by a reusable projection or computation. The theorem's
displayed component projects to fixed-source induction. Section evaluation
projects to motive transport along $\\rho$. Sigma transport computes the
endpoint from $\\mathrm{Rep}_Z(x)[p](\\mathrm{id}_x)=p$. The composition
motive then exposes postcomposition between representables.

This factorization is valuable for regression. A direct rule
`pathComp(p,q) -> q o p` would prove only that one named head reduces. The
expanded checks verify that the theorem remains connected to its semantic
construction. They instantiate both the displayed telescope route and the
derived total-functor route all the way to the same hom-action owner. Nearby
negative assertions keep opaque motives, unrelated arrow endpoints, and
higher cells from being consumed by the specialized path.

The checks exercise this result both through the primary telescope theorem and
through the derived Sigma-total theorem. They also check the preceding
representable and $\\rho$ computations, so the final result is not an
unrelated rewrite attached directly to the theorem name.

There is a useful implementation subtlety. The runtime normal form is the
represented-hom postcomposition owner

```text
hom_postcomp_fapp0(id_Z, q, p).
```

The ordinary categorical presentation `comp_fapp0(q,p)` is a typed
proof-time comparison surface. Emdash does not globally erase these
provenances into one raw composition syntax. Postcomposition,
precomposition, and rigid two-endpoint hom action have different variance and
different higher behavior. Narrow comparisons relate them when a theorem
needs to see the same categorical composite.

This illustrates the normalization policy used throughout the kernel.

- A **rewrite rule** selects a runtime normal form and participates in
  reduction and critical-pair analysis.
- A **unification rule** helps the framework compare two intended
  presentations when neither should compute to the other.
- The global `fapp*` and `tapp*` calculus owns generic identity,
  composition, functoriality, and naturality.
- Constructor-specific rules are projection betas or measured joins, not
  duplicate copies of generic coherence.

In this sense, the equation $\\mathrm{pathComp}(p)(q)=q\\circ p$ is both a
mathematical theorem and a regression test for the architecture. It passes
only if Sigma transport, representable action, displayed transformation
projection, section evaluation, and hom-action cut elimination agree on a
normal form.

# 6. Usable Categorical Binders

The kernel expressions above are explicit and compositional, but they are not
how an end user wants to author every program. Ordinary dependent type theory
allows a variable to occur recursively inside a term and reconstructs the
wiring. Categorical syntax needs the same usability while distinguishing
several kinds of action.

The current surface marks the intrinsic binder mode on the lambda:

```text
λ^f   functorial
λ^n   natural / indexed
λ^fd  displayed-functorial
λ^nd  displayed-natural
```

A type annotation such as `x : A` is separate and may be inferred when the
expected type determines it. This is why `λ^f x. ...`, rather than
`λ x :^f A. ...`, is the durable notation direction: functoriality belongs to
the binder, while the domain annotation is ordinary bidirectional typing
information.

**Type-directed application.** Whitespace application is intentionally neutral
in the source. The expression `F x` does not itself say whether to use an
object component, a capped arrow component, a whole hom action, a section
evaluation, or a displayed component. The resolver combines the inferred type
of `F`, the classifier and variation of `x`, and the expected result.

| Typed situation | Selected internal reading |
| --- | --- |
| `F : A ⊢ B`, `x : Obj(A)` | object action `fapp0(F,x)` |
| `F : A ⊢ B`, `p : Hom_A(x,y)` | arrow action `fapp1(F,p)` |
| functor expected over a whole hom | internal hom action, not one capped point |
| `s : Π(k :^n K), E[k]`, `k : Obj(K)` | section component `piapp0(s,k)` |
| `FF : E ⊢_K D`, `a : E[k]` | displayed fibre component |
| coherent transfors at `k` | internal component and higher-action owners |

The whole-hom case is particularly important. If the expected result is a
functor between hom-categories, prematurely choosing the value on one arrow
would lose the object needed for the next higher action. The resolver
therefore preserves a functor-level term whenever later iteration is
requested. This is the surface counterpart of the kernel's preference for
functor-level folds over capped point rules.

Contravariance is also typed rather than guessed from names. Represented hom
has distinct postcomposition and precomposition owners. A future surface may
infer polarity from a classifier or expected mixed-variance family, but the
current frontend supports only reviewed cases. It will not reverse an arrow
or synthesize an opposite merely because doing so would make a local
application typecheck.

Neutral application makes the syntax familiar while keeping the elaboration
falsifiable. Each selected route produces an explicit owner that the generic
checker can verify. When two routes are possible at the raw syntactic level,
the expected type disambiguates them; when the expected type is insufficient,
the diagnostic requests an annotation rather than committing to a
noncanonical action.

The frontend does not recognize whole source strings and replace them with
owner-specific templates. It lowers each scoped callback or parsed binder to
a first-order contextual representation and recursively analyzes
subexpressions. Variable occurrence and expected classifier information
determine structural wiring.

For ordinary functorial abstraction, the basis includes:

- identity when the body is the variable;
- weakening when the variable is unused;
- diagonal/contraction when it is used more than once;
- exchange for independent nested variables;
- product pairing and projections;
- evaluation of a functor-valued expression against an argument expression;
- functor composition; and
- curry/uncurry for nested abstraction.

This handles examples that are easy to write but not reducible to a single
eta pattern:

```text
λ^f x. (H x) (K x)
λ^f x. F x y0
λ^f x : A. λ^f y : B. E y x
```

The first uses $x$ in both function and argument positions. The second
abstracts after evaluation at a fixed inner object. The third exchanges
independent variables before evaluation. Each compiles to existing product,
pairing, evaluation, composition, and exchange owners.

**Dependency-aware structural compilation.** The compiler treats a context as
ordered typed slots plus dependency edges. For each abstraction it first
lowers the body recursively, then computes how the selected slot occurs in the
resulting typed tree. Zero, one, or multiple uses select weakening,
identity-like routing, or contraction/pairing. Independent nested slots may be
exchanged. A slot that occurs in the type of a later slot cannot be exchanged
across that dependency.

Displayed contexts add a base classifier to every slot. Extending by
$a:A[k]$ changes the base from $K$ to $\\Sigma_KA$. A later family must name
that total or a checked pullback of a family along a known projection.
Independent siblings $B$ and $C$ over the same extended base are grouped
through $P(B,C)$; after their pair is introduced, the next base is
$\\Sigma P(B,C)$. The compiler derives these transitions from family types,
not from untyped punctuation alone.

This design supports both DTT viewpoints that arise in practice. A sequential
telescope represents variables whose types depend on earlier variables.
Fibrewise product structure represents several variables that are independent
of one another but share a dependent base. Weakening, symmetry, and
contraction apply inside the latter block, while substitution and
totalization connect the former levels. The implementation may use different
lowering routines for the two cases; what matters is that they compose through
the same explicit internal owners without an ad hoc semantic exception.

Natural and displayed binders require indexed classifiers rather than an
external naturality proof. A section component example is:

```text
λ^n k : K. (GG k) ((FF k) (s k))
```

Here `s k` is a section value in a fibre and `FF k` is the component of a
displayed functor; `GG k` continues the section through a second displayed
functor. Recursive application elaborates this finite rigid chain through
generic composition at `Catd_cat K`. Both the object component and the action
over a base arrow are already owned by the internal displayed construction.

A displayed functorial example composes internal displayed functors:

```text
λ^fd a : E. GG (FF a)
```

Displayed weakening can recover the hidden base index and apply a section:

```text
λ^fd a : E. s (indexOf a)
```

For independent siblings over one base, the frontend uses fibrewise pairing:

```text
λ^fd (b : B, c : C). fibrePair (FF b) (GG c)
```

The mixed telescope combines genuine dependency edges with an independent
middle block:

```text
λ^fd (a : A; b : B, c : C; d : D). fibrePair b c
```

Semicolons advance the dependent context. The comma says that $b$ and $c$
are siblings over the same preceding total. The family of $d$ is based on
the total containing their pair. The contextual compiler derives the
necessary pullbacks and totalizations, while the user writes the variables
in the same dependency order as an ordinary DTT telescope.

The implemented normal form is not limited to the displayed four-slot
example. It accepts any finite sequence of these canonical dependency levels,
with finite sibling groups at a level, for the reviewed displayed-functorial
and displayed-natural constructions. The category resolver also descends
through any finite number of qualified Hom-category levels over its supported
roots, and the indexed-section route composes finite rigid chains such as the
one above. These results do not license arbitrary dependency or variance
graphs, exchange across a dependency edge, or coherence synthesis outside the
qualified grammar.

**A worked mixed telescope.** The mixed example is small enough to run in the
reviewer but rich enough to show the dependency algorithm:

```text
λ^fd (a : A; b : B, c : C; d : D). fibrePair b c
```

Assume

```text
K : Cat
A : Catd K
B, C : Catd (Sigma_cat A)
D : Catd (Sigma_cat P(B,C)).
```

The expected type makes this a displayed contextual functor, not an outer LF
lambda or a pointwise function. The compiler extends the base to
$\\Sigma_KA$, verifies that $B$ and $C$ are independent siblings there, and
represents them by the fibrewise product $P(B,C)$. It then checks $D$ over the
total containing that pair, inserts dependency-aware weakening because the
body does not use $d$, and emits the sibling projections and displayed pairing
owner explicitly. Giving $B$ and $C$ different bases, basing $D$ before the
sibling pair, exchanging $a$ across a family that depends on it, or returning
a value from an unrelated displayed family is rejected.

The object component alone would not validate this construction. Let $p$ be
a base arrow and let $u$ be an internalized arrow in the displayed source.
The capped cell of the pairing owner reduces componentwise:

$$
\\mathrm{cell}(\\langle FF,GG\\rangle,p,u)
  =
\\bigl\\langle
  \\mathrm{cell}(FF,p,u),
  \\mathrm{cell}(GG,p,u)
\\bigr\\rangle.
$$

The active kernel expresses this at the generic `fdapp1_int_cell` projection
for `Product_pair_funcd`; it does not introduce a second product-cell
calculus. The TypeScript consumer transfers the existing owner and rule,
checks the object and internalized-arrow observations, and retains an opaque
cell as a non-collapse witness. Sequential dependency and fibrewise siblings
may use different lowering routines; the invariant is that both end in
composable internal owners whose object and arrow actions are checked by the
same Core.

The displayed-natural slice demonstrates recursive component composition:

```text
λ^nd k : K. composeCells (theta k) (eta k)
```

The result is not a pointwise function accompanied by a hand-authored
naturality equation. The typed inputs are already transfors, their component
operations are internal projections, and generic higher action carries the
construction forward.

These examples expose the design's key usability rule:

> Convenient syntax may hide structural categorical operations, but it may
> not fabricate categorical coherence.

If the expected type requests an action for which the active kernel has no
internal owner, elaboration reports an unsupported action. Escaped binder
tokens, wrong families, incompatible bases, illegal dependency exchange, and
foreign construction environments are rejected. This fail-closed policy is
what allows the surface to grow without becoming a second, unsound
category-theory implementation.

The string syntax is correspondingly bounded. The adapter parses neutral
application, annotations, the four binder modes, and the reviewed constructors
needed by twelve source presets. It does not parse arbitrary Lambdapi source or every
notation in the book. Direct typed TypeScript remains the more complete
construction surface; both routes converge before checking.

# 7. From Surface Terms To Explicit Core

Consider the ordinary source:

```text
λ^f x. (H x) (K x)
```

The parser identifies a functorial binder and neutral applications. The
resolver uses the expected functor type and the types of `H` and `K` to
classify both occurrences of $x$. The contextual compiler constructs the
diagonal, pairs the two resulting functorial expressions, and applies the
evaluation functor. Serialization then reveals the explicit owners and
arguments that were silent in the source.

The same path applies to direct TypeScript construction. A scoped builder
invokes each callback once with an opaque token. Lowering replaces that token
by a locally nameless contextual slot. No arbitrary JavaScript closure enters
Core, and a token cannot escape its builder or be reused in another
environment.

Explicit Core is then processed by one generic dependent-LF runtime:

1. declarations establish owner types and optional transparent bodies;
2. bidirectional checking verifies applications and dependent binders;
3. metavariable constraints are revisited through bounded pattern
   unification;
4. $\\beta$ reduces outer lambdas and $\\delta$ unfolds authorized
   definitions;
5. reviewed categorical runtime rules normalize internal owners; and
6. the result is serialized with its inferred and expected type.

The strongest small dependent demonstration crosses both layers. An outer LF
lambda receives a section over a nested Sigma telescope. Its body applies the
section to a dependent pair. Checking verifies that the pair belongs to the
expected family; evaluation performs outer $\\beta$ and then the directed
Sigma-telescope fibre rule. Replacing the fibre object by one from another
family produces a type mismatch rather than a stuck or coerced term.

## 7.1 Checked behavior, diagnostics, and provenance

Positive examples alone would not establish the boundary. The executable
corpus pairs them with negative and non-collapse cases. An object from the
wrong category cannot be passed to a functor action. A dependent pair from the
wrong family cannot be consumed by a section. A displayed family based on
$K$ cannot masquerade as one based on $\\Sigma_KA$. An internalized arrow is
checked not to collapse to its object component, and an opaque higher cell
remains opaque when no projection rule applies.

Diagnostics are normalized at the surface boundary. They record a stable
code, phase, source span, expected classifier or family, and an explanatory
detail. The browser does not duplicate these checks; it formats the same
diagnostic returned by the TypeScript elaborator. This makes an edited example
useful to a reviewer: rejection exposes which architectural condition is
missing instead of producing a generic JavaScript exception.

Conformance evidence is separate from runtime provenance. A candidate profile
records the Lambdapi module, source or canonical-export evidence, selected
owner set, and reviewed rule set from which it was built. Node-side tools can
emit a deterministic Lambdapi judgment and compare it with the active kernel.
The browser consumes only the frozen browser-safe selection contract and
compiled runtime data; it neither reads source files nor computes an authority
digest.

The browser reviewer packages this architecture without adding semantic
machinery. Its expression panel offers twelve presets across `^f`, `^n`,
`^fd`, and `^nd`, with editable text, explicit Core, inferred type,
structural prerequisites, and source-located rejection. Its evidence panel
runs the existing outer-LF, ordinary bracket, and genuinely displayed
dependent witnesses on request. Its Core panel exposes a minimal editable
dependent-LF script. The entire published runtime is client-side; it opens the
overview paper and full book as static assets.

The artifact boundary is worth stating precisely.

| Layer | What it establishes |
| --- | --- |
| Active Lambdapi sources | Authoritative categorical declarations, computation rules, and proof-time comparisons |
| Lambdapi checks | Executable positive, negative, and normal-form evidence for the active kernel |
| TypeScript Core | A small dependent checker/evaluator for the reviewed transferred profile |
| Categorical frontend | Recursive compilation of the demonstrated binders to internal owners |
| Browser reviewer | Reproducible access to the same TypeScript paths, with no server or production Lambdapi process |

The browser does not contain the entire Lambdapi development. It establishes
one real end-to-end path: surface syntax reaches explicit internal structure,
generic checking, and computation in a client an external reviewer can run.

# 8. From Invertibility Sieves To Local Geometry

Arrow induction began with a family stable under change of endpoint and only
then extracted a familiar operation from its total category. The same order
organizes local geometry. A condition is first allowed to vary along every
probe. Representability by one chart, coverage by a topology, and reflection
into sheaves are separate constructions. Keeping those stages apart is what
makes the resulting claims executable rather than mnemonic.

## 8.1 The sieve comes before the open

Let $\\mathcal O$ be a presheaf of commutative rings on a category
$\\mathcal K$, let $U$ be an object, and let $s\\in\\mathcal O(U)$. Every
probe $p:V\\to U$ restricts the section to $p^*s\\in\\mathcal O(V)$. Define

$$
D_U(s)(p)
  := \\mathsf{Unit}_{\\mathcal O(V)}(p^*s).
$$

Ring maps preserve units. Hence a witness at $p$ restricts along every
$q:W\\to V$ to a witness at $p\\circ q$. The successful probes form an
ordinary sieve on $U$. No decision procedure for invertibility and no
representing open were needed. Unit evidence is proposition-valued, so the
sieve is subterminal, while a selected inverse remains available during the
calculation.

This is the article's organizing geometric reversal: the primary object is
invertibility's sieve, not invertibility's open. The familiar phrase “the open
on which $s$ is invertible” silently combines two claims. The first is the
functorial stability just proved. The second is that all successful probes are
represented by one object over $U$. The first makes sense on an arbitrary
site; the second depends on additional geometry.

In a posetal site, a representing open $A\\le U$ satisfies

$$
p\\in D_U(s) \\quad\\Longleftrightarrow\\quad p\\text{ factors through }A.
$$

It is therefore the largest open on which $s$ is invertible. Zeuner's
constructive algebraic geometry [5] organizes the coherent or qcqs case by
such compact-open supports. The sieve-centered formulation retains that
account when a compact representative exists, while making the
representability question explicit when it does not.

For affine geometry take $\\mathbf{Aff}=\\mathbf{CRing}^{\\mathrm{op}}$.
The generalized points of a ring $R$ at a test ring $S$ are maps $R\\to S$.
For $f\\in R$ the affine invertibility sieve has components

$$
D_R(f)(S)
  =\\sum_{h:R\\to S}\\mathsf{Unit}_S(h(f)).
$$

Now suppose a localization $\\iota_f:R\\to R[1/f]$ has been supplied by its
universal property. Composition with $\\iota_f$ sends a map
$R[1/f]\\to S$ to a $D_R(f)$-point. Conversely, a map $h:R\\to S$ carrying
$f$ to a unit has a contractible space of factors through $\\iota_f$.
Selecting its center and using contractibility for uniqueness gives an
explicit pointwise equivalence

$$
\\operatorname{Hom}_{\\mathbf{CRing}}(R[1/f],S)
  \\simeq D_R(f)(S).
$$

This statement needs no fraction normal form. A quotient, fraction, or
fixed-image construction may serve as coordinates once it satisfies the same
factorization problem. The checked result is presently pointwise at every
test ring; its components retain existing functorial action, but they have not
been assembled into a new whole presheaf equivalence.

Multiplication computes intersection at the same semantic level. An image of
$fg$ is a unit exactly when the images of both $f$ and $g$ are units, giving
$D_R(fg)(S)\\simeq D_R(f)(S)\\cap D_R(g)(S)$ pointwise. A supplied
localization at $fg$ presents the same question without equating independently
chosen packages.

## 8.2 From finite covers to a Cat-valued reflector

The next step is coverage. Suppose a chart ring $S$ carries a finite family
$f_1,\\ldots,f_n$ and coefficients with

$$
\\sum_i a_i f_i=1.
$$

After selecting localizations at the $f_i$, the resulting basic chart arrows
form a witness-rich proposed cover. The witness retains the family,
coefficients, localization packages, and literal containment in the proposed
sieve. Coverhood itself should not depend on which presentation was supplied.
Emdash therefore defines the generated topology as the intersection of all
Grothendieck topologies accepting the generators. It accepts every retained
finite presentation, satisfies maximality, pullback stability, and local
character, and is least among accepting topologies. The construction proves a
universal property; it does not provide an inductive derivation language or a
decision procedure for coverhood.

Fix now any site $(\\mathcal K,J)$ and a Cat-valued presheaf $P$. For a sieve
$R$ on $U$, whole matching families and whole sections are hom-categories

$$
\\operatorname{Match}_P(R)=\\operatorname{Hom}(\\widehat R,P),
\\qquad
\\operatorname{Sect}_P(U)=\\operatorname{Hom}(yU,P).
$$

Restriction is precomposition with the inclusion
$\\widehat R\\to yU$. Locality says that this restriction is an equivalence
for every covering sieve. Sheafification asks for more: construct a local
presheaf from an arbitrary one, functorially and universally.

The direct cover completion $aP$ is presented by three pieces of categorical
structure. **Return** is a whole map $\\eta_P:P\\to aP$. **Glue** is a whole
functor from matching families in $aP$ to sections in $aP$, varying
functorially over the category of eligible covering questions. **Silent** is
one path saying that gluing the restriction of a section recovers that
section. Newly glued data may enter later matching families, so glue is
recursive; because coefficients are Cat-valued, it must act on arrows between
matching families as well as on their objects.

This return/glue/silent pattern is conceptually adapted from Pédrot's free
sheaf construction [6], but it is installed directly in categorical
semantics. Cover questions, matching and section categories, displayed
functoriality, and whole paths live inside the functorial calculus hosted by
the outer logical framework. No separate modal type theory is assumed. The
constructors are primitive at this categorical-HIT boundary; their
consequences are proved afterward.

Naturality of the one whole glue functor supplies compatibility with pullback
of covers. From that compatibility and silent coherence, the opposite
restriction-after-glue law is derived rather than postulated. A recursor then
extends every seed $P\\to Y$ into a topology-local target $Y$ across $aP$,
and categorical-HIT uniqueness gives the whole equivalence

$$
\\operatorname{Hom}(aP,Y)
  \\simeq \\operatorname{Hom}(P,Y).
$$

Consequently direct cover completion assembles a left adjoint

$$
a:\\operatorname{Psh}_{\\mathbf{Cat}}(\\mathcal K)
  \\rightleftarrows
  \\operatorname{Sh}_{\\mathbf{Cat}}(\\mathcal K,J):i,
\\qquad a\\dashv i,
$$

whose counit on every sheaf is an omega-equivalence. This is a fixed-site,
Cat-valued reflector. It does not yet lift the construction to
commutative-ring-valued presheaves, prove left exactness, or supply a
base-change theorem.

## 8.3 The precise boundary of the geometric application

The affine chain now has a constructed computational spine. Ring maps give
generalized probes; unit preservation gives $D_R(f)$; localization represents
that question pointwise; products compute intersections; finite unimodular
families generate a big Zariski topology; and the coordinate presheaf computes
restriction along its charts. The Cat-valued reflector demonstrates that
sheafification itself can be expressed directly at the layer of categorical
semantics.

The remaining commitments are deliberately visible. The active affine
presentation supplies a reflective commutative-ring-valued structure sheaf
and whole localization locality rather than deriving them from the Cat-valued
reflector. A global-first, site-relative scheme presentation begins with one
supplied global ringed object, a covering sieve constructively generated by
two selected affine charts, and topology-local ring behavior. Whole
restrictions and a selected chart intersection are inherited from the global
presheaf instead of copied into an atlas record.

On that literal overlap, polynomial and localization universal properties
construct the Laurent coordinate changes $t\\mapsto u^{-1}$ and
$u\\mapsto t^{-1}$. A supplied projective-line package retains the global
site-relative scheme, its actual selected overlap, and the whole Laurent
comparison. It is an end-to-end computational capability, not a construction
of a global object from abstract charts. There is no graded ring interface,
homogeneous localization, degree-zero construction, `Proj`, general
projective space, or non-affineness theorem in the active artifact.

## 8.4 Free groupoidal realization and the Gray test

The same owner discipline connects directed arrows with equality paths.
For a groupoidal classifier $A$, the category $\\mathsf{Path}(A)$ has elements
of $A$ as objects and equality as hom. Products are closed under this view
homwise: a path of pairs splits into its two coordinates and coordinate paths
reassemble, while direct dependent transport agrees propositionally with
either sequential coordinate order.

The opaque Circle makes the computational boundary sharper. Its dependent
eliminator reduces both at the base point and when dependent path action is
observed on the generating loop. The familiar constant-family
$\\mathsf{ap}$ equation is derived propositionally rather than installed as a
second runtime rule. A successor-localized Integer classifier supplies the
universal cover, and encode/decode proves

$$
\\mathrm{Hom}_{S^1}(\\mathsf{base},\\mathsf{base})
  \\simeq \\mathbb Z.
$$

WalkingEnd maps to the Circle by sending its directed generator to the loop;
natural powers become the nonnegative integer powers. The two-ended
WalkingArrow similarly maps to a groupoidal Interval. These are finite tests
of the category-indexed operation
$\\mathsf{Groupoidify}(C)$, whose constructor is one whole functor

$$
\\eta_C:C\\longrightarrow
\\mathsf{Path}(\\mathsf{Groupoidify}(C)).
$$

For every groupoid $G$, restriction along $\\eta_C$ and the whole extension
recursor form a fixed-forward mapping-object equivalence

$$
\\begin{aligned}
&\\mathrm{Hom}_{\\mathsf{Grpd}}
  (\\mathsf{Groupoidify}(C),G)\\\\
&\\qquad\\simeq_{\\omega}
  \\mathrm{Functor}(C,\\mathsf{Path}(G)).
\\end{aligned}
$$

The recursor computes on represented points and dependent first cells.
Restriction and extension have whole beta/eta paths and retain higher action.
This is more than a carrier-level free groupoid, but less than a packaged
adjunction: the action of `Groupoidify` on a source functor has not yet been
constructed.

The directed side of the same story is exposed by a compositor

$$
\\phi^F_{g,f}:F[g]\\circ F[f]\\Longrightarrow F[g\\circ f]
$$

projected from whole internal laxity. In a path target this cell is invertible;
for a decoded strict-functor code it computes to identity; in an arbitrary
directed target it may remain noninvertible. Emdash reuses that distinction in
the profiled category $\\mathsf{GrayHom}_{\\mathrm{lax}}(A,B)$: objects are
computationally strict functor codes, while arrows and all higher homs come
from the ambient transfor tower.

One selected right closure is checked:

$$
\\begin{aligned}
&\\mathsf{GrayHom}_{\\mathrm{lax}}(A\\otimes_R B,C)\\\\
&\\qquad\\simeq_{\\omega}
  \\mathsf{GrayHom}_{\\mathrm{lax}}
    (A,\\mathsf{GrayHom}_{\\mathrm{lax}}(B,C)).
\\end{aligned}
$$

Coevaluation at two walking arrows gives a four-vertex square. Its two
coordinate routes are compared by a nonidentity interchanger projected from
whole laxity, with one next action retained. This is a computational coherence
stress test, not a claim to the full combinatorial or Crans--Gray tensor
studied in [7]. Together, the geometry and groupoidal slices support the same
architectural conclusion: generic action should own functoriality and
naturality, semantic constructors should own computation, and elaboration
should reconstruct structural wiring.

## 8.5 Simplexes from dependent homs

Injective skip/keep codes form the internal augmented semi-simplex category.
Yoneda gives $\boldsymbol\Delta[n]=\mathrm{Hom}(-,n+1)$. Directed join gives
$\Delta[0]=\mathbf 1$ and
$\Delta[n+1]=\Delta[n]\star\mathbf 1$; the native recurrence is
$S_0(C)=C$ and $S_{k+1}=\mathrm{PathOut}_{S_k}(s_k)$.

Since $\mathrm{PathOut}$ is a Sigma of a representable hom, its arrows pair a
base cell with a dependent cell above transport. A triangle contains
$p_{12}\circ p_{01}\Longrightarrow p_{02}$; whole base and endpoint action
supply the extra tetrahedral faces and retain another hom action.

An intrinsic flag code records the changing native category. A stage
$F,G:K\to B$, $\epsilon:F\Rightarrow G$ sends an old source $s$ to the new
code $\mathrm{step}(\mathrm{code},F[s])$ and source
$(G[s],\epsilon[s])$. The first stage comes from the ordinal join and later
stages lift $\epsilon$ through $\mathrm{PathOut}$. Nat recursion therefore
constructs the source for variable $n$, maps it under every
$H:\Delta[n]\to C$, and restricts it along nonempty faces. Dimensions zero
through four, the five faces of the four-simplex, noncollapse, and one next
action are checked.

The active `DependentSimplexObservation(C,n)` is an object package, not
yet a whole category. The corresponding mapping-category equivalence,
degeneracies, and general Kan, Segal, or Rezk theorems remain open.

# 9. Research Boundaries

The word *checked* in this article has a local meaning. Lambdapi accepts the
active declarations and rules and verifies the recorded assertions; the
TypeScript runtime accepts the demonstrated transferred terms and rejects its
negative corpus. It does not mean that a global metatheory has already been
formalized.

The principal open boundaries are:

- **Surface generality.** The categorical text language covers the reviewed
  twelve-preset profile, not arbitrary book notation, Lambdapi syntax, or
  every direct TypeScript constructor. The full canonical mathematical
  surface is intentionally broader.
- **Displayed depth and variance.** Independent siblings, genuine dependency,
  finite canonical dependency levels and sibling groups, qualified finite
  Hom-category recursion, finite rigid section chains, and selected higher
  action are implemented. Arbitrary dependency or variance graphs,
  dependency-edge exchange, unrestricted mixed introduction and currying,
  polarity-directed contravariant lowering, and general displayed-transfor
  coherence are not.
- **Transfer scale.** Generic transfer engines and varied representative
  tranches exist, but systematic transfer of the whole active Lambdapi
  library has not graduated. Mathematical rules will continue to require
  owner and interaction review even if their representation becomes
  mechanical.
- **Sheafification and geometry.** Direct cover completion constructs a
  fixed-site Cat-valued reflector, not a commutative-ring lift, a
  left-exactness theorem, or base-change semantics. Affine structure-sheaf
  and locality capabilities remain supplied; schemes are site-relative; the
  projective-line package is supplied rather than glued from charts; and
  graded `Proj` and projective space remain future work.
- **Categorical closure.** General dependent adjunctions
  $\\Sigma_F\\dashv F^*\\dashv\\Pi_F$, full profunctor tensor/coend semantics,
  complete equipment coherence, and semantic collage or dependent elimination
  for join remain future work.
- **Groupoidal closure.** Equality, J, groupoidal dependent sums/products, the
  Circle HIT with $\Omega S^1\simeq\mathbb Z$, its concrete WalkingEnd
  comparison, the WalkingArrow/Interval test, category-indexed
  $\\mathsf{Groupoidify}(C)$ with its target-side whole mapping equivalence,
  and representative product preservation/transport coherence are checked.
  Source functoriality and the adjunction package, closure for every former,
  and arbitrary motive-directed computational decomposition of J are not.
- **Metatheory.** No global normalization, confluence, canonicity,
  consistency, decidability, or semantic-soundness theorem is claimed for the
  full combined calculus. Lambdapi's local rule checks and the project's
  diagnostics are implementation evidence, not replacements for those
  theorems.
- **Higher categories.** Whole laxity, computational strict-functor codes, one
  profiled right Gray closure, and its walking interchanger are checked. The
  mirror closure, tensor functoriality and coherence, full Crans--Gray
  monoidality, global migration of historical strict endpoint cuts, and a
  general weak-$\\omega$-category metatheory remain open.
- **Simplicial methods.** Injective face codes, the augmented semi-simplex
  index, native simplexes through dimension four, and the variable canonical
  source are checked. Degeneracies, the whole mapping-category equivalence,
  and general Kan, Segal, Rezk, complicial, or oriental structure are not.

These limits are architectural information, not disclaimers added after the
fact. Fail-closed elaboration, explicit product manifests, runtime versus
proof-time ownership, and the separation of authority from conformance exist
to make partial progress reviewable without silently broadening the claim.

# 10. Conclusion

Functorial Type Theory treats categorical variation as computational
structure. Emdash realizes that idea through complementary layers: an outer
dependent logical framework and an inner directed dependent calculus of
families, totals, sections, dependent homs, and higher action.

Synthetic arrow induction exhibits the mathematical payoff. The canonical
Sigma-transport arrow $\\rho$ turns reflexive data into a section over all
outgoing arrows, and the composition motive normalizes to $q\\circ p$.
Usable categorical binders exhibit the implementation payoff. Recursive
ordinary and displayed variable occurrences compile to explicit internal
owners and are checked by one generic TypeScript LF, including object and
arrow behavior.

Sieve-centered geometry exhibits the local-to-global payoff. Invertibility is
first the stable sieve $D_R(f)$, a localization represents that question
pointwise, finite certified charts generate a topology, and direct cover
completion constructs a Cat-valued reflector through whole return, glue,
silent coherence, recursion, and uniqueness. The boundaries beyond that
reflector remain as explicit as the construction itself.

Groupoidal realization exhibits the higher-dimensional payoff. Circle
encode/decode restores the inverse powers absent from WalkingEnd, generic
groupoidification characterizes maps out by a whole equivalence, and the Gray
walking square retains a directed interchanger rather than erasing it into an
equation.

Dependent simplexes exhibit the recursive payoff: face observations and
higher action arise from iterated outgoing paths rather than an expanding list
of coherence fields.

The current system is bounded, but the design question has a concrete answer:
readable binders, explicit Core, checked categorical computation, an
authoritative Lambdapi kernel, sieve-based local geometry, free groupoidal
realization, and a client-side reviewer fit into one architecture. The
remaining work is to extend its mathematical and transfer coverage without
losing that internalized, normalization-first discipline.

# References

1. The Univalent Foundations Program. *Homotopy Type Theory: Univalent
   Foundations of Mathematics*. Institute for Advanced Study, 2013.
2. Kosta Došen. *Cut Elimination in Categories*. Trends in Logic 6. Kluwer
   Academic Publishers, 1999.
3. The Lambdapi contributors. *Lambdapi User Manual*.
   [lambdapi.readthedocs.io](https://lambdapi.readthedocs.io/).
4. The emdash contributors. *emdash v3.2 sources*. Accompanying artifact.
5. Max Zeuner. *Univalent Foundations of Constructive Algebraic Geometry*.
   arXiv:2407.17362v1, 2024.
6. Pierre-Marie Pédrot. “Pursuing Shtuck.” Preprint, 2023. HAL:
   hal-04251754v1.
7. Amar Hadzihasanovic. *Combinatorics of Higher-Categorical Diagrams*.
   arXiv:2404.07273v2, 2024.
