<a id="appendix-formal-presentation"></a>

# Appendix G. Formal Presentation Of Functorial Type Theory

The mathematical chapters have used rules from the beginning: an identity
path eliminates by reflexivity, a functor acts on an arrow, a transfor
absorbs a naturality cut, and a representing comparison eliminates a
universal map. This appendix puts those rules in one formal architecture.
It follows the discipline of Appendix A of the
[HoTT Book](#ref-hott-book)—contexts and judgments first, then rule families,
extensions, and metatheory—but changes the order of explanation at one
decisive point.

In functorial type theory, category theory is not added later as a model of a
previously specified, traditional term calculus. The explicit categorical
calculus is already the computational core. Its objects include categories,
iterated homs, functors, transfors, and directed families; its reductions
express functoriality, naturality, induction, and universal properties. A
friendlier end-user language may later elaborate into that core, and external
models may interpret it, but neither layer defines the calculus retroactively.

The architecture is therefore:

| Layer | Role | Present status |
| --- | --- | --- |
| computational categorical kernel | explicit classifiers, owners, rewrite rules, and proof-time comparisons accepted by [Lambdapi](#ref-lambdapi) | active and checked in the cited modules |
| canonical mathematical surface | the notation and rule presentation used by this book | active for prose, comments, and examples; not a parser grammar |
| optional elaborator | recovers implicit categories and endpoints, checks binder modes, and compiles readable notation to explicit owners | future interface |
| external semantic models | interpret a stated kernel fragment in mathematical categories or other structures | separate mathematical work; available only in selected examples |

The operational direction is

```text
mathematical surface
        |
        | optional future elaboration
        v
explicit categorical owner term  --->  Lambdapi checking and reduction
        |
        | separately proved interpretation
        v
external semantic model
```

The lower arrow is not part of parsing, and the upper arrow is not part of
semantics. Keeping them separate is what lets us say exactly which claims are
checked computation, which are mathematical presentation, and which remain
research.

<a id="appendix-formal-presentation-g1"></a>

## G.1 Judgments, Contexts, And Classifiers

A formal presentation begins with judgments made in contexts. We use
$\Gamma$ for a finite ordered list of declarations. The basic external
judgments have the schematic forms

$$
\Gamma\;\mathsf{ctx},
\qquad
\Gamma\vdash T:\mathsf{TYPE},
\qquad
\Gamma\vdash t:T,
\qquad
\Gamma\vdash t\equiv u:T.
$$

These are metatheoretic assertions about expressions. In particular,
`t:T` is not itself an internal proposition whose inhabitant is a proof that
`t` has type `T`. Lambdapi checks the judgment while reading a declaration,
definition, rule, or assertion.

Contexts are ordered because later entries may depend on earlier ones:

$$
x:A,\quad y:B(x),\quad z:C(x,y).
$$

Substitution replaces a declared variable by a term of the required type and
acts in every later entry and conclusion. Renaming, weakening, exchange when
dependencies permit it, and substitution are structural operations of the
ambient dependent framework. They are not constructors of an internal
`Context` classifier in the active emdash kernel.

### External Types And Decoded Classifiers

The kernel uses two related universes. `TYPE` is Lambdapi's ambient type
level. `Grpd : TYPE` is the small groupoidal or type-like classifier
universe used by emdash, and

$$
\tau:\mathsf{Grpd}\longrightarrow\mathsf{TYPE}
$$

decodes a classifier to the ambient type of its elements. Thus the book's
readable judgment $a:A$ normally abbreviates the literal judgment
`a : τ A` for `A : Grpd`.

Categories live at the ambient level:

$$
\mathsf{Cat}:\mathsf{TYPE}.
$$

Their object and arrow collections are internal classifiers:

$$
\begin{aligned}
\operatorname{Obj}(C)&:\mathsf{Grpd},\\
\operatorname{Hom}_{C}(x,y)&:\mathsf{Cat},\\
\operatorname{Hom}(C,x,y)
  :=\operatorname{Obj}(\operatorname{Hom}_{C}(x,y))
  &:\mathsf{Grpd}.
\end{aligned}
$$

The second line is the source of higher structure. If $f,g:x\to y$, then a
2-cell $\alpha:f\to g$ is an object of
$\operatorname{Hom}_{\operatorname{Hom}_{C}(x,y)}(f,g)$; repeating the same
construction exposes higher cells without changing the grammar at each
dimension.

The main internal classifiers used in the book are:

| Mathematical classifier | Literal owner | Decoded inhabitants |
| --- | --- | --- |
| objects of $C$ | `Obj C` | `τ (Obj C)` |
| arrows $x\to_C y$ | `Hom C x y` | `τ (Hom C x y)` |
| functors $A\to B$ | `Functor A B` | `τ (Functor A B)` |
| transfors $F\Rightarrow G$ | `Transf F G` | `τ (Transf F G)` |
| Cat-valued families over $K$ | `Catd K` | `τ (Catd K)` |
| displayed functors $E\to D$ | `Functord E D` | `τ (Functord E D)` |
| displayed transfors $FF\Rightarrow GG$ | `Transfd FF GG` | `τ (Transfd FF GG)` |

This distinction prevents two common category mistakes. First,
`C : Cat` is not an object of some silently assumed set of all categories;
it is an ambient kernel judgment. Second, an arrow classifier is not merely a
set of morphisms: it is the object classifier of another category and can
therefore be iterated.

### Six Ways To Compare Expressions

Several notations that resemble equality have different force.

| Notation | Layer | Meaning |
| --- | --- | --- |
| $t\rightsquigarrow u$ in this book; `t ↪ u` in source | runtime | a selected oriented rewrite makes $u$ the computational form |
| $t\equiv u$ | external conversion | the checker regards the terms as definitionally convertible using active computation |
| `unif_rule t ≡ u ↪ [...]` | proof-time elaboration | a unification problem is replaced by narrower subproblems; neither side is selected as a runtime normal form |
| $p:x=_A y$ | internal mathematics | `p` inhabits an equality classifier and can be eliminated by `ind_eqr` |
| $A\simeq B$ | internal mathematical structure | specified maps and inverse/coherence evidence, such as `TypeEquiv` or a categorical comparison |
| $t=u$ in status-labeled free-form prose | mathematical development | a theorem to be proved in the named future interface, not an undisclosed kernel conversion |

A runtime rule does not by itself assert equality reflection. An internal
path does not make its endpoints definitionally identical. A proof-time
unification rule is not a path constructor, and an equivalence is not an
unlabeled use of conversion. Chapters 1 and 9 rely on precisely these
distinctions.

<!-- evidence:FORMAL-KERNEL-PRESENTATION -->

> **Formal status — checked.** Evidence
> `FORMAL-KERNEL-PRESENTATION` covers the active categorical classifiers,
> their application operations, and representative executable checks. The
> displayed turnstile notation is the book's metanotation; it is not a new
> internal judgment former.

<a id="appendix-formal-presentation-g2"></a>

## G.2 The Mathematical Categorical Presentation

We now give a compact signature in the notation of the book. It is the
human-readable presentation of the kernel, not an untyped concrete grammar.
Implicit arguments are suppressed only when their recovery is forced by the
displayed source and target.

### Categories And Iterated Homs

The core categorical judgments are

$$
\frac{}{C:\mathsf{Cat}},
\qquad
\frac{C:\mathsf{Cat}}{x:\operatorname{Obj}(C)},
\qquad
\frac{x,y:\operatorname{Obj}(C)}
     {f:\operatorname{Hom}_{C}(x,y)}.
$$

Every object has an identity, and composable arrows have a composite:

$$
\operatorname{id}_x:x\to_Cx,
\qquad
\frac{f:x\to_Cy\quad g:y\to_Cz}{g\circ f:x\to_Cz}.
$$

The convention is always “first $f$, then $g$.” Identity and associativity
are available at the intended comparison layers. The implementation does not
install unrestricted reassociation as a general runtime rewrite.

Opposite categories reverse the hom endpoints:

$$
\operatorname{Hom}_{C^{\mathrm{op}}}(x,y)
\rightsquigarrow
\operatorname{Hom}_{C}(y,x).
$$

The path category embeds the equality-local fragment:

$$
\operatorname{Obj}(\mathsf{Path}(A))\rightsquigarrow A,
\qquad
\operatorname{Hom}_{\mathsf{Path}(A)}(x,y)
\rightsquigarrow\mathsf{Path}(x=_Ay).
$$

This is a groupoidal specialization. It does not identify arbitrary directed
arrows with equality paths.

### Functors And Their Iterable Action

For categories $A,B$, the category $A\vdash B$ has functors as objects:

$$
\frac{A,B:\mathsf{Cat}}{A\vdash B:\mathsf{Cat}},
\qquad
\frac{}{F:\operatorname{Obj}(A\vdash B)}.
$$

We write the second judgment as $F:A\to B$. A functor has object action and,
for every pair $x,y:A$, a functor on the whole hom-category:

$$
\begin{aligned}
F[x]&:\operatorname{Obj}(B),\\
F_{x,y}&:
\operatorname{Hom}_{A}(x,y)
\longrightarrow
\operatorname{Hom}_{B}(F[x],F[y]),\\
F[f]&:=F_{x,y}[f].
\end{aligned}
$$

The hom action, not only its value at one arrow, is primary. It can act again
on a 2-cell between arrows, and its own hom action continues the same pattern.
At the first capped level, the selected functoriality cuts are

$$
F[\operatorname{id}_x]\rightsquigarrow\operatorname{id}_{F[x]},
\qquad
F[g]\circ F[f]\rightsquigarrow F[g\circ f].
$$

### Transfors And Family Action

For parallel functors $F,G:A\to B$, the category $F\Rightarrow G$ is their
first hom in the functor category. A transfor
$\eta:F\Rightarrow G$ has a point component

$$
\eta_x:F[x]\longrightarrow G[x]
$$

and, more fundamentally, an off-diagonal hom functor

$$
\eta_{x,y}:
\operatorname{Hom}_{A}(x,y)
\longrightarrow
\operatorname{Hom}_{B}(F[x],G[y]).
$$

We write $\eta[f]$ for its value at $f:x\to y$. Its two adjacent naturality
cuts compute:

$$
\begin{aligned}
G[g]\circ\eta[f]&\rightsquigarrow\eta[g\circ f],\\
\eta[f]\circ F[h]&\rightsquigarrow\eta[f\circ h].
\end{aligned}
$$

The diagonal component is the identity-arrow instance of this family action.
Thus naturality is not a proposition pasted onto a bare family of arrows. It
is part of an operation whose higher action remains available.

### Directed Families, Totals, And Sections

A directed Cat-valued family over $K$ is written

$$
E:K\longrightarrow\mathsf{Cat}.
$$

For $k:K$ it has a fibre $E[k]$, and for $p:k\to_Kk'$ it has transport

$$
E[p]:E[k]\longrightarrow E[k'].
$$

A displayed functor $FF:E\to D$ contains fibre functors and off-diagonal
comparison cells over base arrows. In book notation its classifier is

$$
k:^{n}K\ ;\ E[k]\vdash D[k].
$$

Displayed transfors arise by taking the next hom in this category. The
`Catd`, `Functord`, and `Transfd` facades keep these levels visible
instead of flattening them into pointwise functions.

Two categorical dependent formers organize families:

$$
\sum_{k:^{n}K}E[k]
\qquad\text{and}\qquad
\prod_{k:^{n}K}E[k].
$$

The Sigma total has objects $(k,u)$ with $u:E[k]$. An arrow consists of a base
arrow $p:k\to k'$ and a fibre arrow

$$
E[p](u)\longrightarrow u'
\quad\text{in }E[k'].
$$

The Pi category has coherent sections as objects. Its evaluation at $k$ is a
functor to $E[k]$, not merely a carrier-level application function.

### Chosen Arrows And Natural Families

The two represented-hom actions expose the first Došen-style cut discipline.
For $u:x\to_Ay$,

$$
u_*(g)=u\circ g
\quad\text{and}\quad
u^*(h)=h\circ u.
$$

Lower star is covariant postcomposition; upper star is contravariant
precomposition. With a functor $H$, the acting arrow is $H[u]$, so
$(H[u])^*(h)=h\circ H[u]$. By contrast, $\eta[f]$ uses the whole natural
family $\eta$, not one selected arrow. Structural and universal eliminators
continue this progression.

The product/projection benchmark of Chapter 9 is a theorem in an arbitrary
category $K$ equipped with products. Its Cat-specialized executable probe is
evidence about the current owner calculus, not a restriction of the
mathematical statement to the category of categories.

### Signature-To-Owner Map

The following table records the correspondence without treating readable
notation as a second implementation.

| Readable operation | Active owner |
| --- | --- |
| $x\to_Cy$ | `Hom_cat C x y` and `Hom C x y` |
| $A\vdash B$ | `Functor_cat A B` |
| $F[x]$, $F[f]$ | `fapp0`, `fapp1_func`, `fapp1_fapp0` |
| $F\Rightarrow G$ | `Transf_cat F G` |
| $\eta_x$, $\eta[f]$ | `tapp0_fapp0`, `tapp1_func`, `tapp1_fapp0` |
| $E:K\to\mathsf{Cat}$ and $E[k]$ | `Catd K` and `Fibre_cat E k` |
| displayed functors and transfors | `Functord` and `Transfd` |
| $\sum_kE[k]$, $\prod_kE[k]$ | `Sigma_cat E` and `Pi_cat E` |
| $u_*$, $u^*$ | `hom_postcomp_*` and `hom_precomp_along_*` |

<!-- evidence:CAT-ITERATED-HOMS -->
<!-- evidence:CAT-FUNCTOR-CALCULUS -->
<!-- evidence:TRANSF-POINT-OFFDIAGONAL -->
<!-- evidence:TRANSF-STRICT-NATURALITY -->
<!-- evidence:CAT-DIRECTED-FAMILIES -->

> **Formal status — checked.** Evidence `CAT-ITERATED-HOMS`,
> `CAT-FUNCTOR-CALCULUS`, `TRANSF-POINT-OFFDIAGONAL`,
> `TRANSF-STRICT-NATURALITY`, and `CAT-DIRECTED-FAMILIES` support the
> displayed nucleus. The typography in this section is canonical
> mathematical surface notation; the next section shows literal source.

<a id="appendix-formal-presentation-g3"></a>

## G.3 The Checked Lambdapi Presentation

The active source is a Lambdapi signature. This section gives representative
literal excerpts, enough to explain how the mathematical presentation is
checked without reproducing the kernel.

### Declarations And Definitions

At the universe boundary the source says:

```lambdapi
constant symbol Grpd : TYPE;
injective symbol τ : Grpd → TYPE;

constant symbol Cat : TYPE;
symbol Obj : Cat → Grpd;
injective symbol Hom_cat :
  Π (A : Cat) (X_A Y_A : τ (Obj A)), Cat;
injective symbol Hom (A : Cat) (X_A Y_A : τ (Obj A)) : Grpd
≔ Obj (Hom_cat A X_A Y_A);
```

These lines exhibit three declaration policies.

- A `constant symbol` cannot receive a definition or rewrite rules.
  `Cat`, `Grpd`, and the WalkingEnd constructors use this literal policy.
- A plain `symbol` may be an undefined operation that later receives rules,
  or it may have a transparent body after `≔`.
- An `injective symbol` gives the unifier a rigid constructor-like head.
  The modifier is a trusted declaration choice and is used only at selected
  classifier and stable-owner boundaries.

Lambdapi also supports an `opaque` modifier for a defined symbol whose body
must not reduce. In the book, “opaque WalkingEnd” describes the mathematical
effect of its constant declarations; it does not claim that those lines use
the literal `opaque symbol` spelling.

Implicit parameters appear in square brackets and explicit parameters in
parentheses. Prefix `@` exposes normally implicit parameters at a use site.
In rule patterns, a dollar-prefixed name such as `$A` is a pattern
variable, while `_` asks typing and unification to recover a slot that is
not a genuine discriminator.

### Rewrite Owners

Functor application is declared at a full hom level and a capped arrow level:

```lambdapi
symbol fapp1_func : Π [A B : Cat], Π (F_AB : τ (Functor A B)),
  Π [X_A Y_A : τ (Obj A)],
  τ (Functor
    (Hom_cat A X_A Y_A)
    (Hom_cat B (fapp0 F_AB X_A) (fapp0 F_AB Y_A)));

symbol fapp1_fapp0 : Π [A B : Cat], Π (F_AB : τ (Functor A B)),
  Π [X_A Y_A : τ (Obj A)],
  Π (f : τ (Hom A X_A Y_A)),
  τ (Hom B (fapp0 F_AB X_A) (fapp0 F_AB Y_A));

rule fapp0 (fapp1_func $F_AB) $f
  ↪ fapp1_fapp0 $F_AB $f;
```

The last line is runtime computation: observing the full hom-action at one
arrow exposes the capped action. The generic identity and composition rules
then contract $F[\operatorname{id}]$ and
$F[g]\circ F[f]$. Concrete functor constructors inherit those rules; they do
not each receive private copies of ordinary functoriality.

The same ownership policy governs transfors. `tapp0_fapp0` observes a point
component, while `tapp1_func` and `tapp1_fapp0` own off-diagonal action.
The two strict naturality rewrites are attached to that generic action. A
constructor-specific rule is justified only when it expresses extra
constructor computation, not the fact that something already typed as a
transfor is natural.

### Proof-Time Unification

Some stable category presentations should elaborate together without one
being erased at runtime. For rigid hom-category heads the source includes:

```lambdapi
unif_rule Obj (Hom_cat $A $X $Y) ≡ Obj (Hom_cat $A' $X' $Y')
  ↪ [ $A ≡ $A'; $X ≡ $X'; $Y ≡ $Y' ];
```

This rule decomposes one proof-time unification problem into three. It does
not rewrite an object classifier during execution, prove an internal path,
or assert that `Obj` is globally injective for every category construction.

Similar narrow comparisons relate the ordinary functor-category presentation
to `Catd_cat`, and the ordinary transfor presentation to
`Functord_cat`.

Associativity illustrates the boundary particularly well. The two bracketings
of ordinary composition are compared at proof time, and `comp_assoc`
packages a propositional witness. There is no global runtime rule that
continually reassociates every composite. Represented hom actions,
`tapp1`, and universal comparisons instead own the specific cuts they can
normalize without losing higher action.

### Assertions And Negative Assertions

Executable diagnostics are source commands, not theorem prose. A small
example is:

```lambdapi
assert ⊢ Nat_grpd : Grpd;
assert ⊢ zero : τ Nat_grpd;
assertnot ⊢ @eq_refl Nat_grpd zero ≡ tt;
```

The first two ask Lambdapi to accept a type and an inhabitant. The last checks
that two terms are not definitionally convertible. A typed reflexivity term is
used when a proof-time unification rule must be exercised; a bare conversion
assertion does not test that same mechanism.

The diagnostic suite is intentionally separate from implementation owners.
Permanent examples and assertions provide regression evidence, while the
evidence register connects book claims to both declarations and reviewers.

### Modules And Ownership

The current organization is:

| Module | Formal role |
| --- | --- |
| `emdash3_2.lp` | active categorical kernel and universal-construction owners |
| `emdash3_2_eq1_hom_action.lp` | derived native equality-valued next-hom and groupoidality layer |
| `emdash3_2_eq1_evidence_property.lp` | evidence-property and finite-height consequences |
| `emdash3_2_nat_arithmetic.lp` | reusable Nat operations and sethood |
| `emdash3_2_walking_end_hit.lp` | selected WalkingEnd signature, eliminator, computation, and comparison |
| `emdash3_2_checks.lp` | executable diagnostics |

Imports use `require`; `open` brings imported public names into scope.
The file split expresses dependency and evidence ownership. It is not a claim
that every conceptual chapter already has its own kernel module.

Three source policies are essential for reading rules correctly.

1. Match a computation at its semantic owner and retain stable heads needed
   by later higher action.
2. Keep inferred rule slots anonymous unless a slot is a measured type,
   subject-reduction, or decision-tree guard.
3. Use runtime rewrites only for intended normal forms; use narrowly typed
   proof-time comparisons when neither side should compute to the other.

<!-- evidence:FORMAL-KERNEL-PRESENTATION -->

> **Formal status — checked.** Evidence
> `FORMAL-KERNEL-PRESENTATION` records the representative declaration,
> action, rule, module, and diagnostic surface described here. Successful
> source checking warrants these interfaces; it does not establish the global
> metatheorems listed in G.7.

<a id="appendix-formal-presentation-g4"></a>

## G.4 Formation, Introduction, Elimination, And Computation

The familiar rule schema remains useful, provided we add a sixth question
suited to directed mathematics.

| Rule aspect | Question |
| --- | --- |
| formation | when is the classifier or categorical object well formed? |
| introduction | what data construct an inhabitant or structured object? |
| elimination | how may an inhabitant be observed or used? |
| computation | what does elimination do to introduced data? |
| uniqueness or universality | is an arbitrary inhabitant recovered, propositionally compared, or characterized by a mapping property? |
| action and coherence | how does the construction act on arrows and higher cells as its parameters vary? |

The last row is not optional decoration. A pointwise formula may answer the
first five questions at objects while failing to define a functor, transfor,
or displayed family.

### Equality Induction

For $A:\mathsf{Grpd}$ and $x,y:A$, equality formation gives $x=_Ay$.
Reflexivity introduces an inhabitant
$\mathsf{refl}_x:x=x$. Right-based elimination fixes $y$, takes

$$
P:\prod_{x:A}(x=y)\longrightarrow\mathsf{Grpd},
\qquad
u:P(y,\mathsf{refl}_y),
$$

and returns

$$
\mathsf{ind\_eqr}(P,u,p):P(x,p)
\quad\text{for }p:x=y.
$$

Its literal-reflexivity beta computes:

$$
\mathsf{ind\_eqr}(P,u,\mathsf{refl}_y)
\rightsquigarrow u.
$$

Path action, dependent path action, symmetry, and transitivity are derived
uses. No equality reflection, uniqueness of identity proofs, or global
path-eta rule is added. At the categorical layer, `Path_cat` and
`path_map_func` package equality and function action so that higher path
action can be iterated.

<!-- evidence:TT-EQUALITY-INDUCTION -->

> **Formal status — checked.** Evidence `TT-EQUALITY-INDUCTION`.
> Formation, reflexivity, right-based elimination, beta, `ap`, and
> `apd` are active. A stronger global uniqueness principle is not silently
> inferred from the beta rule.

### Categories, Functors, And Transfors

`Cat`, `Obj`, and `Hom_cat` give formation for the categorical tower.
Identity and composition are introduction operations for arrows, while
iteration of `Hom_cat` eliminates an arrow into its next-cell context.
The selected unit and associativity comparisons say how these introductions
compose; there is no eliminator claiming that every category is freely
generated by its displayed arrows.

For a functor, formation is `Functor A B`. Its elimination operations are
`fapp0` and `fapp1_func`. The projection beta from full hom action to
`fapp1_fapp0` and the identity/composition cuts are its generic
computations. The active theory obtains inhabitants from named functor
constructors and categorical operations; the book does not posit one
record-style constructor whose fields may be supplied incoherently.

For a transfor, formation is `Transf F G`. Point and off-diagonal
application are eliminations. Identity-boundary, composition, and the two
naturality cuts are computations. The full off-diagonal functor is the action
clause: it says what happens not just to an arrow $f$ but to a higher cell
between possible values of $f$.

This gives a useful criterion:

> A point-component formula does not define a transfor until the
> off-diagonal arrow action and its next-hom behavior are supplied or
> explicitly deferred.

### Sigma Totals And Pi Sections

For $E:K\to\mathsf{Cat}$, categorical Sigma formation gives
$\Sigma_KE:\mathsf{Cat}$. An object is introduced as $(k,u)$ with $u:E[k]$.
The first projection and the fibre component eliminate it. A total arrow is
introduced by a pair

$$
\bigl(p:k\to k',
  \alpha:E[p](u)\to_{E[k']}u'\bigr).
$$

Projection and composition rules compute on this structure. The
`sigma_intro_transf` packages the inclusions $E[k]\to\Sigma_KE$ naturally
in $k$, so introduction also has a directed action rather than only a pair
constructor.

Pi formation gives the section category $\Pi_KE$. Evaluation is packaged by
`pi_eval_transf`, whose component at $k$ is the functor

$$
\operatorname{ev}_k:\Pi_KE\longrightarrow E[k].
$$

The evaluation projection computes through `piapp0_func`. Constant
sections and pullback of sections supply important introductions, but the
current interface does not assert a general categorical Pi-eta or a fully
packaged dependent adjunction. Those stronger universal laws require the
base-arrow, off-diagonal, and Beck–Chevalley data described in Chapter 16.

At the groupoid layer, encoded Sigma and Pi classifiers separately provide
dependent pairs, projections, pointwise path observation, and the selected
`happly`/`funext` equivalence. The categorical Sigma/Pi operations above
must not be flattened into those carrier-level formers: their objects vary in
categories and their arrow action is part of the interface.

<!-- evidence:CAT-SIGMA-PI -->
<!-- evidence:TT-SIGMA-PI-PATHS -->

> **Formal status — checked nucleus.** Evidence `CAT-SIGMA-PI` and
> `TT-SIGMA-PI-PATHS`. The active rules cover the cited constructors,
> projections, evaluation, and action. General dependent adjunctions remain
> the research boundary recorded in Chapter 16.

### The WalkingEnd Rule Package

The walking endomorphism makes every row of the schema visible:

| Aspect | Selected WalkingEnd datum |
| --- | --- |
| formation | `WalkingEnd_cat : Cat` |
| object introduction | `walking_base : Obj(WalkingEnd)` |
| arrow introduction | `walking_loop : Hom(WalkingEnd,base,base)` |
| height datum | `walking_end_is_one_cat : IsNCat(1,WalkingEnd)` |
| contextual algebra | $R,D:W\to\mathsf{Cat}$, $u:R[*]\to D[*]$, and $\sigma:D[\ell]\circ u\Rightarrow u\circ R[\ell]$ |
| elimination | `walking_end_ind_funcd R D u sigma : Functord R D` |
| base computation | the fibre component at $*$ reduces to $u$ |
| loop computation | the displayed action at $\ell$ reduces to the supplied component of $\sigma$ |
| uniqueness | no general initiality or contractibility theorem is currently packaged |
| action | the result is a displayed functor, so base-arrow and higher action are retained |

The section eliminator specializes $R$ to the terminal family. The ordinary
recursor specializes both families to constants. They are derived views of
the contextual eliminator, not three independent postulates. The literal
constructor betas are attached to stable generic observers, with two narrow
projection joins for the concrete ordinary-recursion consumers.

<!-- evidence:WE-SIGNATURE -->
<!-- evidence:WE-CONTEXTUAL-ELIMINATOR -->
<!-- evidence:DHIT-DERIVED-ELIMINATORS -->

> **Formal status — checked.** Evidence `WE-SIGNATURE`,
> `WE-CONTEXTUAL-ELIMINATOR`, and
> `DHIT-DERIVED-ELIMINATORS`. The absence of a uniqueness theorem is part
> of the formal statement, not a prose omission.

### Adjunction And Weighted Representability

An adjunction illustrates a rule package whose principal eliminations are
observations rather than a public record constructor. For named functors
$F:R\to L$ and $G:L\to R$, the classifier

$$
\mathsf{Adjunction}(F,G)
$$

forms the proposition-like structure accepted by the kernel. From
$J:\mathsf{Adjunction}(F,G)$ one eliminates the selected unit and counit:

$$
\eta:\operatorname{id}_R\Rightarrow GF,
\qquad
\varepsilon:FG\Rightarrow\operatorname{id}_L.
$$

The two triangle cuts compute at off-diagonal components. Their role is
exactly beta reduction: an introduction by a unit followed by elimination by
a counit contracts to the underlying map, and dually.

A weighted limit is presented one level more abstractly. Given
$F:J\to B$, $W:J'\rightsquigarrow J$, and $L:J'\to B$, formation gives the
classifier

$$
\mathsf{IsWeightedLimit}_{\mathrm{cov}}(F,W,L).
$$

An inhabitant is a computational comparison between the weighted-cone
profunctor and the representable hom profunctor. Reindexing and applying that
certificate eliminates it into inverse operations

$$
\mathsf{push}
\quad\text{and}\quad
\mathsf{pull}.
$$

Their composites reduce by the generic profunctor-comparison beta and eta
rules. The action clause is reindexing along every probe functor
$M:I\to B$; the universal property is not restricted to one set of global
elements. Adjunction mates then transport the whole comparison, which is why
right-adjoint preservation is a computation on certificates rather than a
fresh pointwise proof.

Existence for every diagram and uniqueness of representing objects are
separate theorems. The active classifier says what data certify a chosen
$L$; it does not postulate a global limit operator or a native univalent
uniqueness package.

<!-- evidence:ADJ-TRIANGLE-CUTS -->
<!-- evidence:WEIGHTED-LIMIT-REPRESENTABILITY -->

> **Formal status — checked.**
> Evidence `ADJ-TRIANGLE-CUTS` and
> `WEIGHTED-LIMIT-REPRESENTABILITY`.
>
> The formation/elimination/computation interface is active. Semantic end
> formulas, general existence, and univalent uniqueness remain separately
> status-labeled mathematics.

<a id="appendix-formal-presentation-g5"></a>

## G.5 Elaboration And Canonical Surface Syntax

Readable notation is indispensable, but it need not be the foundational
layer. A future elaborator should compile notation into the explicit owners
described above:

| Stage | Responsibility | Status |
| --- | --- | --- |
| parse | build a scoped syntax tree from declared notation | future for the complete canonical surface |
| elaborate | infer omitted categories, endpoints, variances, and implicit arguments; solve typed constraints | partial prototype evidence only |
| select owner | choose the stable categorical constructor or application head required by the notation | design contract in the canonical-syntax report |
| check | submit the explicit term to Lambdapi and accept only a typed result | active kernel/toolchain |
| reduce | use the kernel's selected rewrite owners | active kernel/toolchain |

Elaboration may recover information; it may not invent mathematics. If a
pointwise family lacks arrow action, the elaborator must report missing
coherence rather than synthesize an arbitrary transfor. If lower-star and
upper-star action are both type-correct, the written variance or expected
type must disambiguate them.

### Surface Forms And Explicit Targets

The current canonical notation includes:

| Surface | Explicit target |
| --- | --- |
| `a ->^C b` | `Hom_cat C a b` |
| `A ⊢ B` | `Functor_cat A B` |
| `F => G` | `Transf_cat F G` |
| `E[k]` | `Fibre_cat E k` |
| `A[k^-] ⊢_[k] B[k]` | `Functor_catd A B` |
| `Π (k :^n K), E[k]` | `Pi_cat E` |
| `u_*(g)` | a `hom_postcomp_*` application |
| `u^*(h)` | a `hom_precomp_along_*` application |

For example, if $\eta:F\Rightarrow G$ and $f:x\to_Ay$, the readable term
$\eta[f]:F[x]\to_BG[y]$ elaborates toward the fully explicit owner

```lambdapi
@tapp1_fapp0 A B F G x y eta f
```

The source notation does not have to expose all seven parameters, but the
result must typecheck as that operation or an explicitly documented
equivalent owner.

Binder modes express how variables may vary. A functorial variable carries
ordinary action, a natural/index variable participates in a coherent family,
and an object-only variable contributes no arrow action of its own. The
book's settled notation uses forms such as $k:^{n}K$ for the natural/indexed
role. A future grammar must specify scoping and mode inference precisely
before the additional mode annotations become user syntax.

### What The Parent Prototype Establishes

The parent emdash repository contains an older TypeScript prototype. Its term
data distinguish explicit and implicit applications and include category,
functor, transfor, off-diagonal application, displayed-action, and binder-mode
nodes. Its elaboration code demonstrates bidirectional checking, fresh
implicit holes, typed constraints, and some mode validation. This is useful
feasibility evidence: endpoint recovery for categorical operations can be
treated as compilation rather than made part of every mathematical formula.

Its present parser, however, covers a small ASCII language of `Type`,
`fun`, Pi arrows, application, lets, implicit braces, and holes. It does
not parse the complete canonical categorical notation, and the prototype is
not a production compiler from this book's surface to the active Lambdapi
modules. Some of its semantic assumptions also predate the current v3.2
owners.

Consequently:

- the prototype is read-only historical and feasibility evidence;
- no book theorem, source check, render, or release imports it;
- its AST is not the normative surface grammar;
- any renewed elaborator requires a separate RFC against the current
  canonical syntax and current kernel owners.

<!-- evidence:FORMAL-ELABORATION-BOUNDARY -->

> **Formal status — research boundary.** Evidence
> `FORMAL-ELABORATION-BOUNDARY`. The compilation stages above are a
> concrete architecture, not a claim that an end-to-end current elaborator
> exists. The active book depends only on the mathematical surface and the
> checked Lambdapi sources.

<a id="appendix-formal-presentation-g6"></a>

## G.6 Directed Higher-Inductive Signatures

A directed higher-inductive signature must specify more than a list of
generators. At minimum it needs:

1. object, arrow, and higher-cell constructors with typed boundaries;
2. the categories and families into which they may be interpreted;
3. recursion, dependent elimination, and any contextual elimination
   principles;
4. coherence data demanded by varying source and target families;
5. constructor computation at named observers;
6. action on arrows and higher cells of every varying parameter;
7. optional dimension or truncation evidence;
8. a statement of uniqueness or initiality when one has actually been proved.

The WalkingEnd signature is the selected worked instance. With
$W=\mathsf{WalkingEnd}$, $*:\operatorname{Obj}(W)$, and
$\ell:*\to_W*$, its contextual algebra is

$$
\begin{aligned}
R,D&:W\longrightarrow\mathsf{Cat},\\
u&:R[*]\longrightarrow D[*],\\
\sigma&:D[\ell]\circ u\Longrightarrow u\circ R[\ell].
\end{aligned}
$$

The eliminator returns

$$
\mathsf{ind}^{d}(R,D,u,\sigma):R\longrightarrow^{d}D.
$$

At the base, its fibre functor reduces to $u$. At the literal generator, its
displayed laxity component reduces to the supplied component of $\sigma$.
These are constructor beta rules. Generic functoriality and transfor
naturality own the remaining identity, composition, and ordinary naturality
cuts.

The coherence cell is directed:

$$
D[\ell]\circ u
\Longrightarrow
u\circ R[\ell].
$$

It is neither an equality nor an automatically invertible path. Reversing it
would define a different eliminator orientation. Supplying only its pointwise
components would also be incomplete, because the transfor must act on arrows
of $R[*]$ and on their higher cells.

The one-dimensional witness is separate signature data. It lets a later
directed 2-cell between parallel based arrows be converted to equality; it
does not make the generating 1-cell invertible. This separation is essential
to the normalization proof of Chapter 8.

The ordinary section eliminator and recursor are specializations:

$$
\begin{array}{c|c|c}
\text{view} & R & D\\
\hline
\text{contextual} & \text{arbitrary} & \text{arbitrary}\\
\text{section} & \text{terminal family} & \text{arbitrary}\\
\text{recursor} & \text{terminal family} & \text{constant family}.
\end{array}
$$

This relationship is an architectural requirement for a future signature
compiler: it should generate one coherent principle and derive weaker views,
not postulate unrelated recursors whose computations may disagree.

What is not yet active is equally specific. There is no general language of
directed cell boundaries, no compiler that generates contextual eliminators
and projection-stable beta rules, no general algebra category, and no theorem
that every such presentation is initial. A plausible implementation must
also generate focused diagnostics for typing, subject reduction, critical
pairs, and both possible projection orders.

<!-- evidence:DHIT-GENERAL-SCHEMA -->

> **Formal status — checked instance and research boundary.** Evidence
> `WE-SIGNATURE` and `WE-CONTEXTUAL-ELIMINATOR` support the complete
> selected instance. Evidence `DHIT-GENERAL-SCHEMA` records the missing
> general signature and compiler rather than extrapolating them from one HIT.

<a id="appendix-formal-presentation-g7"></a>

## G.7 Basic Metatheory And Its Boundary

A successful checker run is strong evidence that the submitted declarations
and rules satisfy the tool's current acceptance conditions. It is not, by
itself, a proof of every global property one might want from the combined
rewrite and unification theory. The current warranted statements are:

| Property | What this edition may say |
| --- | --- |
| typing of active sources | checked by bounded Lambdapi runs over the active module graph |
| local subject-reduction obligations of promoted rewrite rules | checked by Lambdapi's ordinary rule acceptance; not separately formalized as one global project theorem |
| selected computation | witnessed by promoted rules and focused positive and negative assertions |
| selected proof-time comparison | exercised by typed uses or typed reflexivity checks, not inferred merely from a conversion assertion |
| evidence traceability | checked syntactically from book markers to active owners and reviewers |
| build and render reproducibility | tested by the release tooling for the recorded source snapshot |
| global confluence | not established for the whole emdash rewrite and unification theory |
| strong normalization | not established for the whole theory |
| global canonicity | not established; only selected constructor and normalization computations are tested |
| decidable conversion or type checking as an emdash metatheorem | not claimed beyond observed behavior of the current Lambdapi toolchain on the active sources |
| consistency and semantic soundness | require model and metatheory proofs for a precisely stated fragment; they do not follow silently from compilation |

### Engineering Evidence Is Not A Metatheorem

The repository records warning inventories, focused owner-position probes,
critical-pair investigations, strict inferred-slot audits, and bounded full
checks. These practices are indispensable. They locate overlap risks, reject
ill-typed rules, compare reduction orders, and protect intended normal forms.
They still sample or delegate parts of a global theorem rather than proving
one in the object theory.

Warning counts are therefore diagnostics, not a numeric confluence proof.
A zero count would not establish normalization, and a nonzero count does not
by itself refute a deliberately joined computation. Likewise, deterministic
PDF output establishes release reproducibility, not mathematical consistency.

### The Role Of Models

`BNat` is a separate concrete one-object category whose endomorphisms are
natural numbers under addition. The checked functor from WalkingEnd to
`BNat` is meaningful model evidence for the selected generators and
recursor. The encode–decode theorem then proves much more about the based hom
inside the opaque source.

That model is not a soundness interpretation for all of `emdash3_2.lp`.
It does not interpret every higher category, displayed family, equality
principle, profunctor, or rewrite rule. A global consistency claim would
require a stated syntax fragment, an interpretation of every formation and
computation rule in that fragment, and a proof that conversion is preserved.

<!-- evidence:WE-BNAT-MODEL -->

> **Formal status — checked local model evidence.** Evidence
> `WE-BNAT-MODEL` supports the separate WalkingEnd-to-BNat interpretation.
> No global soundness theorem is inferred from it.

### Adaptation Of The HoTT Formal Appendix

The four source units of the HoTT formal appendix enter this presentation as
follows:

| HoTT source unit | Functorial adaptation |
| --- | --- |
| A.1, first presentation | G.2 gives the readable categorical signature; G.5 keeps it distinct from a parser |
| A.2, second presentation | G.1 and G.3 state judgments and literal source; G.4 organizes representative rule families |
| A.3, homotopy type theory | equality and univalence remain qualified layers, while G.6 presents the selected directed WalkingEnd extension |
| A.4, basic metatheory | this section retains the taxonomy of properties but replaces inherited conclusions by the conservative status matrix above |

The adaptation deliberately does not import the HoTT appendix's normalization
or metatheoretic conclusions as results about emdash. Different rewrite
owners, proof-time unification rules, opaque categorical structure, and
directed higher cells require their own theorem.

<!-- evidence:FORMAL-METATHEORY-BOUNDARY -->

> **Formal status — research boundary.** Evidence
> `FORMAL-METATHEORY-BOUNDARY`. The matrix states what current checks
> establish and gives a concrete specification for future metatheory. Global
> confluence, strong normalization, canonicity, decidability, consistency,
> and semantic soundness remain unclaimed until separately proved.

The resulting architecture is intentionally asymmetric. The categorical
kernel can already compute without waiting for a traditional front end. A
future elaborator can improve usability without changing the foundation, and
future semantic models can justify larger fragments without becoming a
second source language. That is the formal sense in which functorial type
theory begins from categorical computation.
