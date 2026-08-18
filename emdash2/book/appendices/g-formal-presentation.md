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
express functoriality, naturality, induction, and universal properties. The
active Lambdapi v3.2 development authors and checks that calculus and remains
the mathematical authority.

The canonical mathematical surface used by this book is deliberately more
spacious than any one executable grammar. A renewed TypeScript product now
implements a bounded route from readable categorical binders to explicit
emdash Core and a small dependent logical framework. That route makes a
reviewed fragment directly usable; it does not become a second categorical
kernel or define the mathematics retroactively.

The architecture therefore distinguishes these roles before its two
executable paths meet in the operational diagram that follows:

| Layer or role | Responsibility | Present status |
| --- | --- | --- |
| canonical mathematical surface | the notation and rule presentation used by this book | active for prose, comments, and examples; not a parser grammar |
| scoped contextual elaboration | recursively interprets reviewed categorical variables, binders, neutral applications, and structural forms against typed expectations | active for the bounded direct-TypeScript and text profiles |
| typed outer-LF declarations | validate selected higher-level declarations and expand them into ordinary LF declarations and rules | active for adjunction assumptions and one bounded dependent-structure form; no new trusted Core node |
| backend-neutral explicit emdash Core | records the selected logical and categorical owners without committing to one runtime backend | active TypeScript intermediate representation |
| generic TypeScript dependent LF | checks Core terms, performs conversion and bounded reduction, and runs the reviewed proof-time rules | active for the recorded product boundary |
| active Lambdapi v3.2 kernel | authors the categorical declarations, computation, and proof-time comparisons used as mathematical authority | active and checked in the cited modules; also the conformance oracle |
| external semantic models | interpret a stated kernel fragment in mathematical categories or other structures | separate mathematical work; available only in selected examples |

```text
canonical mathematical surface (broader than implemented text)
  -> reviewed direct TypeScript / text expressions
  -> scoped contextual elaboration
  -> explicit Core terms ------------------------------------------+
                                                                  |
typed host declarations                                           |
  -> deterministic expansion                                      |
  -> ordinary LF declarations and rules --------------------------+
                                                                  |
                                                                  v
generic TypeScript LF checker / conversion / bounded runtime
  -> optional deterministic Lambdapi emission / conformance

active authored Lambdapi v3.2 kernel = mathematical authority
external models                    = separate mathematical work
```

The text adapter is not the checker, an authoring macro is not a new term
former, the TypeScript checker is not the active mathematical authority, and
the implemented text subset is not the whole canonical surface. External
interpretation is separate again. Keeping these roles distinct lets us say
exactly which claims are checked computation, which are executable
presentation, which are mathematical exposition, and which remain research.

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

The source graph is larger than a useful reading list. The following map
groups adjacent modules by mathematical responsibility; the evidence
register supplies the exact owner and reviewer for each cited claim.

| Module family | Formal role |
| --- | --- |
| `emdash3_2.lp` | categorical nucleus: classifiers, iterated homs, functors, transfors, directed families, cuts, and universal-construction interfaces |
| `emdash3_2_presheaves.lp`, `emdash3_2_sieves.lp`, `emdash3_2_sites.lp` | presheaves, higher and ordinary sieves, pullback, and the direct Grothendieck-topology laws |
| `emdash3_2_generated_topologies.lp`, `emdash3_2_sieve_extensions.lp`, `emdash3_2_site_basis.lp`, `emdash3_2_ringed_sites.lp` | least generated topology, whole matching/section families, basis comparison, and ringed-site presentations |
| `emdash3_2_direct_cover_*.lp` | return/glue/silent cover completion, recursion, topology-locality, whole Hom universality, and the resulting Cat-valued reflector |

| Module family | Formal role |
| --- | --- |
| `emdash3_2_commutative_algebra.lp` through the polynomial and localization modules | set-carrier rings and structured maps, finite unit-ideal data, free extension, universal localization, and whole localization comparisons without polynomial or fraction syntax |
| the commutative-algebra presheaf, affine-points, affine-Zariski, ringed-site, and affine-scheme modules | the invertibility sieve $D(f)$, localization representation, generated big Zariski topology, coordinate presheaf, and assumption-explicit affine presentations |
| the ringed-space cover, affine-chart, site-relative-scheme, and chart-overlap modules | one supplied global ringed object, constructively generated covers, whole actual-slice restrictions, affine realizations, topology-local rings, and inherited overlaps |
| `emdash3_2_commutative_algebra_laurent.lp`, `emdash3_2_commutative_algebra_scheme_laurent_overlaps.lp`, `emdash3_2_commutative_algebra_projective_line.lp` | universal-property coordinate inversion on one literal overlap and the supplied projective-line boundary; no graded `Proj` construction |
| `emdash3_2_eq1_*.lp`, `emdash3_2_nat_arithmetic.lp`, `emdash3_2_walking_end_hit.lp` | equality-valued higher action, reusable arithmetic, and the WalkingEnd encode-decode development |
| the groupoidal-closure, Integer, Circle, truncation, and connectedness modules | path-former comparisons, successor-localized integers, Circle encode–decode, classified truncation, and the selected connectedness consumer |
| the groupoidal-interval, walking-comparison, and groupoidification modules | two finite free-inversion tests, category-indexed formation and whole unit, target extension/restriction, whole mapping equivalence, compositor, and Interval recovery |
| the whole-laxity and Gray profile/right-closure modules | displayed and ordinary whole laxity surfaces, computational strict-functor codes, the shared Gray hom profile, one selected right closure, and the derived walking interchanger |
| `emdash3_2_checks.lp` and `examples/` | executable diagnostics and independent reviewer-facing witnesses rather than mathematical owners |

Imports use `require`; `open` brings imported public names into scope. The
file split records dependency and evidence ownership. A conceptual chapter
may use several owners, and one source family may support several chapters;
neither direction is forced to mirror the table of contents.

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

### Selected Groupoidal HITs And Free Inversion

The groupoidal signatures used by the fourth spiral share the ordinary
equality eliminator but select different constructor boundaries.

| Construction | Formation and introduction | Selected elimination and computation | Whole boundary |
| --- | --- | --- | --- |
| Circle | `Circle_grpd`, `circle_base`, `circle_loop` | unrestricted dependent `circle_ind`; point beta and dependent `PathOver` loop beta compute | ordinary constant-family `ap` beta is propositional; the based loop carrier is equivalent to Integer |
| Interval | `Interval_grpd`, `interval_i0`, `interval_i1`, `interval_seg` | dependent `interval_ind`; both endpoint betas and dependent segment beta compute | ordinary segment `ap` beta is propositional; WalkingArrow supplies the free-inversion comparison |
| classified truncation | `Trunc_ntype(n,A)` in `NType_cat(n)`, with point `trunc_intro` | elimination only into classified $n$-truncated fibres; point beta computes | decoding exposes `Trunc_grpd(n,A)` and retained truncation evidence without identifying the result with an arbitrary equivalent carrier |
| groupoidification | `Groupoidify(C)` with one whole unit $\eta_C:C\to\mathsf{Path}(\mathsf{Groupoidify}(C))$ | recursion computes on represented points and on dependent action over represented arrows | extension and restriction are whole functors with path-valued beta/eta and retained higher action |

The Circle and Interval path-constructor computations are attached to
dependent action:

$$
\operatorname{apd}
  (\mathsf{circle\_ind}(D,b,\ell),\mathsf{loop})
\rightsquigarrow \ell,
$$

and analogously for `interval_ind` at `seg`. Passing to a constant family
produces the familiar homogeneous path only after the general bridge from
constant-family `PathOver` to `ap`. The resulting equation is internal
equality, not a second rewrite. This keeps one higher-constructor owner while
still recovering the usual recursion theorem.

For a category $C$ and groupoid $G$, the free-inversion boundary is the whole
mapping equivalence

$$
\operatorname{Hom}_{\mathsf{Grpd}}
  (\mathsf{Groupoidify}(C),G)
\simeq_{\omega}
\operatorname{Functor}
  (C,\mathsf{Path}(G)).
$$

Restriction is path action followed by precomposition with $\eta_C$;
extension is the categorical-HIT recursor varying in the entire source
representation. Their beta and eta are paths between whole functors, so their
first and next hom actions remain available. This is the target-side universal
property for every fixed $C$. The present package does not yet construct the
action of `Groupoidify` on an arbitrary source functor or assemble the
resulting adjunction.

<!-- evidence:CIRCLE-HIT-COMPUTATION -->
<!-- evidence:WALKING-INTERVAL-GROUPOIDIFICATION -->
<!-- evidence:GENERIC-GROUPOIDIFICATION-MAPPING -->

> **Formal status — checked selected signatures.** Evidence
> `CIRCLE-HIT-COMPUTATION`, `WALKING-INTERVAL-GROUPOIDIFICATION`, and
> `GENERIC-GROUPOIDIFICATION-MAPPING`. These are computationally reviewed HIT
> slices with whole action; they do not constitute a general HIT declaration
> compiler or a complete computational HoTT metatheory.

### Whole Laxity And The Profiled Gray Closure

The strict naturality cuts of the historical prototype do not exhaust the
internal action. Before pointwise projection, the displayed hom calculus owns
a whole laxity transformation. Ordinary post/left and pre/right comparisons
are transparent specializations of that displayed owner, and the functor
compositor is its identity-transfor specialization:

$$
\phi^F_{g,f}:F[g]\circ F[f]\Longrightarrow F[g\circ f].
$$

Because $f$ still ranges over a whole hom category, one further hom action can
observe how $\phi$ varies. A path-valued target makes the comparison
invertible. A decoded strict-functor code instead makes the selected
compositor compute to identity. These are target and profile specializations
of one action, not duplicate functor theories.

The category $\mathsf{GrayHom}_{\mathrm{lax}}(A,B)$ uses strict-functor codes
as objects and reuses the ambient transfor and higher-hom tower between their
decoded carriers. One selected right closure is checked:

$$
\mathsf{GrayHom}_{\mathrm{lax}}(A\otimes_R B,C)
\simeq_{\omega}
\mathsf{GrayHom}_{\mathrm{lax}}
  \bigl(A,\mathsf{GrayHom}_{\mathrm{lax}}(B,C)\bigr).
$$

Coevaluation at the walking-arrow shape exposes four vertices and two
coordinate routes. Projecting the already-existing whole post/left laxity
action supplies their oriented interchanger and retains its next action. No
independent square axiom is introduced. The checked slice does not supply the
mirror closure, tensor functoriality and coherence, or a full Crans–Gray
biclosed monoidal structure.

<!-- evidence:FUNCTORD-WHOLE-LAXITY -->
<!-- evidence:GRAY-COMPUTATIONAL-PROFILE -->
<!-- evidence:GRAY-RIGHT-CLOSURE -->

> **Formal status — checked selected profile.** Evidence
> `FUNCTORD-WHOLE-LAXITY`, `GRAY-COMPUTATIONAL-PROFILE`, and
> `GRAY-RIGHT-CLOSURE`. The result is a computational stress test for the
> foundations, not a reclassification of every existing functor as globally
> lax or strict.

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
layer. The renewed TypeScript path compiles a reviewed subset into the
explicit owners described above:

| Stage | Implemented bounded profile | Retained boundary |
| --- | --- | --- |
| parse | located `^f`, `^n`, `^fd`, and `^nd` binders, neutral application, selected constructors, and grouped displayed contexts | not the complete book or Lambdapi grammar |
| elaborate | typed expected classifiers route recursively through the existing contextual categorical program | no arbitrary pointwise-to-coherent synthesis |
| select owner | reviewed operation families lower to internal categorical and structural owners | no whole-library owner-acquisition claim |
| check and reduce | the generic TypeScript LF checks explicit Core, compares terms, and executes the bounded runtime | no global metatheory |
| conform | optional deterministic Lambdapi emission and a bounded oracle compare selected results with the active kernel | no production Lambdapi dependency |

Elaboration may recover information; it may not invent mathematics. If a
pointwise family lacks arrow action, the elaborator must report missing
coherence rather than synthesize an arbitrary transfor. If lower-star and
upper-star action are both type-correct, the written variance or expected
type must disambiguate them.

### Surface Forms And Explicit Targets

The canonical notation includes:

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
`@tapp1_fapp0 A B F G x y eta f`.

The source notation does not have to expose all seven parameters, but the
result must typecheck as that operation or an explicitly documented
equivalent owner. Readability changes what the author writes, not what the
checker trusts.

**One compositional motif, four binder modes.** Binder modes say how a
variable is allowed to vary. The reviewed executable forms are

```text
λ^f  x : A. ...
λ^n  k : K. ...
λ^fd a : E. ...
λ^nd k : K. ...
```

The mode belongs to the lambda. The classifier annotation after the variable
may be omitted when the bidirectional expected classifier supplies it, but
the mode is not inferred from that annotation. The mathematical telescope
notation $k:^{n}K$ therefore records the same natural/indexed role as
`λ^n k : K. ...` without pretending that mathematical declarations and
executable binders are literally the same grammar. Ordinary object binding
in the outer LF uses its ordinary dependent lambda.

The four modes are easiest to compare around one compositional motif. Let
$H:A\to B$ be an ordinary functor. Let $E,D,Q:K\to\mathsf{Cat}$ be directed
families, $FF:E\to D$ and $GG:D\to Q$ displayed functors, and $s$ a coherent
section of $E$. Finally, let
$\eta:F_0\Rightarrow F_1$ and $\theta:F_1\Rightarrow F_2$ be displayed
transfors. At successive categorical levels the same idea appears as:

| Mode | Representative expression | Mathematical reading |
| --- | --- | --- |
| `^f` | `λ^f x : A. H x` | an ordinary functorial variable inside one category |
| `^n` | `λ^n k : K. (GG k) ((FF k) (s k))` | a base variable whose result is a coherent section of $Q$ |
| `^fd` | `λ^fd a : E. GG (FF a)` | an object varying in a displayed family, retaining its hidden base index |
| `^nd` | `λ^nd k : K. composeCells (theta k) (eta k)` | a coherent family of cells between displayed functors, one hom level higher |

These are not four spellings for an ordinary lambda. The `^n` form must
respect transport in the base; the `^fd` form must retain displayed object and
arrow action; the `^nd` form must construct a transfor rather than a bare
pointwise family. In each case the expected classifier selects a reviewed
internal construction. If that construction is absent, elaboration fails
instead of accepting a JavaScript callback with an external naturality
promise.

Ordinary nesting already shows why recursive scope matters. Assume
`A, B, C : Cat` and `E : Functor B (Functor_cat A C)`. The reviewed
expression is:

```text
λ^f x : A. λ^f y : B. E y x
```

This term has classifier `Functor A (Functor_cat B C)`. Neutral application first
selects the action of `E` on `y` and then its action on `x`. Recursive
abstraction lowers the result through the existing
`exchange-functor-abstraction` owner before explicit Core is checked.

No external functoriality equation accompanies the source expression. The
selected owner already carries object and arrow action, and the resulting
explicit Core is checked by the same generic LF as other terms.

### Dependency Levels And Independent Siblings

Displayed contexts make the distinction between dependency and independence
visible. A representative mixed telescope is

```text
λ^fd (a : A; b : B, c : C; d : D). fibrePair b c
```

It has dependency levels `A; B,C; D`. A semicolon advances to a family over the
preceding total context, while a comma groups independent siblings over the
same prefix. The middle pair lowers through the transparent fibrewise product,
displayed pairing, Sigma projections, and reindexing owners. Thus `b` and `c`
may be paired, weakened, contracted, or exchanged fibrewise; no exchange of
`a` across a classifier depending on `a` is implied. Object and base-arrow
behavior remain internal to those owners rather than being supplied as
external coherence evidence.

The implemented normal form is not limited to the displayed four-variable
example. It supports any finite sequence of these canonical dependency
levels, with finite sibling groups at a level, for the reviewed displayed
functorial and displayed-natural constructions. Separately, the category
resolver can descend through any finite number of qualified Hom-category
levels over its supported roots, and the indexed-section route can compose a
finite rigid chain of displayed functors on a section. These depth results do
not amount to arbitrary dependency or variance graphs. Exchange
across a dependency edge, unrestricted mixed introduction and currying, and
coherence synthesis outside the qualified grammar remain open.

### Declaration Convenience Without New Mathematics

Some repetition belongs to the surrounding logical framework rather than to
categorical terms. Two direct-TypeScript declaration forms remove that
repetition before explicit Core is checked.

For an adjunction, `assumeAdjunction` receives already declared functors,
unit, and counit. It expands to an ordinary `Adjunction(F,G)` assumption and
two proof-time agreements identifying the declared transformations with the
kernel's stable unit and counit observations. A second form accepts a counit
and a coherent whole hom-profunctor transpose. In both cases the declaration
preserves the distinction between proof-time agreement and runtime
conversion: independently named maps do not silently become new reduction
rules for the categorical kernel.

For a finite dependent package, `declareStructure` expands one
unparameterized, nonrecursive, single-constructor structure into an opaque
carrier, an injective constructor, named primitive projections, and one
ordered, subject-reducing beta rule for each projection. Later field types may
depend on earlier fields, which is the essential convenience for mathematical
presentations. The form generates no record eta, eliminator, recursion,
positivity theorem, general inductive declaration, or browser/text syntax.

Both conveniences are conservative in the practical architectural sense:
their output consists of the same ordinary LF declarations and rules that
could have been written explicitly. Neither adds a trusted Core node or a
Lambdapi mathematical owner. The elaborator improves the act of stating a
presentation; it cannot turn missing structure or coherence into a theorem.

### Located Text And The Browser Reviewer

The text adapter accepts a small, located language rather than a string that
is later treated as trusted code. It records source spans, parses the reviewed
binders, grouped contexts, neutral whitespace application, and selected term,
category, and displayed-family constructors, then delegates typing and owner
selection to the same contextual program used by direct TypeScript. A failure
therefore reports its parsing, resolution, or elaboration phase together with
the source location. It is not a second action table or checker.

The integrated browser reviewer makes this path inspectable without a server.
Its twelve editable examples span the four binder modes, the canonical
sibling/Sigma context, qualified recursive Hom categories, and finite rigid
section chains. The current natural-binder example is the two-step section

```text
λ^n k : K. (GG k) ((FF k) (s k))
```

from the running motif above. For an accepted expression the client displays
the explicit backend-neutral Core, inferred and expected classifiers, and the
structural owners used in lowering. For a rejected edit it displays the
source-located diagnostic. The same page can run the outer-LF/ordinary/
displayed research report, retain the minimal explicit-Core playground, and
open the generated book. All of this execution is client-side; Lambdapi is an
optional development oracle, not a browser or production dependency.

### Historical Prototype And Retained Boundary

The repository history contains an older TypeScript feasibility prototype
with generic bidirectional checking, holes, unification, rewriting, and
proof-state machinery. Those mechanisms informed the renewed work, but its
stale category-specific layer is not an authority for v3.2. The renewed
product instead targets backend-neutral explicit Core aligned with active
owners and uses Lambdapi only as an optional conformance oracle.

The current path is deliberately bounded: it does not parse every notation
in the book, accept arbitrary dependency or variance graphs, synthesize
coherence from an unstructured pointwise function, or mechanically transfer
the whole Lambdapi library. Its qualified finite-depth results are neither
one hard-coded example nor a complete surface language. They are explicit
continuation boundaries, not hidden assumptions of the examples that run.

<!-- evidence:FORMAL-ELABORATION-BOUNDARY -->

> **Formal status — research boundary.** Evidence
> `FORMAL-ELABORATION-BOUNDARY`. The direct-TypeScript and categorical-text
> paths, explicit Core, generic checker/evaluator, bounded adjunction and
> dependent-structure declarations, client-side reviewer, and optional
> conformance route are executable for the reviewed profile. A complete
> compiler for the canonical surface, arbitrary displayed coherence, a
> general record or inductive facility, and whole-library transfer are not
> claimed. The active Lambdapi sources remain the mathematical authority.

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
kernel computes without depending on a traditional front end. The bounded
elaborator improves usability without changing the foundation, and future
semantic models may justify larger fragments without becoming a second
source language. That is the formal sense in which functorial type theory
begins from categorical computation.
