<a id="chapter-30"></a>

# 30. Cartesian Structure And Dependent Products

A product is usually introduced by a diagram and a universal property. A
pullback is introduced by a square. A dependent product is introduced as a
right adjoint to substitution. These descriptions are mathematically correct,
but they can hide the common computational question:

> What happens when a universal construction is immediately eliminated, and
> which whole operation must remain visible so that the reduction can be
> iterated at the next categorical level?

This chapter answers that question for selected cartesian and indexed
structure. It begins with binary products and the empty product. It then moves
to slices, where postcomposition is always available and pullback reindexing
is selected structure. A second selected right adjoint completes the chain

$$

\Sigma_u \dashv u^* \dashv \Pi_u.

\tag{30.1}
$$

The three functors in (30.1) act between whole slice categories. Their units,
counits, off-diagonal actions, and mate operations therefore retain higher
arrows. That retained action is what distinguishes an internal computational
presentation from a collection of objectwise bijections.

## 30.1 A Chosen Product Is A Whole Functor

Let $C$ be a category. A chosen binary-product structure begins with a whole
functor

$$
P:C\times C\longrightarrow C.
\tag{30.2}
$$

For objects $A,B$ write $A\times B=P(A,B)$. The two projections are not
unrelated arrows chosen afresh at every pair. They are components of whole
transformations

$$
\kappa_1:P\Rightarrow\operatorname{pr}_1,
\qquad
\kappa_2:P\Rightarrow\operatorname{pr}_2.
\tag{30.3}
$$

Thus a change in either input already has a natural action. If
$f:X\to A$ and $g:X\to B$, pairing supplies

$$
\langle f,g\rangle:X\longrightarrow A\times B.
\tag{30.4}
$$

In the internal presentation, pairing itself is a whole transformation between
represented Hom families. Fixing $X,A,B$ projects it to a functor

$$
\operatorname{Hom}_C(X,A)\times\operatorname{Hom}_C(X,B)
\longrightarrow
\operatorname{Hom}_C(X,A\times B).
\tag{30.5}
$$

Consequently a higher arrow between two pairs of legs is sent to a higher arrow
between their pairings. The operation is not capped at (30.4).

This selected product functor must be kept distinct from
$\mathsf{ProductCat}(A,B)$, the category whose objects and arrows are pairs.
The latter exists for every $A$ and $B$ and is used to state the source of
$P$; it does not choose products inside an arbitrary $C$.

## 30.2 The Triangular Product Cuts

[Došen's cut-elimination perspective](#ref-dosen-cut-elimination) motivates
antecedential product operations that make projection followed by further
composition into one visible cut. For a suitable arrow $h$, write

$$
K_1^a(h)=h\circ\kappa_1,
\qquad
K_2^a(h)=h\circ\kappa_2.
\tag{30.6}
$$

The basic product reductions are

$$
\begin{aligned}
K_1^a(h)\circ\langle f,g\rangle
  &\rightsquigarrow h\circ f,\\
K_2^a(h)\circ\langle f,g\rangle
  &\rightsquigarrow h\circ g.
\end{aligned}
\tag{30.7}
$$

The right-hand sides are smaller cuts: the product introduction has
disappeared, and the unobserved component is absent. Pairing also distributes
through precomposition,

$$
\langle f,g\rangle\circ k
\rightsquigarrow
\langle f\circ k,g\circ k\rangle,
\tag{30.8}
$$

while projection postcomposition accumulates,

$$
h\circ K_i^a(f)
\rightsquigarrow
K_i^a(h\circ f).
\tag{30.9}
$$

Finally, pairing the two projections removes the detour entirely:

$$
\langle\kappa_1,\kappa_2\rangle
\rightsquigarrow
\operatorname{id}_{A\times B}.
\tag{30.10}
$$

These rules do more than prove that a product exists. They select a normal
form for arrows built from projections, pairing, and composition. The generic
action of the whole functor $P$ agrees at proof time with the triangular map

$$
P[f,g]
\doteq
\langle K_1^a(f),K_2^a(g)\rangle,
\tag{30.11}
$$

where $\doteq$ records proof-time agreement rather than a competing runtime
orientation.

There is also a transparent unpairing functor that postcomposes an arrow with
both projections. Pairing followed by unpairing and unpairing followed by
pairing have checked pointwise inverse paths. Equality of the two whole
functor composites is a stronger packaging step and is not inferred merely
from those pointwise paths.

<!-- evidence:TRIANGULAR-BINARY-PRODUCTS -->

> **Formal status — checked.** Evidence `TRIANGULAR-BINARY-PRODUCTS`. A
> selected whole product functor, whole projections, whole represented-family
> pairing, stable $K_1^a/K_2^a$ and pairing observations, beta,
> distribution, eta, and selected normalization rules are active. The generic
> product-functor action has an explicit proof-time comparison with the
> triangular map. No free-cartesian syntax or global commuting decision
> procedure is claimed.

### Whole Pairing Through The Product Adjunction

In an ordinary category, the same chosen product functor P is right adjoint
to the diagonal Δ:C→C×C. The computational presentation explicitly supplies
Δ⊣P for the original binary-product choice. Its counit is the pair of original
projections, and its unit component is the original pairing of two identities.
It selects no second product object.

The family lift from [Chapter 12](#chapter-12) now transposes whole
transformations. Given U,V,W:B→C, a pair of transformations U⇒V and U⇒W
has one whole pairing U⇒P(V,W). Unpairing uses the original projections;
the adjunction owns their cancellation. This reusable Cartesian interface
is upstream of the additive and homological applications in Chapter 31.

<!-- evidence:ORDINARY-PRODUCT-ADJUNCTION -->

> **Formal status — checked interface.** Evidence
> `ORDINARY-PRODUCT-ADJUNCTION`. `one_cat_binary_product_adjunction` and
> the ordinary product-category profile are declared structural operations
> over the existing `BinaryProducts` data. Whole family pairing/unpairing
> and their formulas are derived operations.

## 30.3 The Empty Product

A chosen terminal object $t$ is the empty product. Its computational structure
is one whole transformation

$$
!:\operatorname{id}_C\Rightarrow\operatorname{Const}_t.
\tag{30.12}
$$

The component at $A$ is the canonical arrow

$$
!_A:A\longrightarrow t.
\tag{30.13}
$$

Because (30.12) is whole, an arrow $h:A\to B$ has an off-diagonal
observation, and the canonical terminal cut computes:

$$
!_B\circ h\rightsquigarrow !_A.
\tag{30.14}
$$

The unrestricted uniqueness statement

$$
f=!_A
\qquad(f:A\to t)
\tag{30.15}
$$

is not oriented as a variable-headed rewrite. Instead the object/groupoid Hom
classifier $\operatorname{Hom}_C(A,t)$ is contractible, recentered at the
component $!_A$. Equation (30.15) is then a derived equality path. In
particular $!_t=\operatorname{id}_t$ is derived without forcing every visible
endomorphism of a terminal object to rewrite before its context is known.

<!-- evidence:TERMINAL-OBJECT-COMPUTATION -->

> **Formal status — checked.** Evidence `TERMINAL-OBJECT-COMPUTATION`. The
> selected terminal object has a whole canonical-arrow transformation,
> computing component and off-diagonal action, the cut (30.14), and
> contractible Hom classifiers. Arbitrary uniqueness is equality evidence;
> there is no bare-variable unifier or variable-headed runtime rule.

The thin selected cartesian package merely pairs the existing binary-product
and terminal-object capabilities. It adds no product, projection, terminal
arrow, rewrite rule, or unification rule of its own.

### Whole Categorical Contraction

Contractibility of the object groupoid of D does not account for its
noninvertible arrows. A categorical contraction instead supplies a whole
equivalence D≃1, where 1 is the terminal category. The current native
interface fixes the canonical forward functor D→1 and retains the inverse
functors and the existing whole inverse laws. Object-groupoid
contractibility is derived afterward as an observation of this data.

For a family E:K→Cat, the coherent version contracts the whole family map
E→const₁. Its selected inverse is one whole dependent functor. Evaluation
at k retains that inverse in the fibre E(k); it does not independently
choose a contraction for every fibre. The current Ω interface has
equality-valued laws between whole functors. This use of that interface does
not assert a general univalence theorem or reconstruct directed action from
objectwise paths.

<!-- evidence:WHOLE-CATEGORICAL-CONTRACTION -->

> **Formal status — checked.** Evidence `WHOLE-CATEGORICAL-CONTRACTION`.
> `CatContraction` and `CatdContraction` transparently specialize the existing
> `OmegaEquivAlong` interface. Inverse evaluation and the derived ordinary
> contraction are checked; no additional equivalence primitive is introduced.

### Terminal And Initial Adjunction Presentations

Write p:C→1 for the canonical functor and t:1→C for the chosen object.
Terminality has the categorical presentation p⊣t; initiality has the dual
presentation t⊣p. Their units and counits are whole transformations.

For ordinary C, the current extension supplies these two adjunctions from
the original selected terminal/initial capabilities. The generic adjunction
comparison then gives whole Hom mate functors, retained inverses and ordinary
uniqueness observations. The maps into 1 are the actual selected mates; they
are not cast to a preferred functor by equality transport.

Derived whole diagram comparisons relate the unit/counit arrow families
to the original terminal/initial arrow families. Both directions retain their
inverse maps, with computing point endpoints and proved whole endpoint and
inverse equations. The two former primitive family normalizers are no
longer needed. This keeps the original
terminal normal forms: the terminal component at t is propositionally equal
to idₜ and remains computationally distinct from it. Callers supply no
naturality-square data.

<!-- evidence:ORDINARY-TERMINAL-ADJUNCTIONS -->

> **Formal status — checked interface.** Evidence
> `ORDINARY-TERMINAL-ADJUNCTIONS`. The two ordinary adjunction presentations
> are explicit structural declarations. Their unit/counit, Hom comparison,
> inverse and ordinary contraction views are derived. They are not claimed
> as derivations from the original terminal β rules alone.

The general higher replacement of the primary terminality interface remains
a separate qualification problem. It must specify a whole Hom comparison
and its profiles, and distinguish the current computational DefIso adjunction
contract from a weaker higher equivalence. Removing the ordinary guard from
these declarations would not establish that extension.

## 30.4 Direct And Weighted Products

Chapter 16 describes weighted limits through representability. A binary
product can also be presented by a suitable weight and a strict
$\mathsf{DefIso}$ comparison. The direct triangular interface and the weighted
interface answer different implementation questions:

- the triangular interface chooses the runtime projection/pairing calculus;
- the weighted interface packages a stronger representability comparison in
  the general profunctor machinery.

The active adapter therefore takes the weighted comparison as supplied data
and records paths identifying its two projections with the triangular ones.
It does not fabricate a weighted witness from pointwise beta and eta alone.
This preserves both useful presentations without making either an alias for
the other.

## 30.5 Slices And The Always-Existing $\Sigma_u$

Fix an object $X$ of $C$. The slice $C/X$ organizes arrows ending at $X$.
Its objects may be written

$$
a=(A\xrightarrow{p}X).
\tag{30.16}
$$

For $u:X\to Y$, postcomposition is always available:

$$
\Sigma_u:C/X\longrightarrow C/Y,
\qquad
(A\xrightarrow{p}X)\longmapsto
(A\xrightarrow{u\circ p}Y).
\tag{30.17}
$$

These functors are the arrow action of one whole covariant family

$$
\mathsf{SliceSigma}(C):C\longrightarrow\mathsf{Cat}.
\tag{30.18}
$$

The fibre at $X$ is exactly $C/X$. Hence the domain of (30.17) is preserved
definitionally, and the structure arrow computes by ordinary postcomposition;
no equality transport is inserted to repair its endpoint.

The internal slice is directed. A slice arrow has an underlying base arrow and
a comparison cell in an iterated Hom. In a locally discrete category that cell
amounts to the usual commuting equality. In a general higher category it must
not be erased or replaced by a manually supplied equation.

## 30.6 Pullback As Chosen Base Change

Postcomposition does not choose a pullback domain. A chosen pullback structure
supplies the opposite-variance whole family

$$
\mathsf{SliceBaseChange}(PB):C^{\mathrm{op}}
\longrightarrow\mathsf{Cat},
\tag{30.19}
$$

again with exact fibre $C/X$. Its action at $u:X\to Y$ is

$$
u^*:C/Y\longrightarrow C/X.
\tag{30.20}
$$

The defining universal relationship is the existing adjunction

$$
\Sigma_u\dashv u^*.
\tag{30.21}
$$

Let its unit and counit be

$$
\eta^u:\operatorname{id}_{C/X}\Rightarrow u^*\Sigma_u,
\qquad
\varepsilon^u:\Sigma_u u^*\Rightarrow\operatorname{id}_{C/Y}.
\tag{30.22}
$$

They are actual whole transformations. Their off-diagonal actions are the
Došen operations

$$
\gamma_u^c(k)=\eta^u[k],
\qquad
\varphi_u^a(h)=\varepsilon^u[h].
\tag{30.23}
$$

For arrows of the appropriate slice types, the full rectangular cuts compute:

$$
\begin{aligned}
\varphi_u^a(h)\circ\Sigma_u\bigl(\gamma_u^c(k)\bigr)
  &\rightsquigarrow h\circ\Sigma_u(k),\\
u^*\bigl(\varphi_u^a(h)\bigr)\circ\gamma_u^c(k)
  &\rightsquigarrow u^*(h)\circ k.
\end{aligned}
\tag{30.24}
$$

Identity instances recover the ordinary unit and counit components and both
triangle identities. The readable slice terms normalize through opposite
restriction-oriented Sigma categories, so the active rectangle rules match
the exact surviving endpoints rather than defined aliases.

## 30.7 Mates And The Pullback Object

Fix $a$ in $C/X$ and $g$ in $C/Y$. The adjunction gives whole mate functors

$$
\begin{aligned}
\Phi_{a,g}:&\operatorname{Hom}_{C/Y}(\Sigma_u a,g)
 \longrightarrow\operatorname{Hom}_{C/X}(a,u^*g),\\
\Gamma_{a,g}:&\operatorname{Hom}_{C/X}(a,u^*g)
 \longrightarrow\operatorname{Hom}_{C/Y}(\Sigma_u a,g).
\end{aligned}
\tag{30.25}
$$

Their point formulas are

$$
\Phi(h)=u^*(h)\circ\eta^u_a,
\qquad
\Gamma(k)=\varepsilon^u_g\circ\Sigma_u(k).
\tag{30.26}
$$

The stable point and whole presentations compare at proof time with these
semantic bodies. Both point composites and both whole functor composites
reduce to identity. At the whole level, exact raw Hom-category guards retain
$a$ and $g$ after opposite normalization; a wildcard-only cancellation rule
would not be safe.

Now write $g:Z\to Y$. The selected pullback object is simply the slice object

$$
u^*(g)=(P\xrightarrow{\pi_1}X).
\tag{30.27}
$$

The counit component

$$
\varepsilon^u_g:\Sigma_u(u^*g)\longrightarrow g
\tag{30.28}
$$

has an underlying arrow $\pi_2:P\to Z$ and a directed cell

$$
g\circ\pi_2\Longrightarrow u\circ\pi_1.
\tag{30.29}
$$

Thus the pullback object, both projections, and the square are observations of
the selected slice object and counit. They are not independent fields.

A cone from $a$ to $g$ is exactly an object of

$$
\operatorname{Hom}_{C/Y}(\Sigma_u a,g).
\tag{30.30}
$$

The universal lift is $\Phi$, and cone recovery is $\Gamma$. There is no
pullback-specific cone constructor accepting two legs and a square witness.
In a locally discrete category, (30.29) and the projection cells recover the
ordinary strict equations.

<!-- evidence:PULLBACK-SLICE-BASE-CHANGE -->

> **Formal status — checked.** Evidence `PULLBACK-SLICE-BASE-CHANGE`. Chosen
> pullbacks form one whole exact-slice base-change family with
> $\Sigma_u\dashv u^*$, actual unit/counit transfors, full rectangular cuts,
> point and guarded whole mate cancellation, and derived pullback
> object/projection/square observations. Generic family substitution
> `Pullback_catd` remains a different construction.

## 30.8 Dependent Products In Slices

A category with chosen pullbacks need not have dependent products. The extra
structure selects a third whole slice family

$$
\mathsf{SliceDependentProduct}(DP):C\longrightarrow\mathsf{Cat}
\tag{30.31}
$$

with exact fibre $C/X$. Its action at $u:X\to Y$ is

$$
\Pi_u:C/X\longrightarrow C/Y.
\tag{30.32}
$$

The selected relationship is the second adjunction

$$
u^*\dashv\Pi_u.
\tag{30.33}
$$

Write its unit and counit as

$$
\eta^{\Pi,u}:\operatorname{id}_{C/Y}\Rightarrow\Pi_u u^*,
\qquad
\varepsilon^{\Pi,u}:u^*\Pi_u\Rightarrow\operatorname{id}_{C/X}.
\tag{30.34}
$$

Again these are the generic actual adjunction transformations. Their stable
off-diagonal observations satisfy

$$
\begin{aligned}
\varphi_{\Pi,u}^a(h)\circ
  u^*\bigl(\gamma_{\Pi,u}^c(k)\bigr)
  &\rightsquigarrow h\circ u^*(k),\\
\Pi_u\bigl(\varphi_{\Pi,u}^a(h)\bigr)\circ
  \gamma_{\Pi,u}^c(k)
  &\rightsquigarrow\Pi_u(h)\circ k.
\end{aligned}
\tag{30.35}
$$

The associated whole Hom correspondence is

$$
\operatorname{Hom}_{C/X}(u^*a,b)
\simeq
\operatorname{Hom}_{C/Y}(a,\Pi_u b).
\tag{30.36}
$$

The transparent transpose and untranspose functors have the familiar formulas

$$
h\longmapsto\Pi_u(h)\circ\eta^{\Pi,u}_a,
\qquad
k\longmapsto\varepsilon^{\Pi,u}_b\circ u^*(k),
\tag{30.37}
$$

and retain higher Hom action. The generic adjunction profunctor comparison
owns the varying-endpoint whole equivalence; no parallel mate theory is
introduced.

<!-- evidence:SLICE-DEPENDENT-PRODUCTS -->

> **Formal status — checked.** Evidence `SLICE-DEPENDENT-PRODUCTS`. A selected
> coherent dependent-product structure supplies the whole exact-slice family
> $\Pi_u$, the existing adjunction $u^*\dashv\Pi_u$, actual whole
> unit/counit transfors, both full rectangular cuts, transparent whole mate
> action, and the generic whole Hom comparison. It adds no specialized
> composite-point or identity-action rule.

## 30.9 The Three-Adjoint Chain

Combining (30.21) and (30.33) gives the promised chain

$$
\begin{aligned}
\Sigma_u &: C/X\longrightarrow C/Y,\\
u^* &: C/Y\longrightarrow C/X,\\
\Pi_u &: C/X\longrightarrow C/Y,
\end{aligned}
\qquad
\Sigma_u\dashv u^*\dashv\Pi_u.
\tag{30.38}
$$

The left adjunction says that changing a structure arrow by postcomposition is
freely related to pulling an object back. The right adjunction says that maps
out of a pullback are represented by a dependent product. Both statements are
internal equivalences of Hom categories with executable triangular cuts.

The neutral total capability

$$
\mathsf{SliceDependentProducts}(C)
\tag{30.39}
$$

packages a chosen pullback structure together with its indexed chosen
dependent-product structure. The name is deliberately weaker than
"locally cartesian closed category." To reach that conventional package the
development should still select the intended finite-limit convention and
derive exponentials in each slice. Beck-Chevalley comparison, Frobenius
reciprocity, pushout duality, and comparison with independently selected
weighted pullbacks are later coherence layers.

They are later layers, not reasons to replace the three whole families. Each
future comparison has well-typed endpoints built from the existing
$\Sigma_u$, $u^*$, and $\Pi_u$ actions.

## 30.10 The End Of The Sixth Spiral

The chapter began with the smallest structural detour:

$$
\kappa_i\circ\langle f,g\rangle.
$$

It ended with adjunctions between categories of structured arrows. The same
discipline governed every stage:

- keep the constructor or whole universal operation visible;
- reduce elimination after introduction to a smaller cut;
- use proof-time comparison when neither presentation should erase the other;
- retain higher action before projecting to points; and
- state coherence not yet constructed as a boundary rather than as an
  implicit equation.

The result is not a claim that all cartesian higher-category theory has been
completed. It is a checked computational spine on which the next coherence
questions can be asked without changing what products, pullbacks, or
dependent products mean.
