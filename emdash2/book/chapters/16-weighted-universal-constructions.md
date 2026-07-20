<a id="chapter-16"></a>

# 16. Weighted Universal Constructions

A limit is often introduced by drawing a cone and asking for a universal
vertex. That picture is indispensable, but it hides the operation that makes
the vertex universal: for every probe object, the category of cones must be
represented by a hom. Weighted limits expose this operation directly.

The resulting account is not a catalogue of products, equalizers, ends, and
Kan extensions. It is one theorem with several specializations:

$$
\text{weight and diagram}
\longrightarrow
\text{cone classifier}
\longrightarrow
\text{representing comparison}.
$$

The same comparison calculus that eliminated cuts in Chapter 9 then supplies
the universal beta and eta laws. Adjunction mates transport the comparison,
and therefore every right adjoint preserves every selected weighted limit for
which the comparison has been supplied.

Our mathematical conventions follow the Cat-enriched viewpoint of
[Kelly](#ref-kelly). The active artifact deliberately implements a narrower
computational interface: tensor and its two residuals are symbolic objects
with checked vertical beta/eta operations, not constructions from general
ends and coends. This distinction lets the theorem compute without claiming
semantic infrastructure that has not yet been built.

## 16.1 Weights Are Parameterized Shapes

Let

$$
F:J\longrightarrow B
$$

be a diagram. A parameterized covariant weight has the form

$$
W:J'\rightsquigarrow J,
\qquad
W:(J')^{\mathrm{op}}\times J\longrightarrow\mathsf{Cat}.
$$

For each $j':J'$, the partial functor $W(j',-)$ is a Cat-valued weight on
$J$. The first endpoint is contravariant, so an arrow $j'_0\to j'_1$ acts
from the weight at $j'_1$ to the weight at $j'_0$. This is exactly the
variance needed for the resulting representing objects to assemble into a
functor

$$
L:J'\longrightarrow B.
$$

The familiar unparameterized definition is the special case
$J'=\mathbf 1$. Retaining $J'$ is important: choosing one limit object for
each parameter is not enough. The comparison below must also make those
choices functorial in the parameter and iterable at the next hom level.

In the ordinary set-enriched case, a weight is a functor
$W:J\to\mathsf{Set}$. The set $W(j)$ describes how many copies, positions,
or generalized inputs the object $Fj$ contributes. In the Cat-valued case
those positions themselves have arrows, so a weighted cone carries coherence
along both $J$ and the internal categories $W(j',j)$.

## 16.2 The Profunctor Of Weighted Cones

For a probe object $b:B$ and a parameter $j':J'$, the expected category of
weighted cones is

$$
\operatorname{Cone}_{W}(b,F;j')
\simeq
[J,\mathsf{Cat}]
\bigl(W(j',-),\operatorname{Hom}_{B}(b,F-)\bigr).
$$

An object of this category is a natural family of arrows from $b$ into the
diagram, indexed by the weight. Its arrows are the corresponding higher
transformations. Varying $b$ acts by precomposition, while varying $j'$ acts
through the contravariant endpoint of $W$. Thus the cone construction has the
profunctorial type

$$
\operatorname{Cone}_{W}(F):B\rightsquigarrow J'.
$$

The active definition does not unfold the functor-category expression above.
It uses the covariant profunctor implication:

$$
\operatorname{Cone}_{W}(F)
:=
\operatorname{ProfImply}_{\mathrm{cov}}
\bigl(\operatorname{Hom}_{B}(-,F-),W\bigr).
$$

The literal owner is `WeightedCone_prof`, defined through
`Prof_imply_cov`. This is a useful separation. The mathematical formula says
what weighted cones mean in a semantic model with the necessary ends; the
implication is the stable computational owner used by the present theory.

## 16.3 Tensor And The Two Residuals

Suppose

$$
P:A\rightsquigarrow B,
\qquad
Q:B\rightsquigarrow X,
\qquad
O:A\rightsquigarrow X.
$$

Tensor makes the middle endpoint into a cut:

$$
P\otimes_B Q:A\rightsquigarrow X.
$$

There are two ways to solve a mapping problem against this composite. Holding
$Q$ fixed gives a right residual with type $A\rightsquigarrow B$; holding
$P$ fixed gives a left residual with type $B\rightsquigarrow X$. The active
interfaces are characterized by inverse operations

$$
\begin{aligned}
\operatorname{ProfMap}
 \bigl(P,\operatorname{ProfImply}_{\mathrm{cov}}(O,Q)\bigr)
&\simeq
\operatorname{ProfMap}(P\otimes_B Q,O),\\
\operatorname{ProfMap}
 \bigl(Q,\operatorname{ProfImply}_{\mathrm{con}}(P,O)\bigr)
&\simeq
\operatorname{ProfMap}(P\otimes_B Q,O).
\end{aligned}
$$

Evaluation introduces the tensor cut; lambda abstraction removes it. In both
orientations the selected composites reduce:

$$
\begin{aligned}
\lambda(\operatorname{eval}(t))&\rightsquigarrow t,\\
\operatorname{eval}(\lambda(u))&\rightsquigarrow u.
\end{aligned}
$$

These are universal-property beta and eta laws in the same sense as the
upper-star and `tapp1` reductions of Chapter 9. They choose a stable owner for
associativity rather than globally reassociating arbitrary composites.

<!-- evidence:PROF-CLOSED-CALCULUS -->

> **Formal status — checked.** Evidence `PROF-CLOSED-CALCULUS`.
> `Prof_imply_cov` and `Prof_imply_con` are the two opaque residual
> objects. `Prof_eval_cov_map`, `Prof_lambda_cov_map`,
> `Prof_eval_con_map`, and `Prof_lambda_con_map` expose the checked
> fixed-endpoint beta/eta calculus. This status does not assert an end formula
> for either residual.

The weighted cone is now forced rather than guessed. For every
$P:B\rightsquigarrow J'$,

$$
\operatorname{ProfMap}
 \bigl(P,\operatorname{Cone}_{W}(F)\bigr)
\simeq
\operatorname{ProfMap}
 \bigl(P\otimes_{J'}W,\operatorname{Hom}_{B}(-,F-)\bigr).
$$

A map on the right is precisely a $P$-shaped family of $W$-weighted cone
data. The residual packages all such maps into one profunctor. In this form,
a weight is not an annotation on a limit symbol: it is the profunctor cut
that the cone classifier abstracts.

The tensor itself remains an opaque fixed-middle composite. Its current
functorial action and shaped-element constructor are checked, but a semantic
coend, associator, unitors as equivalences, and the coherence of a full
profunctor bicategory are not consequences of those interfaces.

<!-- evidence:PROF-TENSOR -->
<!-- evidence:PROF-GENERAL-COEND -->

> **Formal status — checked interface and research boundary.** Evidence
> `PROF-TENSOR` covers the selected tensor object, outer-endpoint
> reindexing, vertical bifunctoriality, and shaped tensor elements. Evidence
> `PROF-GENERAL-COEND` records what is missing. The displayed residual
> mapping laws are checked only through the fixed-endpoint eval/lambda
> operations above.

## 16.4 A Weighted Limit Is A Representation

A $W$-weighted limit of $F$ is a functor

$$
L:J'\longrightarrow B
$$

together with a representation of the cone profunctor:

$$
\Phi:
\operatorname{Cone}_{W}(F)
\simeq
\operatorname{Hom}_{B}(-,L-).
$$

At a pair $(b,j')$, this says

$$
\operatorname{Cone}_{W}(b,F;j')
\simeq
\operatorname{Hom}_{B}(b,Lj').
$$

The direction of the hom is worth checking. A limit receives a cone *from*
the probe $b$, so maps from $b$ to the limit classify cones from $b$. A
colimit will reverse this direction in Chapter 17.

There are two active representation classifiers. The ordinary classifier
`IsWeightedLimit_cov_iso` asks for isomorphism evidence in the profunctor
category. The computational classifier `IsWeightedLimit_cov_comp` asks for a
`ProfComparison`. The latter retains selected forward and inverse maps whose
beta and eta laws compute on every incoming profunctor map.

<!-- evidence:WEIGHTED-LIMIT-REPRESENTABILITY -->

> **Formal status — checked.** Evidence
> `WEIGHTED-LIMIT-REPRESENTABILITY`. `WeightedCone_prof` constructs the
> cone profunctor, while `IsWeightedLimit_cov_iso` and
> `IsWeightedLimit_cov_comp` give the ordinary and computational
> representation interfaces. The checked claim is the interface and its
> reductions, not existence of a weighted limit for every diagram.

This is the universal-property row of the rule schema in
[Appendix G.4](#appendix-formal-presentation-g4). Formation fixes
$F$, $W$, and the proposed representing functor $L$; introduction supplies a
comparison certificate; push and pull are eliminations; their inverse
reductions are beta and eta; and reindexing in the probe is the action clause.
Existence and univalent uniqueness are additional principles, not hidden
fields of the checked classifier.

This formulation also separates *being* a limit from *choosing* one. A
theorem may accept a comparison for a particular $F$, $W$, and $L$ without
postulating a global limit operator. In a univalent specialization,
representability can later make the choice unique in the appropriate sense;
the preservation theorem below does not need that stronger uniqueness
package.

## 16.5 Universal Introduction And Elimination

Let

$$
M:I\longrightarrow B
$$

be a shaped family of probe objects, and let

$$
R:I\rightsquigarrow J'
$$

index a family of test data. Reindexing $\Phi$ along $M$ gives inverse
operations

$$
\begin{aligned}
\mathsf{push}:&
\operatorname{ProfMap}
 \bigl(R,\operatorname{Cone}_{W}(M,F)\bigr)
\longrightarrow
\operatorname{ProfMap}
 \bigl(R,\operatorname{Hom}_{B}(M,L)\bigr),\\
\mathsf{pull}:&
\operatorname{ProfMap}
 \bigl(R,\operatorname{Hom}_{B}(M,L)\bigr)
\longrightarrow
\operatorname{ProfMap}
 \bigl(R,\operatorname{Cone}_{W}(M,F)\bigr).
\end{aligned}
$$

Here

$$
\operatorname{Cone}_{W}(M,F)
:=
\operatorname{ProfImply}_{\mathrm{cov}}
 \bigl(\operatorname{Hom}_{B}(M-,F-),W\bigr).
$$

The operation `push` eliminates a supplied cone through the universal
comparison and obtains its mediating map into $L$. The operation `pull`
introduces a cone by composing a map into $L$ with the universal cone. Their
cuts reduce in both directions:

$$
\begin{aligned}
\mathsf{pull}(\mathsf{push}(r))&\rightsquigarrow r,\\
\mathsf{push}(\mathsf{pull}(s))&\rightsquigarrow s.
\end{aligned}
$$

<!-- evidence:PROF-COMPARISON-BETA-ETA -->

> **Formal status — checked.** Evidence
> `PROF-COMPARISON-BETA-ETA`. The weighted operations
> `weighted_limit_cov_push` and `weighted_limit_cov_pull` are typed
> specializations of the generic `prof_comparison_push` and
> `prof_comparison_pull` owners. The beta/eta rules belong to the generic
> comparison, so no new cancellation rule is attached to each kind of limit.

The role of $R$ is easy to underestimate. Taking a single element would test
only one cone. Allowing an arbitrary incoming profunctor map says that the
universal operation is stable under families, endpoint action, and the next
categorical layer retained by the fixed-endpoint profunctor category. This is
the functorial type-theoretic replacement for an unstructured bijection of
sets of cones.

## 16.6 Conical Limits As The Terminal-Weight Specialization

Set $J'=\mathbf 1$ and take the terminal weight

$$
\mathbf 1_{J}:\mathbf 1\rightsquigarrow J.
$$

Its only fibre is the terminal category. In the usual semantic
interpretation,

$$
\begin{aligned}
\operatorname{Cone}_{\mathbf 1_J}(b,F;*)
&\simeq
[J,\mathsf{Cat}]
 \bigl(\mathbf 1,\operatorname{Hom}_{B}(b,F-)\bigr)\\
&\simeq
\operatorname{Cone}(b,F).
\end{aligned}
$$

A functor $\ell:\mathbf 1\to B$ selects a vertex. The weighted
representation becomes the familiar conical universal property

$$
\operatorname{Cone}(b,F)
\simeq
\operatorname{Hom}_{B}(b,\ell).
$$

Products, terminal objects, pullbacks, and equalizers arise by choosing their
usual indexing categories $J$. The weighted formulation does not require a
new universal-property mechanism for each of them.

At the active-interface level, the substitution is exact:

$$
\operatorname{IsWeightedLimit}
 \bigl(F,\operatorname{TerminalProf}(\mathbf 1,J),\ell\bigr)
$$

is a well-formed instance of `IsWeightedLimit_cov_comp`. This variance fact
is permanent regression evidence. What is not checked is the semantic
identification of the opaque profunctor implication with the displayed
functor category of ordinary cones.

<!-- evidence:WEIGHTED-LIMIT-SPECIALIZATIONS -->

> **Formal status — formal consequence.** Evidence
> `WEIGHTED-LIMIT-SPECIALIZATIONS`. `Terminal_prof`,
> `IsWeightedLimit_cov_comp`, and the focused classifier diagnostics
> establish the terminal-weight instance and its preservation corollary.
> Calling its fibres the usual cone categories is mathematical development
> contingent on the end semantics described below.

## 16.7 Right Kan Extensions As Conjoint-Weighted Limits

Let

$$
K:J\longrightarrow J'
$$

and retain the diagram $F:J\to B$. The conjoint of $K$ is the profunctor

$$
K^{\ast}:J'\rightsquigarrow J,
\qquad
K^{\ast}(j',j)
=\operatorname{Hom}_{J'}(j',Kj).
$$

It has exactly the variance of a limit weight. Define a selected right
Kan-extension comparison along $K$ to be the weighted-limit comparison

$$
\operatorname{IsWeightedLimit}
 \bigl(F,K^{\ast},\operatorname{Ran}_{K}F\bigr).
$$

When the residual has its expected end semantics, the fibrewise formula is

$$
\operatorname{Hom}_{B}
 \bigl(b,(\operatorname{Ran}_{K}F)(j')\bigr)
\simeq
\operatorname{Nat}
\left(
  \operatorname{Hom}_{J'}(j',K-),
  \operatorname{Hom}_{B}(b,F-)
\right).
$$

This is the standard pointwise right Kan-extension formula. It says that
maps into the value at $j'$ are cones whose shape is the representable
weight out of $j'$.

The use of a conjoint is not a mnemonic guess. `Conjoint_prof K` has type
$J'\rightsquigarrow J$, so the expression

$$
\operatorname{IsWeightedLimit}
 \bigl(F,\operatorname{Conjoint}(K),R\bigr)
$$

is a well-formed active classifier for every $R:J'\to B$. The focused
variance audit checks precisely this substitution.

The following two claims must nevertheless remain separate:

1. **Interface specialization:** conjoint weight yields an instance of the
   selected weighted comparison. This is a formal consequence of the active
   types.
2. **Semantic identification:** that instance agrees with the ordinary
   natural-transformation or end definition of pointwise right Kan extension.
   This requires a semantic end owner and coherence for the relevant
   Cat-valued transformation category.

<!-- evidence:WEIGHTED-END-KAN-SEMANTICS -->

> **Formal status — mathematical development.** Evidence
> `WEIGHTED-END-KAN-SEMANTICS`. The standard conical and pointwise
> Kan-extension formulas are mathematically part of the weighted theory.
> `Prof_imply_cov` currently packages their computational residual but does
> not unfold to a general end.

## 16.8 Adjunction Mates Transport Representables

Let

$$
S:A\longrightarrow B,
\qquad
R:B\longrightarrow A,
\qquad
S\dashv R.
$$

For arbitrary shaped functors $M:I\to A$ and $D:J\to B$, the adjunction
supplies the representable comparison

$$
\operatorname{Hom}_{B}(SM,D)
\simeq
\operatorname{Hom}_{A}(M,RD).
$$

It is natural in both endpoints and therefore lives as a
`ProfComparison`, not merely as a family of unrelated pointwise
equivalences. Passing this comparison through the fixed-weight implication
transports whole cone profunctors.

<!-- evidence:ADJ-HOM-PROF-COMPARISON -->

> **Formal status — checked.** Evidence
> `ADJ-HOM-PROF-COMPARISON`.
> `Adjunction_hom_prof_comparison_along` is the reindexed mate
> comparison. Its inverse directions and their cancellation are inherited
> from the generic profunctor-comparison calculus.

In classical category theory, a mate is often introduced by a formula using
the unit and counit. Computationally, the mate is better understood as a
change of representable coordinates. The triangle reductions of Chapter 12
are exactly the beta/eta laws ensuring that moving across the adjunction and
back removes the cut.

## 16.9 The Preservation Theorem

Assume that

$$
\ell:J'\longrightarrow B
$$

is supplied with a computational comparison certifying it as the
$W$-weighted limit of $D:J\to B$. We prove that

$$
R\ell:J'\longrightarrow A
$$

is the $W$-weighted limit of $RD:J\to A$.

Test the proposed representation at an arbitrary $M:I\to A$. There are three
comparisons:

$$
\begin{aligned}
\operatorname{Cone}_{W}(M,RD)
&\simeq
\operatorname{Cone}_{W}(SM,D)
&&\text{by the inverse mate under the residual},\\
&\simeq
\operatorname{Hom}_{B}(SM,\ell)
&&\text{by the supplied limit comparison},\\
&\simeq
\operatorname{Hom}_{A}(M,R\ell)
&&\text{by the mate at the candidate limit}.
\end{aligned}
$$

The middle comparison is the original representation reindexed along $S$.
The first and third are the same hom adjunction used in opposite directions
and at different diagrams. Composing them yields

$$
\operatorname{Cone}_{W}(RD)
\simeq
\operatorname{Hom}_{A}(-,R\ell-),
$$

which is the required weighted-limit comparison.

The implementation mirrors this proof without inserting a special rewrite
that says “right adjoints preserve limits.” Its three factors are:

1. `right_adjoint_weighted_limit_comp_step1`, the inverse mate mapped
   through the fixed-weight implication;
2. `right_adjoint_weighted_limit_comp_step2`, the supplied comparison
   reindexed along the left adjoint;
3. `right_adjoint_weighted_limit_comp_step3`, the mate at $\ell$.

`right_adjoint_preserves_weighted_limit_cov_comp` composes these
certificates. Since the result is again a `ProfComparison`, all universal
push/pull beta and eta behavior survives.

<!-- evidence:WEIGHTED-LIMIT-PRESERVATION -->

> **Theorem 16.1 — Right adjoints preserve selected weighted limits.**
> Given a computational $W$-weighted-limit comparison for $D$ and an
> adjunction $S\dashv R$, the active construction returns a computational
> $W$-weighted-limit comparison for $RD$ represented by $R\ell$.
>
> **Formal status — checked.** Evidence
> `WEIGHTED-LIMIT-PRESERVATION`. The theorem is conditional on a supplied
> comparison. It neither asserts that every weighted limit exists nor that a
> right adjoint creates one.

This proof is the promised continuation of cut elimination. The first mate
changes coordinates, the given universal comparison eliminates the central
cone cut, and the final mate changes coordinates back. Associativity is
controlled by composition of comparison certificates; it is not delegated to
a global reassociation rule.

## 16.10 Ordinary-Limit And Kan-Extension Corollaries

The theorem is uniform in $W$, so the two audited specializations immediately
give interface-level corollaries.

For the terminal weight:

> If $\ell$ carries the selected conical-limit comparison for $D$, then
> $R\ell$ carries the corresponding comparison for $RD$.

For the conjoint of $K:J\to J'$:

> If $\operatorname{Ran}_{K}D$ carries the selected right-Kan comparison,
> then $R\operatorname{Ran}_{K}D$ carries the corresponding comparison for
> $\operatorname{Ran}_{K}(RD)$.

These are not new preservation algorithms. They are the same
`right_adjoint_preserves_weighted_limit_cov_comp` term with
$W=\operatorname{TerminalProf}(\mathbf 1,J)$ or
$W=\operatorname{Conjoint}(K)$. The formal consequence is therefore stronger
than a slogan and weaker than the unimplemented semantic end theorem: the
classifier, transported comparison, and beta/eta interface are active; the
identification with every conventional presentation of limits or Kan
extensions is not.

## 16.11 Ends, Coends, And Dependent Universal Constructions

A semantic completion of this chapter would construct the residual by an end,
for example

$$
\operatorname{Cone}_{W}(b,F;j')
\simeq
\int_{j:J}
\left[
  W(j',j),
  \operatorname{Hom}_{B}(b,Fj)
\right],
$$

and tensor by a coend

$$
(P\otimes_B Q)(a,x)
\simeq
\int^{b:B}P(a,b)\times Q(b,x).
$$

Such constructions must provide more than object formulas. They need
introduction and elimination principles, action on base arrows and transfors,
beta/eta or comparison laws, associativity and unit coherence, and a
validation route through the shaped co-Yoneda theorem. Until those owners
exist, the formulas are semantic specifications for the opaque interfaces.

Dependent category theory asks for a further chain. For a base functor
$f:X\to Y$, one expects suitable change-of-base functors and adjunctions

$$
\Sigma_f\dashv f^{*}\dashv\Pi_f,
$$

with Beck--Chevalley and higher naturality conditions. The current Sigma and
Pi categories of directed families are important footholds, but no general
dependent adjunction package connects them to arbitrary base change. A
pointwise object formula would be insufficient: the construction must retain
base-arrow action, off-diagonal transfor action, and iteration into the next
hom.

<!-- evidence:DEPENDENT-ADJUNCTIONS -->

> **Formal status — research boundary.** Evidence
> `DEPENDENT-ADJUNCTIONS`. General end/coend owners, pointwise Kan
> packages, and the dependent adjunction chain remain separate formal
> projects. The active weighted comparison is the design constraint those
> projects should refine, not a claim that they are already present.

Chapter 17 now applies the safest of all extensions: opposite duality. It
turns the checked limit theorem into a colimit theorem, after which the join
shows how terminal-weight cross-arrow data can itself be internalized as a
directed categorical shape.
