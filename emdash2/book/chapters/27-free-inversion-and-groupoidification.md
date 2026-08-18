<a id="chapter-27"></a>

# 27. Free Inversion And Groupoidification

The Circle calculation explains what happens to one directed endomorphism
after inverse motion is admitted. A universal construction must say more. It
must characterize maps from the realized object into every groupoidal target,
and it must retain the higher action that makes those maps coherent.

For a category $C$, write $\mathsf{Groupoidify}(C)$ for its selected free
groupoidal realization and

$$
\eta_C:C\longrightarrow
  \operatorname{Path}(\mathsf{Groupoidify}(C))
$$

for the whole unit. A path-valued functor $F:C\to\operatorname{Path}(G)$
extends across the unit to a map from $\mathsf{Groupoidify}(C)$ to $G$.
Restriction and extension are inverse as whole functors on the mapping
categories:

$$
\operatorname{Hom}_{\mathsf{Grpd}}
  (\mathsf{Groupoidify}(C),G)
\;\simeq\;
\operatorname{Functor}(C,\operatorname{Path}(G)).
$$

The recursor computes on represented objects and at the canonical dependent
observation of a represented arrow. The unit also retains its explicit
compositor and one next action. Thus the construction does not first forget
$C$ to an object set or an unstructured graph.

<!-- evidence:GENERIC-GROUPOIDIFICATION-MAPPING -->

> **Formal status — checked.** Evidence
> `GENERIC-GROUPOIDIFICATION-MAPPING`. The displayed equivalence is the active
> fixed-forward whole mapping boundary for arbitrary $C$ and groupoidal $G$.
> Source functoriality, a whole `Groupoidify_func`, and the packaged adjunction
> with `Path_cat_func` remain deferred.

<a id="chapter-27-tests"></a>

## 27.1 Two Tests Before The General Construction

The general theorem is easier to understand after two finite shapes. For the
walking endomorphism, restriction along the comparison with the Circle is an
equivalence between Circle maps and path-valued WalkingEnd representations.
The inverse reads the image of the base and generator and uses Circle
recursion. This strengthens the power calculation of Chapter 26 into a whole
universal mapping statement.

The walking arrow tests a feature hidden by one-object examples: its source
and target differ. Its groupoidal realization is the interval with two points
and one path. The interval eliminator computes at both endpoints and at its
dependent generating segment; its whole mapping property classifies exactly
one directed arrow in a groupoidal target.

Specializing generic groupoidification to the WalkingArrow gives maps in both
directions between $\mathsf{Groupoidify}(\mathsf{WalkingArrow})$ and the
interval. The generic and interval beta/eta laws prove both cancellation
paths. The result is an equivalence, not a definitional identification of the
two HIT presentations.

The completed chapter will use these examples to distinguish three adjoint-
shaped ideas. The core of a category retains arrows already invertible.
Truncation lowers the homotopy level of groupoidal data. Groupoidification
freely realizes directed arrows as paths. Conflating them reverses a universal
property before any calculation begins.

> **Formal status — mathematical development.** The theorem statements and
> formal boundaries are fixed and checked. The complete reader-facing proof
> architecture, comparison table, and restriction/extension diagram remain
> part of this chapter's active prose tranche.
