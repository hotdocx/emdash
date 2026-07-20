<a id="chapter-15"></a>

# 15. Structure Identity And Saturation

The structure identity principle asks when equality of carriers equipped with
compatible structure agrees with structured equivalence. Saturation asks how
to replace an unsaturated categorical presentation by one for which the
appropriate identity-to-equivalence map is an equivalence. These are related
questions, but neither is merely a restatement of the finite-height evidence
already used by WalkingEnd.

## 15.1 The structure-over-carrier schema

The intended argument begins with a carrier classifier, a family of
structures over it, and a notion of structure-preserving equivalence. The
identity principle then identifies paths of structured objects with those
equivalences under a univalence hypothesis. Existing evidence-property and
retract-truncation theorems are useful local ingredients; they are not the
generic theorem.

> **Formal status — mathematical development.** The missing infrastructure is
> a reusable structure-over-carrier signature with coherent transport and an
> equivalence classifier at the native categorical level.

## 15.2 Rezk completion by its universal property

A Rezk completion should be introduced as a universal map from a
precategory-like object into a saturated one. The Yoneda-image construction
and a higher-inductive saturation construction are two ways to realize that
property in the HoTT setting. The latter is especially relevant here because
its proof again uses encode-decode, but WalkingEnd itself is not a Rezk
completion.

> **Formal status — research boundary.** No general saturation object,
> fully-faithful-and-essentially-surjective universal map, or native Rezk
> universal property is implemented. A future benchmark must validate the
> mapping property and its higher naturality, not only construct an object
> carrier.
