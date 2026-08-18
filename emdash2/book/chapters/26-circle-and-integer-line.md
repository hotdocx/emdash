<a id="chapter-26"></a>

# 26. The Circle And The Integer Line

The walking endomorphism of Chapter 8 has one directed generator, and its
based endomorphisms are counted by natural numbers. The Circle has one loop,
but the loop is an equality path. It can be traversed forward and backward.
The corresponding arithmetic is therefore not the free monoid of natural
powers but the integer line.

The Circle is presented by a point $\mathsf{base}$ and a loop
$\mathsf{loop}:\mathsf{base}=\mathsf{base}$. Its dependent eliminator
computes at the point and, at the canonical dependent observer, on the loop.
The distinction between dependent and ordinary path action is important:

$$
\operatorname{apd}(\mathsf{circle\_ind},\mathsf{loop})
  \;\equiv\; \ell
$$

at the selected dependent owner, whereas the corresponding ordinary
$\operatorname{ap}$ equation is retained as equality evidence. Computation
is strong enough to expose the higher constructor without turning every
propositional comparison into a rewrite.

The universal cover sends the base to the successor-localized Integer and the
loop to successor. Transport in this family is the encoder. Integer-indexed
positive and negative powers supply the decoder. Endpoint-dependent Circle
induction and Integer induction prove that the two constructions are inverse.

<!-- evidence:CIRCLE-LOOP-INTEGER -->

> **Formal status — checked.** Evidence `CIRCLE-LOOP-INTEGER`. The intrinsic
> based-loop carrier and the categorical based Hom carrier are each
> `TypeEquiv` to Integer. A whole equality-valued categorical equivalence is
> retained separately; neither category head is rewritten to the other.

<a id="chapter-26-route"></a>

## 26.1 From Successor To Monodromy

The proof will be developed from the arithmetic outward. The Integer carrier
is not introduced as a second signed syntax. It is the transparent facade of
the sequential telescope obtained by repeatedly applying successor to the
natural numbers. Successor and predecessor are inverse, and the inherited
set-targeted eliminator is precisely what the Circle decoder needs.

The next stage constructs the code family over the Circle. Univalence turns
the successor equivalence into a path in the universe; Circle recursion turns
that universe path into monodromy. Encoding transports zero around an
arbitrary based loop. Decoding builds the corresponding integer power of the
generating loop. The two round trips use different induction principles, and
their difference explains why the proof is computational rather than merely
an assertion that the fundamental group is familiar.

The final stage returns to families. A self-equivalence determines Circle
monodromy, and restriction to the directed walking endomorphism remembers
only its forward action. Mere connectedness is then proved without choosing
a global untruncated path, and the set truncation of the Circle is shown
contractible.

> **Formal status — mathematical development.** This source currently fixes
> the theorem-led route and exact computation boundary. The detailed
> encode/decode exposition, HoTT attribution map, and connectedness proof will
> be expanded before the chapter tranche closes.
