<a id="appendix-notation"></a>

# Appendix A. Notation

The book follows
`reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`.
This appendix records the compact notation used in the mathematical line of
the book. It is a reading guide, not a proposal to make every glyph parser
syntax.

| Book notation | Reading | Current implementation witness |
| --- | --- | --- |
| $a\to_C b$ | an arrow of $C$ from $a$ to $b$ | `Hom C a b` |
| $F:A\vdash B$ | a functor from $A$ to $B$ | `Functor A B` |
| $E:K\vdash\mathsf{Cat}$ | a Cat-valued directed family | `Catd K` |
| $E[f]$ | functorial action of a family on a base arrow | `catd_transport_func` |
| $H_x$ | the based hom-category $\operatorname{Hom}_W(*,x)$ | `Hom_cat WalkingEnd_cat walking_base x` |
| $W$, $*$, $\ell$ | WalkingEnd, its base, and its directed generator | `WalkingEnd_cat`, `walking_base`, `walking_loop` |
| $\mathsf{Code}$ | the Nat-valued directed family over $W$ | `walking_Code_catd` |
| $\mathsf{encode}_x(p)$ | apply $\mathsf{Code}[p]$ to zero | `walking_encode` |
| $\ell^n$ or $\mathsf{power}(n)$ | the $n$th generator-prefix power | `walking_power` |
| $\mathsf{decode}_x(c)$ | the object action of the contextual decoder | `walking_directed_decode_funcd` |
| $\nu_p$ | the directed normalization cell $p\to\mathsf{decode}_x(\mathsf{encode}_x(p))$ | `walking_directed_normalization_cell` |
| $\simeq$ | an explicitly stated equivalence interface | in Theorem 8.1, `walking_hom_nat_type_equiv` |
| $F[f]$ | functor action on an arrow | `fapp1_fapp0` and its iterable `fapp1_func` owner |
| $u_*(g)$ | postcomposition by $u$, namely $u\circ g$ | `hom_postcomp_fapp0` |
| $u^*(h)$ | precomposition by $u$, namely $h\circ u$ | `hom_precomp_along_fapp0` |
| $\eta[f]$ | off-diagonal action of a transfor on $f:x\to y$ | `tapp1_fapp0` |
| $\chi^\Phi_{(p,u)}$ | displayed transport-comparison component | `fdapp1_int_cell` |
| $P:A\rightsquigarrow B$ | a Cat-valued profunctor on $A^{\mathrm{op}}\times B$ | `Prof A B` |
| $U_A$ | the unit hom profunctor | `Unit_prof A` |
| $P\otimes_B Q$ | selected fixed-middle profunctor tensor | `Prof_tensor P Q` |
| $F\dashv G$ | adjunction data with selected triangle cuts | `Adjunction F G` |
| $\operatorname{Cone}_W(F)$ | the weighted-cone profunctor | `WeightedCone_prof F W` |
| $\operatorname{IsWeightedLimit}(F,W,L)$ | a chosen representation of weighted cones | `IsWeightedLimit_cov_comp F W L` |
| $\operatorname{Cocone}_W(F)$ | the opposite-dual weighted-cocone profunctor | `WeightedCocone_prof F W` |
| $A\star B$ | directed join with left-to-right cross arrows | `Join_cat A B` |

The bounded executable text bridge uses four intrinsic categorical lambda
modes:

```text
λ^f  x : A. ...
λ^n  k : K. ...
λ^fd a : E. ...
λ^nd k : K. ...
```

The superscript belongs to the lambda: it specifies ordinary functorial,
natural/indexed, displayed-functorial, or displayed-natural variation. The
classifier annotation after the variable may be omitted when an expected
classifier supplies it bidirectionally, but the binder mode itself is not
inferred from that annotation. Thus the book's mathematical telescope
declaration $k:^{n}K$ corresponds to binding with `λ^n k : K. ...`; the two
notations have the same mode reading without being character-for-character
surface syntax. Ordinary object binding in the outer logical framework uses
its ordinary dependent lambda rather than a categorical `^o` mode.

Composition is written in diagrammatic reading order as $g\circ f$: first
$f$, then $g$. For the concrete model $\mathsf{BNat}$, this agrees with the
implemented convention $g\circ f=g+f$, where Nat addition recurses in its
left argument.

The two star actions are deliberately variance-separated. If $g:w\to x$ and
$u:x\to y$, then $u_*(g):w\to y$. If $u:x\to y$ and $h:y\to z$, then
$u^*(h):x\to z$. Thus the formula $f^*(g)=g\circ f$ names
**precomposition** and belongs to `hom_precomp_along_*`; it is not the
postcomposition owner with a typographic variation.

These formulas are categorical, not specifically functor-categorical. Their
general reading takes $w,x,y,z$ to be objects and the displayed arrows to be
arrows of an arbitrary ambient category $K$. The specialization
$K=\mathsf{Cat}$ makes those objects categories and those arrows functors;
that is the currently checked product/projection instance used in Chapter 9.

$\mathsf{Path}(A)$ denotes the equality-path category on a carrier $A$. It
must not be confused with a directed hom-category. In particular, the objects
of $H_x$ are arrows of $W$, whereas arrows of $H_x$ are directed
2-cells between those arrows.

> **Formal status — mathematical development with a checked executable
> subset.** The four categorical binder spellings, neutral application, and
> selected structural forms are implemented only for the reviewed profiles.
> The rest of the appendix remains mathematical notation, not an assertion
> that the complete book grammar is parsed.
