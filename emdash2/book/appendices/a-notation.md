<a id="appendix-notation"></a>

# Appendix A. Notation

The book follows
`reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`.
This appendix records the compact notation used in the mathematical line of
the book. It is a reading guide, not a proposal to make every glyph parser
syntax.

| Book notation | Reading | Current implementation witness |
| --- | --- | --- |
| `a ->^C b` | an arrow of `C` from `a` to `b` | `Hom C a b` |
| `F : A ⊢ B` | a functor from `A` to `B` | `Functor A B` |
| `E : K ⊢ Cat` | a Cat-valued directed family | `Catd K` |
| `E[f]` | functorial action of a family on a base arrow | `catd_transport_func` |
| `H_x` | the based hom-category `Hom_W(*,x)` | `Hom_cat WalkingEnd_cat walking_base x` |
| `W`, `*`, `ell` | WalkingEnd, its base, and its directed generator | `WalkingEnd_cat`, `walking_base`, `walking_loop` |
| `Code` | the Nat-valued directed family over `W` | `walking_Code_catd` |
| `encode_x(p)` | apply `Code[p]` to zero | `walking_encode` |
| `ell^n` or `power(n)` | the `n`th generator-prefix power | `walking_power` |
| `decode_x(c)` | the object action of the contextual decoder | `walking_directed_decode_funcd` |
| `nu_p` | the directed normalization cell `p -> decode_x(encode_x(p))` | `walking_directed_normalization_cell` |
| `simeq` | an explicitly stated equivalence interface | in Theorem 8.1, `walking_hom_nat_type_equiv` |
| `F[f]` | functor action on an arrow | `fapp1_fapp0` and its iterable `fapp1_func` owner |
| `u_*(g)` | postcomposition by `u`, namely `u o g` | `hom_postcomp_fapp0` |
| `u^*(h)` | precomposition by `u`, namely `h o u` | `hom_precomp_along_fapp0` |
| `eta[f]` | off-diagonal action of a transfor on `f:x->y` | `tapp1_fapp0` |
| `chi^Phi_(p,u)` | displayed transport-comparison component | `fdapp1_int_cell` |
| `P:A rightsquigarrow B` | a Cat-valued profunctor on `A^op times B` | `Prof A B` |
| `U_A` | the unit hom profunctor | `Unit_prof A` |
| `P tensor_B Q` | selected fixed-middle profunctor tensor | `Prof_tensor P Q` |

Composition is written in diagrammatic reading order as `g o f`: first
`f`, then `g`. For the concrete model `BNat`, this agrees with the
implemented convention `g o f = g + f`, where Nat addition recurses in its
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

`Path(A)` denotes the equality-path category on a carrier `A`. It
must not be confused with a directed hom-category. In particular, the objects
of `H_x` are arrows of `W`, whereas arrows of `H_x` are directed
2-cells between those arrows.

> **Formal status — mathematical development.** No notation in this appendix
> is automatically implemented parser syntax.
