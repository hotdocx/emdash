EMAIL10

You are right: there are two “reflexivity” layers, and they must be kept separate.

Here is the clarified version I would use.

```text
Let Z be a category.  For each object x : Z, define the outgoing-arrow
category

    Out_x = Σ (y : Z), Hom_Z(x,y).

Its distinguished object is

    ι_x = (x,id_x) : Out_x.

This is the analogue of refl in fixed-source path induction.  For every
outgoing arrow p : x -> y, there is a canonical arrow in Out_x

    ρ^x_p : ι_x -> (y,p).

Thus, for a motive E : Out_x -> Cat and initial datum u : E(ι_x), fixed-source
directed induction gives a section

    Ind_x(E,u) : Π q : Out_x, E(q)

with component

    Ind_x(E,u)(q) = E(ρ^x_q)(u).
```

Now the second layer:

```text
The new phenomenon appears when x itself is allowed to vary.  Let r : x -> y be
a base arrow in Z.  This is not the same as the inner reflexive object ι_x.
It is an outer change-of-source arrow.

Precomposition gives

    Out(r) : Out_y -> Out_x
    Out(r)(z,q : y -> z) = (z,q ∘ r).

So a motive E : Out_x -> Cat is transported to

    r_*E = E ∘ Out(r) : Out_y -> Cat.

The initial datum u : E(ι_x) is transported to a datum at the reflexive
outgoing arrow of y by the canonical arrow ρ^x_r : ι_x -> (y,r):

    r_*u = E(ρ^x_r)(u)
         : E(y,r)
         = (r_*E)(ι_y).
```

The comparison between sections is then:

```text
There are two ways to obtain a section of r_*E over Out_y.

First transport the already-constructed section:

    r_*(Ind_x(E,u)).

At (z,q : y -> z), this is

    Ind_x(E,u)(Out(r)(z,q))
    = E(ρ^x_{q∘r})(u).

Second transport the motive and initial datum first, then apply induction at y:

    Ind_y(r_*E, r_*u).

At (z,q : y -> z), this is

    (r_*E)(ρ^y_q)(r_*u)
    = E(Out(r)(ρ^y_q))(E(ρ^x_r)(u)).
```

The coherence equation behind the comparison is:

```text
Out(r)(ρ^y_q) ; ρ^x_r = ρ^x_{q∘r}.
```

So the two section components have the same intended meaning, but when this is internalized as a theorem varying in `x`, the comparison is not just the fixed-source beta rule. It is a directed naturality/coherence comparison between “transport the induced section” and “induce after transporting motive and initial data.”

That is the laxity layer. It concerns the outer source-change arrow `r : x -> y`, not the inner reflexive outgoing object `ι_x = (x,id_x)`.





-----



Yes. I would lead with the familiar J/path-induction shape, then say: in the directed categorical analogue, fixed-
  source induction is easy to state, but internalizing the source object x forces a variance/transport comparison
  that is invisible in ordinary identity-type path induction.

  I would avoid the strong phrase “not discovered before.” Safer and more defensible for algtop-l:

  > This exposes a laxity phenomenon that, as far as I know, is not usually isolated in the ordinary identity-type
  > presentation of path induction.

  Draft:

  I would like to announce a new v3.2 draft of emdash, a Lambdapi
  formalization aimed at functorial programming with higher categories.

  The motivating example is the familiar shape of path induction in dependent
  type theory.  Given a type A, a point x : A, a motive over paths out of x,

      E : Π (y : A), (x = y) -> Type,

  and a term

      u : E x refl,

  path induction constructs

      Π (y : A) (p : x = y), E y p.

  The v3.2 development studies the directed/categorical analogue.  For a
  category Z and an object x : Z, replace paths out of x by the outgoing-arrow
  category

      Out_Z(x) = Σ (y : Z), Hom_Z(x,y).

  The reflexive outgoing arrow is (x,id_x), and every outgoing arrow
  p : x -> y determines a canonical arrow

      ρ_{x,y,p} : (x,id_x) -> (y,p)

  inside Out_Z(x).  Thus, for a motive

      E : Out_Z(x) -> Cat

  and u : E(x,id_x), one obtains a section

      q ↦ E(ρ_q)(u).

  This is the fixed-source version of categorical path induction.

  The new point appears when one fully internalizes the source object x.  The
  assignment x ↦ Out_Z(x) is contravariant: an arrow p : x -> y induces

      Out_Z(y) -> Out_Z(x),
      (z,q : y -> z) ↦ (z,q ∘ p).

  Consequently, motives and sections must be transported along this
  precomposition functor.  In an ordinary identity-type presentation, transport
  at refl hides much of this structure.  In the directed setting, however, a
  displayed functor need not preserve such transported data strictly.  One is
  led naturally to a comparison cell

      χ^{F}_{p,u} :
        D[p](F[x](u)) -> F[y](E[p](u)),

  which is a laxity datum for directed family transport.

  In emdash v3.2 this comparison is not postulated as an external naturality
  square.  It is extracted computationally from an internal displayed hom-action.
  In strict/cartesian cases, such as representable precomposition, the comparison
  cell collapses to an identity, and the induced transitivity computation
  normalizes to ordinary categorical composition:

      q after p.

  This suggests that directed path induction has a genuinely categorical
  laxness layer which is not usually visible in the standard identity-type
  formulation of path induction.  I would be very interested to hear whether
  this phenomenon has an established name or prior formulation in categorical
  logic, HoTT, or higher category theory.

  The draft paper and Lambdapi files are in the emdash repository:
  [link]

  Best,
  [name]

  I would keep the novelty claim as “not usually visible” plus an invitation for references. That is stronger than
  “just implementation detail” but avoids overclaiming priority.



-----



• You are right: there are two “reflexivity” layers, and they must be kept separate.

      Out_x = Σ (y : Z), Hom_Z(x,y).

  Thus, for a motive E : Out_x -> Cat and initial datum u : E(ι_x), fixed-source
  directed induction gives a section

      Ind_x(E,u) : Π q : Out_x, E(q)

  with component

      Ind_x(E,u)(q) = E(ρ^x_q)(u).

  Now the second layer:

  The new phenomenon appears when x itself is allowed to vary.  Let r : x -> y be
  a base arrow in Z.  This is not the same as the inner reflexive object ι_x.
  It is an outer change-of-source arrow.

  Precomposition gives

      Out(r) : Out_y -> Out_x
      Out(r)(z,q : y -> z) = (z,q ∘ r).

  So a motive E : Out_x -> Cat is transported to

      r_*E = E ∘ Out(r) : Out_y -> Cat.

  The initial datum u : E(ι_x) is transported to a datum at the reflexive
  outgoing arrow of y by the canonical arrow ρ^x_r : ι_x -> (y,r):

      r_*u = E(ρ^x_r)(u)
           : E(y,r)
           = (r_*E)(ι_y).

  The comparison between sections is then:

  There are two ways to obtain a section of r_*E over Out_y.

  First transport the already-constructed section:

      r_*(Ind_x(E,u)).

  At (z,q : y -> z), this is

      Ind_x(E,u)(Out(r)(z,q))
      = E(ρ^x_{q∘r})(u).

  Second transport the motive and initial datum first, then apply induction at y:

      Ind_y(r_*E, r_*u).

  At (z,q : y -> z), this is

      (r_*E)(ρ^y_q)(r_*u)
      = E(Out(r)(ρ^y_q))(E(ρ^x_r)(u)).

  The coherence equation behind the comparison is:

  Out(r)(ρ^y_q) ; ρ^x_r = ρ^x_{q∘r}.

  So the two section components have the same intended meaning, but when this is internalized as a theorem varying in
  x, the comparison is not just the fixed-source beta rule. It is a directed naturality/coherence comparison between
  “transport the induced section” and “induce after transporting motive and initial data.”

  That is the laxity layer. It concerns the outer source-change arrow r : x -> y, not the inner reflexive outgoing
  object ι_x = (x,id_x).



-----




Yes. The missing piece is: laxity is not the statement that the two object-level formulas are morally the same. It
  is the extra structure needed to make the family of fixed-source eliminators assemble over the outer source
  variable.

  A clearer consolidated version:

  For fixed x : Z, define

      Out_x = Σ (y : Z), Hom_Z(x,y)
      ι_x   = (x,id_x).

  For a motive E : Out_x -> Cat, fixed-source directed induction is a functor

      I_x(E) : E(ι_x) -> Π (a : Out_x), E(a)

  with

      I_x(E)(u)(a) = E(ρ^x_a)(u),

  S_r(E) : S_x(E) -> S_y(r_*E)
  S_r(E)(u) = E(ρ^x_r)(u)


  S_x(E)  -- I_x(E) -->  T_x(E)
    |                    |
    | S_r(E)             | T_r(E)
    v                    v
  S_y(r_*E) -- I_y(r_*E) --> T_y(r_*E).


  versus

  I_y(r_*E)(S_r(E)(u)).

    = I_x(E)(u)(z,q ∘ r)
    = E(ρ^x_{q∘r})(u)

  and

  I_y(r_*E)(S_r(E)(u))(z,q)
    = (r_*E)(ρ^y_q)(E(ρ^x_r)(u))
    = E(Out(r)(ρ^y_q))(E(ρ^x_r)(u)).

  The intended equality is controlled by the canonical rho-composition law:

  Out(r)(ρ^y_q) ; ρ^x_r = ρ^x_{q∘r}.

  So objectwise, the comparison says:

  E(ρ^x_{q∘r})(u)
    ≈
  E(Out(r)(ρ^y_q))(E(ρ^x_r)(u)).

  The laxity layer is the internal categorical version of this comparison:

  χ^I_{r,E,u} :
    T_r(E)(I_x(E)(u))
      -> I_y(r_*E)(S_r(E)(u))

  as an arrow in the section category

  Π (b : Out_y), (r_*E)(b).

  In ordinary dependent type theory, the analogous source variation is usually hidden because identity/path induction
  is organized around refl, and the computation rule is stated at refl. Here there are two layers: the inner
  reflexive outgoing object ι_x, and the outer directed source-change arrow r : x -> y. Once the outer arrow is
  internalized, the theorem must transport motives, initial data, and sections coherently. That coherence is not
  merely the fixed-source beta rule; it is the comparison cell above.



----


