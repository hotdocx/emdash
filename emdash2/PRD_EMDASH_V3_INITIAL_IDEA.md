Our project is `emdash` , whose goal is to write a Lambdapi specification for a programming language (and proof assistant) for ω-categories...  @README.md

In fact, now that we have made substantial progress in @emdash2.lp then we are now in the third iteration of the goal: `emdash` version 3, to be written into the file @emdash3.lp

---

Now we will take the lessons, insights learned from emdash2.lp and start over cleanly into emdash3.lp

Approximately:
- first of all, we should actually learn from Homotopy Type Theory (hott) firstly:
  + hott starts with dependent type theory and introduces the equality `=` which lands in all types `Type`/`TYPE` instead of propositions ( `Prop` ); with an induction principle which essentially says that `Hom` is a unit profunctor and can be contracted, so there is e.g. an equivalence betweek functors F : (hom(x,—) ⊗ A) → B and functors G : A → B which provides an "induction" reverse-operation to the operation of evaluating `F` at `refl_x` / `1_x` (reflexitivity/identity at x)
  + then hott tries to characterize:
    * what is the equality `=` in a Sigma Σ type: it is. a base equality between the first components together with a equality between the LHS second component transported bt the base equality and the RHS second component: (a1, b1) =_(Πx:A.B[x]) (a2, b2) ≔ (p: a1 =_A a2, p_!(b1) =_B[a2] b2 )
    * what is the equality `=` in a Pi Π type: it is an homotopy: f =_(Πx:A.B[x]) g ≔ Πx:A. (f x =_B[x] g x)
    * what is the equality `=` in the universe: this is the univalence axiom
    * what is the equality `=` in a pushout type: this becomes synthetic homotopy theory

Approximately:
So I am thinking, as a starter these architecture modifications from emdash2.lp for the new emdash3.lp
- I believe we already have  Σ (alias Σ_cat ) type, this is `Total_cat` I believe
- we keep `Functor_catd` as this allows us to iterate; then we need also a new operation `Catd_catd E : Catd` for any `E: Catd Z` so that we can iterate similarly as for `Functor_catd`
- we would need to have a dedicated Π (alias Π_cat )type i.e. Π E : Cat for E : Catd Z, and then `Functord_cat` will be an alias/defined via `Π` and `Functor_catd` i.e.  `Functord_cat FF GG` is `Π (Functor_catd FF GG)`
- we would need `hom_` / `hom_int` to be unified from the start as fully internal, and restore the uniformity/symmetry of e pre-applications of external/parameter functor on both covariant and contravariant variable, i.e. `Hom(G ~ , F —)` ... this is necessary if we want later things to be simplified and easily internal  (e.g. we could get away with `fapp1_int_transf` via a use of `comp_cat_fapp0` to avoid the asymetry/non-uniformity, but in other places it might become difficult (impossible?) e.g. in  `tdapp1_func_funcd`?) ... (still it is an open question whether we truly need both pre-applied functors as parameters of `hom` (e.g. is  using Op/duality operations (e.g. to get `hom_con` etc) (seem) enough? ))
- we would need `homd_` / `homd_int` / `homd_curry` to be unified from the start as fully internal, and simplied in curried / iterated form (rather than via the "total/sigma" (`*_base` technique), which is still being used even for the `homd_curry` (in disguise) ) ... and I think our new `Catd_catd` could make an alternative direct-iterated formulation of `homd_curry` easier/clearer 
- then we can characterize arrows `→` in Σ type (which we already have somewhat, specially in the Groth case), and  characterize arrows `→` in Π type which is a todo I believe, and  characterize arrows `→` in universe (`Cat_cat`) which we have already have (directed-) univalence definitionaly, ... (then we can defer interactions between `→` and `=` and meaning/definition of equivalence/isomorphism and definition of "(non-directed-)univalent category" and what it means (non-directed univalence Voevodsky-style) when the category is the universe `Cat_cat`... ) ... then later we can defer higher inductive types (categories) / pushouts (e.g. "join" of categories) (and characterization of `→` ?) for later...

---

... all these are very approximate, the goal for now is to do a brief brainstorming and clarify/spell-out the goal cleanly...

---

Think hard and do a careful review and analysis; and find a design, architecture, and implementation to solve this task...