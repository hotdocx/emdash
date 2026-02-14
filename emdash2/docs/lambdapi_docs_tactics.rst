Proof tactics
=============

The BNF grammar of tactics is in `lambdapi.bnf <https://raw.githubusercontent.com/Deducteam/lambdapi/master/doc/lambdapi.bnf>`__.

.. _admit:

``admit``
---------

Adds in the environment new symbols (axioms) proving the focused goal.

.. _apply:

``apply``
---------

``apply t`` refines the current goal with ``t _ … _``, i.e. ``t``
applied to a number of underscores, which depends on the goal and the
type of ``t``. For instance, if ``t`` is a term of type ``Π x₁:T₁, …,
Π xₙ:Tₙ,U`` and ``U`` matches the current goal, then it will generated
``n`` subgoals for ``T₁``, …,``Tₙ``.


.. _assume:

``assume``
----------

If the focused typing goal is of the form ``Π x₁ … xₙ,T``, then
``assume h₁ … hₙ`` replaces it by ``T`` with each ``xᵢ`` replaced by
``hᵢ``.

.. _fail:

``change``
----------

``change t`` replaces the current goal ``u`` by ``t``, if ``t ≡ u``.

``fail``
--------

Always fails. It is useful when developing a proof to stop at some
particular point.

.. _generalize:

``generalize``
--------------

If the focused goal is of the form ``x₁:A₁, …, xₙ:Aₙ, y₁:B₁, …, yₚ:Bₚ
⊢ ?₁ : U``, then ``generalize y₁`` transforms it into the new goal
``x₁:A₁, …, xₙ:Aₙ ⊢ ?₂ : Π y₁:B₁, …, Π yₚ:Bₚ, U``.

.. _have:

``have``
--------

``have x: t`` generates a new goal for ``t`` and then let the user prove
the focused typing goal assuming ``x: t``.

.. _induction:

``induction``
-------------

If the focused goal is of the form ``Π x:I …, …`` with ``I`` an
inductive type, then ``induction`` refines it by applying the
induction principle of ``I``.

.. _refine:

``refine``
----------

The tactic ``refine t`` tries to instantiate the focused goal by the
term ``t``. ``t`` can contain references to other goals by using
``?n`` where ``n`` is a goal name. ``t`` can contain underscores ``_``
or new metavariable names ``?n`` as well. The type-checking and
unification algorithms will then try to instantiate some of the
metavariables. The new metavariables that cannot be solved are added
as new goals.

.. _remove:

``remove``
----------

``remove h₁ … hₙ`` erases the hypotheses ``h₁ … hₙ`` from the context of the current goal.
The remaining hypotheses and the goal must not depend directly or indirectly on the erased hypotheses.
The order of removed hypotheses is not relevant.

.. _set:

``set``
-------

``set x ≔ t`` extends the current context with ``x ≔ t``.

.. _simplify:

``simplify``
------------

With no argument, ``simplify`` normalizes the focused goal with respect
to β-reduction and the user-defined rewriting rules.

``simplify rule off`` normalizes the focused goal with respect to
β-reduction only.

If ``f`` is a non-opaque symbol having a definition (introduced with
``≔``), then ``simplify f`` replaces in the focused goal every occurrence
of ``f`` by its definition.

If ``f`` is a symbol identifier having rewriting rules, then ``simplify
f`` applies these rules bottom-up on every occurrence of ``f`` in the
focused goal.

Remark: ``simplify`` fails if the goal cannot be simplified.

.. _solve:

``solve``
---------

Simplify unification goals as much as possible.

.. _why3:

``why3``
--------

The tactic ``why3`` calls a prover (using the why3 platform) to solve
the current goal. The user can specify the prover in two ways :

* globally by using the command ``prover`` described in :doc:`queries`

* locally by the tactic ``why3 "<prover_name>"`` if the user wants to change the
  prover inside an interactive mode.

If no prover name is given, then the globally set prover is used
(``Alt-Ergo`` by default).

A set of symbols should be defined in order to use the ``why3`` tactic.
The user should define those symbols using builtins as follows :

::

   builtin "T"   ≔ … // : U → TYPE
   builtin "P"   ≔ … // : Prop → TYPE
   builtin "bot" ≔ … // : Prop
   builtin "top" ≔ … // : Prop
   builtin "not" ≔ … // : Prop → Prop
   builtin "and" ≔ … // : Prop → Prop → Prop
   builtin "or"  ≔ … // : Prop → Prop → Prop
   builtin "imp" ≔ … // : Prop → Prop → Prop
   builtin "eqv" ≔ … // : Prop → Prop → Prop
   builtin "all" ≔ … // : Π x: U, (T x → Prop) → Prop
   builtin "ex"  ≔ … // : Π x: U, (T x → Prop) → Prop

**Important note:** you must run ``why3 config detect`` to make
Why3 know about the available provers.


---


Proof tactics on equality
=========================

The BNF grammar of tactics is in `lambdapi.bnf <https://raw.githubusercontent.com/Deducteam/lambdapi/master/doc/lambdapi.bnf>`__.

The tactics ``reflexivity``, ``symmetry`` and ``rewrite`` assume the
existence of terms with approriate types mapped to the builtins ``T``,
``P``, ``eq``, ``eqind`` and ``refl`` thanks to the following builtin
declarations:

::

   builtin "T"     ≔ … // : U → TYPE
   builtin "P"     ≔ … // : Prop → TYPE
   builtin "eq"    ≔ … // : Π [a], T a → T a → Prop
   builtin "refl"  ≔ … // : Π [a] (x:T a), P(x = x)
   builtin "eqind" ≔ … // : Π [a] x y, P(x = y) → Π p:T a → Prop, P(p y) → P(p x)

.. _reflexivity:

``reflexivity``
---------------

Solves a goal of the form ``Π x₁, …, Π xₙ, P (t = u)`` when ``t ≡ u``.

.. _rewrite:

``rewrite``
-----------

The ``rewrite`` tactic takes as argument a term ``t`` of type ``Π x₁ …
xₙ,P(l = r)`` prefixed by an optional ``left`` (to indicate that the
equation should be used from right to left) and an optional rewrite
pattern in square brackets prefixed by a dot, following the syntax and
semantics of SSReflect rewrite patterns:

::

   <rw_patt> ::=
     | <term>
     | "in" <term>
     | "in" <ident> "in" <term>
     | <ident> "in" <term>
     | <term> "in" <ident> "in" <term>
     | <term> "as" <ident> "in" <term>

See examples in `rewrite1.lp <https://github.com/Deducteam/lambdapi/blob/master/tests/OK/rewrite1.lp>`_
and `A Small Scale Reflection Extension for the Coq
system <http://hal.inria.fr/inria-00258384>`_, by Georges Gonthier,
Assia Mahboubi and Enrico Tassi, INRIA Research Report 6455, 2016,
section 8, p. 48, for more details.

In particular, if ``u`` is a subterm of the focused goal matching ``l``,
that is, of the form ``l`` with ``x₁`` replaced by ``u₁``, …, ``xₙ``
replaced by ``uₙ``, then the tactic ``rewrite t`` replaces in the
focused goal all occurrences of ``u`` by the term ``r`` with ``x₁``
replaced by ``u₁``, …, ``xₙ`` replaced by ``uₙ``.

.. _symmetry:

``symmetry``
------------

Replaces a goal of the form ``P (t = u)`` by the goal ``P (u = t)``.



---


Proof tactics example file rewrite1.lp
=========================



// Data type of booleans.

constant symbol B : TYPE;

constant symbol true  : B;
constant symbol false : B;

// Data type of natural numbers.

constant symbol N : TYPE;

constant symbol z : N;
constant symbol s : N → N;

// Addition on natural numbers.

symbol add : N → N → N;

rule add z      $x ↪ $x;
rule add (s $x) $y ↪ s (add $x $y);

// Multiplication on natural numbers.

symbol mul : N → N → N;

rule mul z      _  ↪ z;
rule mul (s $x) $y ↪ add $y (mul $x $y);

// Type of data type codes and their interpretation as types.

constant symbol U : TYPE;

injective symbol T : U → TYPE;

constant symbol bool : U;
constant symbol nat  : U;

rule T bool ↪ B;
rule T nat  ↪ N;

constant symbol pi : Π (a : U), (T a → U) → U;

rule T (pi $a $f) ↪ Π (x : T $a), T ($f x);

// Type of propositions and their interpretation as types.

constant symbol Prop : TYPE;

symbol P : Prop → TYPE;

constant symbol all : Π (a : U), (T a → Prop) → Prop;

rule P (all $a $f) ↪ Π (x : T $a), P ($f x);

// Induction principle on N.

symbol nat_ind : Π (p:N → Prop), P(p z) → (Π n, P(p n) → P(p (s n))) → Π n, P(p n);

rule nat_ind _  $u _  z      ↪ $u;
rule nat_ind $p $u $v (s $n) ↪ $v $n (nat_ind $p $u $v $n);

// Boolean equality on N.

symbol beq : N → N → B;

rule beq z      z      ↪ true;
rule beq (s $x) (s $y) ↪ beq $x $y;
rule beq z      (s _ ) ↪ false;
rule beq (s _ ) z      ↪ false;

// Leibniz equality.

constant symbol eq : Π a, T a → T a → Prop;

constant symbol refl : Π a x, P (eq a x x);

constant symbol eqind : Π a x y, P (eq a x y) → Π (p:T a → Prop), P (p y) → P (p x);
// FIXME Try to infer the type of p.

// Setting up builtins for rewrite.

builtin "P"     ≔ P;
builtin "T"     ≔ T;
builtin "eq"    ≔ eq;
builtin "eqind" ≔ eqind;
builtin "refl"  ≔ refl;

// Symmetry of the equality (first option, rewrite).
opaque symbol eq_sym : Π a x y, P (eq a x y) → P (eq a y x)
≔ begin
  assume a x y h;
  rewrite h;
  refine refl a y
end;

// Symmetry of the equality (second option, by hand).
opaque symbol eq_sym_other_1 : Π a x y, P (eq a x y) → P (eq a y x)
≔ begin
  assume a x y h;
  refine eqind a x y h (λ z, eq a y z) (refl a y)
end;

// Symmetry of the equality (third option, by hand with a wildcard).
opaque symbol eq_sym_other_2 : Π a x y, P (eq a x y) → P (eq a y x)
≔ begin
  assume a x y h;
  refine eqind a x y h (λ z, eq a y z) _;
  refine refl a y
end;

// [s] is compatible with Leibniz equality.
opaque symbol s_eq : Π x y, P (eq nat x y) → P (eq nat (s x) (s y))
≔ begin
  assume x y xy;
  refine eqind nat x y xy (λ z, eq nat (s z) (s y)) (refl nat (s y))
end;

// [z] is right neutral for add.
opaque symbol add0r n : P (eq nat (add n z) n)
≔ begin
  refine nat_ind (λ n, eq _ (add n z) n) _ _
  { // Case Z;
  simplify;
  refine refl nat z }
  { // Case S;
  assume n h;
  simplify;
  refine s_eq (add n z) n h }
end;

// [Π n m, n + S m = S (n+m)]
opaque symbol add_succ_r : Π n m, P (eq nat (add n (s m)) (s (add n m)))
≔ begin
  assume n m;
  refine nat_ind (λ n, eq nat (add n (s m)) (s (add n m))) _ _ n
  { // Case Z
  simplify;
  refine refl nat (s m) }
  { // Case S
  simplify;
  assume pn ih;
  rewrite ih;
  refine refl nat (s (s (add pn m))) }
end;

// Commutativity of the addition.
opaque symbol addcomm : Π n m, P (eq nat (add n m) (add m n))
≔ begin
  assume n m;
  refine nat_ind (λ (n:N), eq nat (add n m) (add m n)) _ _ n
  { // Case Z
  simplify;
  symmetry; refine add0r m }
  { // Case S
  simplify;
  assume k ih;
  rewrite ih;
  rewrite add_succ_r m k;
  refine refl nat (s (add m k)) }
end;

// Adding the same value is the same as multiplying by 2.
opaque symbol add_same_times_two : Π x, P (eq nat (add x x) (mul (s(s z)) x))
≔ begin
  assume x;
  simplify;
  rewrite add0r;
  refine refl nat (add x x)
end;

//////////////////////////////////////////////////////////////////////////////
// Rewrite tests with quantified variables in the hypothesis.               //
//////////////////////////////////////////////////////////////////////////////

// This stupid test directly uses the addcomm lemma.
opaque symbol rewriteTest1 : Π a b, P (eq nat (add a b) (add b a))
≔ begin
  assume a b;
  //print;
  rewrite .[add _ b] addcomm;
  refine refl nat (add b a)
end;

// This stupid test directly uses the addcomm lemma in one place.
opaque symbol rewriteTest2 : Π a b, P (eq nat (add (add a b) b) (add (add b a) b))
≔ begin
  assume a b;
  //print;
  rewrite .[x in (add x b)] addcomm;
  refine refl nat (add (add b a) b)
end;

// This stupid test directly uses the addcomm lemma in two places.
opaque symbol rewriteTest3 : Π a b,
  P (eq nat (add (add (add a b) b) (add (add a b) b))
            (add (add (add b a) b) (add (add b a) b)))
≔ begin
  assume a b;
  //print;
  rewrite .[x in (add x b)] addcomm;
  refine refl nat (add (add (add b a) b) (add (add b a) b))
end;

// An easy contextual rewrite.
opaque symbol rewriteTest4 : Π a b,
  P (eq nat (add (add (add a b) (add a b)) a)
            (add (add (add b a) (add a b)) a))
≔ begin
  assume a b;
  rewrite .[x in (add x (add a b))] addcomm;
  refine refl nat (add (add (add b a) (add a b)) a)
end;

// A slightly more complicated contextual rewrite.
opaque symbol rewriteTest5 : Π a b,
  P (eq nat (add (add a b) (add a b)) (add (add b a) (add b a)))
≔ begin
  assume a b;
  rewrite .[x in add x x] addcomm;
  refine refl nat (add (add b a) (add b a))
end;

// An even more complicated rewrite, combining both wildcards and binders.
opaque symbol rewriteTest6 : Π a b,
  P (eq nat (add (add (add a b) a) a) (add (add a (add a b)) a))
≔ begin
  // print;
  assume a b;
  rewrite .[x in (add x _)] addcomm;
  refine refl nat (add (add a (add a b)) a)
end;

// Example 17: Very trivial SSReflect example.
symbol silly_axiom : Π m n, P (eq nat m n);

opaque symbol rewriteTest7 : Π a b c,
 P (eq nat (add (add (add a b) c) (add a b))
           (add (add (add c b) c) (add a b)))
≔ begin
  assume a b c;
  rewrite .[in x in (add x c)] (silly_axiom a c);
  refine refl nat (add (add (add c b) c) (add a b))
end;

// Very trivial SSReflect example.
opaque symbol rewriteTest8 : Π a b c,
 P (eq nat (add (add (add a b) c) (add a b))
           (add (add (add c b) c) (add a b)))
≔ begin
  assume a b c;
  rewrite .[in (add (_) c)] (silly_axiom a c);
  refine refl nat (add (add (add c b) c) (add a b))
end;

opaque symbol rewriteTest9 : Π a b c,
  P (eq nat (add (add a b) (add c (add a b)))
            (add (add a b) (add c (add b a))))
≔ begin
  assume a b c;
  rewrite .[(add a  _) in x in (add c x)] addcomm;
  refine refl nat (add (add a b) (add c (add b a)))
end;

opaque symbol rewriteTest10 : Π a b c,
  P (eq nat (add (add c (add a b)) (add (add a b) (add c (add a b))))
            (add (add c (add b a)) (add (add a b) (add c (add b a)))))
≔ begin
  assume a b c;
  rewrite .[(add a _) in x in (add c x)] addcomm;
  refine refl nat (add (add c (add b a)) (add (add a b) (add c (add b a))))
end;

opaque symbol rewriteTest11 : Π a b c,
  P (eq nat (add (add (add (add a b) c) (add (add a b) c)) (add (add a b) c))
            (add (add (add (add a b) c) (add (add b a) c)) (add (add a b) c)))
≔ begin
  assume a b c;
  rewrite .[(add a _) in x in (add (add _ x) _)] addcomm;
  refine refl nat (add (add (add (add a b) c)
           (add (add b a) c)) (add (add a b) c))
end;

opaque symbol rewriteTest12 : Π a b c,
  P (eq nat (add (add c (add a b)) (add (add a b) (add c (add a b))))
            (add (add c (add b a)) (add (add a b) (add c (add b a)))))
≔ begin
  assume a b c;
  rewrite .[(add a b) as x in (add _ x)] addcomm;
  refine refl nat (add (add c (add b a)) (add (add a b) (add c (add b a))))
end;