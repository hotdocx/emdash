<INSTRUCTIONS>
## Goal
This repo contains Lambdapi developments for “m— / emdash” functorial programming, focusing on strict/lax ω-categories, ω-functors, ω-transformations (transfors), and normalization via rewrite/unification rules.

## Advices

Our project is `emdash` version 2, whose goal is to write a Lambdapi specification @emdash2.lp for a programming language (and proof assistant) for ω-categories...  @README.md @emdash2.lp

The baseline "inspiration" is in @emdash.lp and @cartierSolution13.lp Ensure you have read those files into your memory before starting.

Examples of usage of lambdapi are in the folder @lambdapi-examples/ (if you encouter syntax errors which you are struggling to solve, you should try to find the answer in the @lambdapi-examples/ folder and try to apply the same logic to your case)

The file we are editing @emdash2.lp is draft work in progress. The immediate first milestone is to be able to express the definition/declaration of a ω-category such as its usual horizontal composition of higher (2-)arrows, its usual horizontal-vertical composition "exchange law", the “stacking” (generalized horizontal composition) of  higher (2-)cells along a (1-)cell instead of along the usual 0-cell. The second milestone is to be able to express the adjunction of functors. All these should be computational, in the style of Kosta Dosen book "cut-elimination in categories"

Advice: although we are interested in ω-categories (that is infinity/ω hierarchy of arrow, arrows of arrow, etc), as a rule of thumb, being able to express the 2-category version of what we want will, without extra efforts, also apply/extend to the ω-categories.

Advice: you should proceed and typecheck progressively/incrementally, and try and see how far you can go and how much is feasible presently. Note: always remember that we may be lacking infrastructure, concepts, symbols, rewrite/unification rules to directly express what we want right now; so you can try but keep in mind that what you want might not be feasible yet... Also try to identify whether there are some pre-requisites side-tasks, to develop the necessary concepts and rewrite/unification rules, before starting the main task.

Advice: you should try to write comments/explanations/doc about what you have implemented.

Advice: you should think hard and do a careful review and analysis; and find a design, architecture, and implementation to solve the task...

## Fast commands
- Typecheck the current development: `make check`
- Watch+recheck on save: `make watch` (logs to `logs/typecheck.log`)
- Typecheck only omega version: `lambdapi check -w emdash2.lp`
- Typecheck only 1-category version: `lambdapi check -w emdash.lp`
- Remove compilation artefacts: `make clean`

## SOP: Avoid hung typechecks (timeouts)
During early development, a “hung” typecheck usually indicates a rewrite/unification issue. Prefer a short timeout (≤ 60s) and investigate if it fires:
- One-shot with timeout: `EMDASH_TYPECHECK_TIMEOUT=60s make check`
- Watch mode already uses `scripts/check.sh` (with the same timeout mechanism).

## SOP: Continuous typecheck (watch mode)
Recommended workflow (2 terminals):
- Terminal A: `make watch`
- Terminal B: `tail -f logs/typecheck.log`

One-shot check (useful in scripts/CI):
- `python3 scripts/watch_typecheck.py --once`

Tuning / troubleshooting:
- Increase/decrease polling interval: `python3 scripts/watch_typecheck.py --interval 0.2`
- Disable screen clears: `python3 scripts/watch_typecheck.py --no-clear`

Background daemon-style (then tail the log):
- `nohup make watch >/dev/null 2>&1 &`

## Conventions
- Keep the repo in a state where `make check` succeeds.
- Prefer small, composable files/modules once the theory grows (split out kernel/infrastructure vs. examples).
- When adding rewrite/unif rules, also add a small “sanity” term (or query) exercising the rule.

## Debugging Lambdapi
- Print goals/contexts by adding `#check`/`#print` queries (see `docs/lambdapi_docs_queries.rst.txt`).
- Inspect rewrite compilation via decision trees: `lambdapi decision-tree <Module>.<symbol>`.

## Notes for Codex CLI iteration
- Keep `make watch` running and let the agent read `logs/typecheck.log` to see current typecheck failures while editing.
</INSTRUCTIONS>


## Some docs (in .rst reStructuredText format)

Some Lambdapi docs are in `docs/lambdapi_docs_syntax.rst` and `docs/lambdapi_docs_commands.rst` and `docs/lambdapi_docs_queries.rst` and `docs/lambdapi_docs_pattern.rst`, including via web search.


Lambdapi Syntax of terms (copied from `docs/lambdapi_docs_syntax.rst`)
===============

The BNF grammar of Lambdapi is in `lambdapi.bnf <https://raw.githubusercontent.com/Deducteam/lambdapi/master/doc/lambdapi.bnf>`__.

Identifiers
-----------
An identifier can be:

* a *regular* identifier: ``/`` or an arbitrary non-empty sequence of
  UTF-8 codepoints not among ``\t\r\n :,;`(){}[]".@$|?/`` that is not
  an integer number

* an *escaped* identifier: an arbitrary sequence of characters
  enclosed between ``{|`` and ``|}``

**Remark:** for any regular identifier ``i``, ``{|i|}`` and ``i`` are
identified.

**Convention:** identifiers starting with an uppercase letter denote
types (e.g.  ``Nat``, ``List``), and identifiers starting with a
lowercase letter denote constructors, functions and proofs
(e.g. ``zero``, ``add``, ``refl``).

Qualified identifiers
---------------------
A qualified identifier is an identifier of the form
``dir1.`` … ``dirn.file.id`` denoting the function symbol ``id`` defined
in the file ``dir1/`` … ``/dirn/file.lp``. To be used, ``dir1.`` …
``dirn.file`` must be required first.

**Remark**: ``dir1``, …, ``dirn`` cannot be natural numbers.

Terms
-----
A user-defined term can be either:

* ``TYPE``, the sort for types

* an unqualified identifier denoting a bound variable

* a qualified or a non-qualified symbol previously declared in the
  current file or in some previously open module, possibly prefixed by
  ``@`` to disallow implicit arguments

* an anonymous function ``λ (x:A) y z,t`` mapping ``x``, ``y`` and ``z``
  (of type ``A`` for ``x``) to ``t``

* a dependent product ``Π (x:A) y z,T``

* a non-dependent product ``A → T`` (syntactic sugar for ``Π x:A,T`` when ``x``
  does not occur in ``T``)

* a ``let f (x:A) y z : T ≔ t in u`` construction

* an application written by space-separated juxtaposition, except for
  symbols having an infix :ref:`notation` (e.g. ``x + y``)

* an infix symbol application ``x + y``

* an identifier wrapped in parentheses to access its notationless
  value (e.g. ``(+)``)

* a metavariable application ``?0.[x;y]`` that has been generated
  previously. ``?0`` alone can be used as a short-hand for ``?0.[]``.

* a pattern-variable application ``$P.[x;y]`` (in rules only). ``$P``
  alone can be used as a shorthand for ``$P.[]``, except under binders
  (to avoid mistakes).

* ``_`` for an unknown term or a term we don't care about.  It will be
  replaced by a fresh metavariable in terms, or a fresh pattern
  variable in a rule left-hand side, applied to all the variables of
  the context.

* a term enclosed between square brackets ``[`` … ``]`` for explicitly
  giving the value of an argument declared as implicit

.. String-builtin:

* a string enclosed between double quotes if the following :ref:`builtin <builtin>` is defined:

::

   builtin "String" := …; // : TYPE

* a (qualified) signed decimal number if the following builtins are in defined (in the module path used as qualification):

::

   builtin "0"  ≔ …; // : T
   builtin "1"  ≔ …; // : T
   …
   builtin "10" := …; // : T
   builtin "+" := …; // : T → T → T
   builtin "*" := …; // : T → T → T
   builtin "-" := …; // : T → T // (optional)
   type 42;

Subterms can be parenthesized to avoid ambiguities.

Decimal notation
----------------
The system can also print the values of various types using a decimal notation by defining the following builtins:

* Natural numbers in base 1 (Peano numbers):

::
   
   builtin "nat_zero" ≔ ...; // : N
   builtin "nat_succ" ≔ ...; // : N → N

* Positive natural numbers in base 2:

::
   
   builtin "pos_one" ≔ ...; // : P
   builtin "pos_double" ≔ ...; // : P → P
   builtin "pos_succ_double" ≔ ...; // : P → P

* Integer numbers in base 2:

::
   
   builtin "int_zero" ≔ ...; // : Z
   builtin "int_positive" ≔ ...; // : P → Z
   builtin "int_negative" ≔ ...; // : P → Z


---


Lambdapi Commands (copied from `docs/lambdapi_docs_commands.rst`)
========

The BNF grammar of Lambdapi is in `lambdapi.bnf <https://raw.githubusercontent.com/Deducteam/lambdapi/master/doc/lambdapi.bnf>`__.

Lambdapi files are formed of a list of commands. A command starts with
a particular reserved keyword and ends with a semi-colon.

One-line comments are introduced by ``//``:

::

   // These words are ignored

Multi-line comments are opened with ``/*`` and closed with ``*/``. They can be nested.

::

   /* These
      words are
      ignored /* these ones too */ */

.. _builtin:

``builtin``
---------------

The command ``builtin`` allows to map an internally defined string
literal ``"…"`` to a user symbol identifier. Those mappings are
necessary for other commands, tactics or notations to work.

.. _coerce_rule:

``coerce_rule``
---------------

Lambdapi can be instructed to insert function applications into terms whenever
needed for typability. These functions are called *coercions*. For instance,
assuming we have a type ``Float``, a type ``Int`` and a function
``FloatOfInt : Int → Float``, the latter function can be declared
as a coercion from integers to floats with the declaration

::

    coerce_rule coerce Int Float $x ↪ FloatOfInt $x;

Symbol ``coerce`` is a built-in function symbol that computes the coercion.
Whenever a term ``t`` of type ``Int`` is found when Lambadpi expected a
``Float``, ``t`` will be replaced by ``coerce Int Float t`` and reduced.
The declared coercion will allow the latter term to be reduced to
``FloatOfInt t``.

Coercions can call the function ``coerce`` recursively,
which allows to write, e.g.

::

    coerce_rule coerce (List $a) (List $b) $l ↪ map (λ e: El $a, coerce $a $b e) $l;

where ``Set: TYPE;``, ``List : Set → TYPE``, ``El : Set → TYPE`` and ``map`` is
the usual map operator on lists such that ``map f (cons x l) ≡ cons (f x) (map l)``.

*WARNING* Coercions are still experimental and may not mix well with
metavariables. Indeed, the term ``coerce ?1 Float t`` will not reduce to
``FloatOfInt t`` even if the equation ``?1 ≡ Int`` has been registered during
typing. Furthermore, for the moment, it is unsafe to have symbols that can be
reduced to protected symbols in the right-hand side of coercions:
reduction may occur during coercion elaboration,
which may generate unsound protected symbols.

.. _inductive:

``inductive``
-------------

The commands ``symbol`` and ``rules`` above are enough to define
inductive types, their constructors, their induction
principles/recursors and their defining rules.

We however provide a command ``inductive`` for automatically
generating the induction principles and their rules from an inductive
type definition, assuming that the following builtins are defined:

::

   ￼builtin "Prop" ≔ ...; // : TYPE, for the type of propositions
   ￼builtin "P"    ≔ ...; // : Prop → TYPE, interpretation of propositions as types

An inductive type can have 0 or more constructors.

The name of the induction principle is ``ind_`` followed by the name
of the type.

The command currently supports parametrized mutually defined dependent
strictly-positive data types only. As usual, polymorphic types can be
encoded by defining a type ``Set`` and a function ``τ:Set → TYPE``.

Example:

::

   ￼inductive ℕ : TYPE ≔
   ￼| zero: ℕ
   ￼| succ: ℕ → ℕ;

is equivalent to:

::

   ￼constant symbol ℕ : TYPE;
   ￼constant symbol zero : ℕ;
   ￼constant symbol succ : ℕ → ℕ;
   ￼symbol ind_ℕ p : π(p zero) → (Π x, π(p x) → π(p(succ x))) → Π x, π(p x);
   ￼rule ind_ℕ _ $pz _ zero ↪ $pz
   ￼with ind_ℕ $p $pz $ps (succ $n) ↪ $ps $n (ind_ℕ $p $pz $ps $n);

For mutually defined inductive types, one needs to use the ``with``
keyword to link all inductive types together.

Inductive definitions can also be parametrized as follows:

::

   (a:Set) inductive T: TYPE ≔
   | node: τ a → F a → T a
   with F: TYPE ≔
   | nilF: F a
   | consF: T a → F a → F a;

Note that parameters are set as implicit in the types of
constructors. So, one has to write ``consF t l`` or ``@consF a t l``.

For mutually defined inductive types, an induction principle is
generated for each inductive type:

::

   assert ⊢ ind_F: Π a, Π p:T a → Prop, Π q:F a → Prop,
     (Π x l, π(q l) → π(p (node x l))) →
     π(q nilF) →
     (Π t, π(p t) → Π l, π(q l) → π(q (consF t l))) →
     Π l, π(q l);
   assert ⊢ ind_T: Π a, Π p:T a → Prop, Π q:F a → Prop,
     (Π x, Π l, π(q l) → π(p (node x l))) →
     π(q nilF) →
     (Π t, π(p t) → Π l, π(q l) → π(q (consF t l))) →
     Π t, π(p t);

Finaly, here is an example of strictly-positive inductive type:

::

   inductive 𝕆:TYPE ≔ z:𝕆 | s:𝕆 → 𝕆 | l:(ℕ → 𝕆) → 𝕆;

   assert ⊢ ind_𝕆: Π p, π (p z) → (Π x, π (p x) → π (p (s x)))
     → (Π x, (Π y, π (p (x y))) → π (p (l x))) → Π x, π (p x);

   assert p a b c ⊢ ind_𝕆 p a b c z ≡ a;
   assert p a b c x ⊢ ind_𝕆 p a b c (s x) ≡ b x (ind_𝕆 p a b c x);
   assert p a b c x y ⊢ ind_𝕆 p a b c (l x) ≡ c x (λ y, ind_𝕆 p a b c (x y));

.. _notation:

``notation``
----------------

The ``notation`` commands associate to a symbol identifier (declared
in the current module or in another module) a specific notation used
by the parser and the printer of the system. The possible notations
are:

- **infix**

  ::

    notation + infix left 6.5;
    notation * infix left 7;


  * With the above notation, the system now expects ``+`` to only
    appear in expressions of the form ``x + y``. As a consequence,
    ``+`` is not a valid term anymore. To locally deactivate a
    notation, you can use ``(+)`` or ``@+`` instead.

  * A symbol declared as infix must have a type of the form ``A → A →
    A``.

  * The additional keyword ``left`` declares the symbol associative to
    the left, that is, ``x + y + z`` is parsed as ``(x + y) +
    z``. Symmetrically, the additional keyword ``right`` declares the
    symbol associative to the right, that is, ``x + y + z`` is parsed
    as ``x + (y + z)``.

  * Priority levels are used to disambiguate expressions mixing
    several operators. Hence, with the priorities declared above,
    ``x + y * z`` is parsed as ``x + (y * z)``.

  * Priorities can be natural numbers or floating point
    numbers. Hence, a priority can (almost) always be inserted between
    two different levels.

- **prefix/postfix**

  ::

   notation ¬ prefix 5;
   notation ! postfix 10;

  * Infix, prefix and postfix operators share the same levels of
    priority. Hence, depending on the priorities, ``-x + z`` is
    parsed as ``(-x) + z`` or as ``-(x + z)``.

  * Non-operator application (such as ``f x`` where ``f`` and ``x``
    are not operators) has a higher priority than any operator
    application. Hence, if ``-`` is declared as prefix, then ``- f x``
    is always parsed ``- (f x)``, no matter the priority of ``-`` is.

  * The functional arrow has a lower priority than any operator.
    Hence, ``- A → A`` is always parsed ``(- A) → A``, whatever the
    priority of ``-`` is.

- **quantifier** allows to write ```f x, t`` instead of ``f (λ x, t)``:

  ::

   symbol ∀ {a} : (T a → Prop) → Prop;
   notation ∀ quantifier;
   compute λ p, ∀ (λ x:T a, p); // prints `∀ x, p
   type λ p, `∀ x, p; // quantifiers can be written as such
   type λ p, `f x, p; // works as well if f is any symbol

.. _opaque:

``opaque``
---------------

The command ``opaque`` allows to set opaque (see **Opacity modifier**) a previously defined symbol.

::

   symbol πᶜ p ≔ π (¬ ¬ p); // interpretation of classical propositions as types
   opaque πᶜ;

.. _open:

``[private] open``
------------------

Puts into scope the symbols of the previously required modules given
in arguments. It can also be combined with the ``require`` command.

Non-private ``open`` commands are transitively inherited: if A opens B
and B opens C, then the symbols of C are also put in scope in the
environment of A.

::

   require std.bool;
   open std.bool;
   require open church.sums;

Note that ``open`` always takes as arguments qualified
identifiers. See :doc:`module` for more details.

Note that aliased modules cannot be open.

.. _require:

``require``
-----------

Informs Lambdapi to import in the current environment the (non
private) symbols, rules and builtins declared or defined in some other
modules. These symbols can be used by prefixing them with their module
path: if a module ``Stdlib.Bool`` declares a symbol ``true`` then,
after ``require Stdlib.Bool``, one can use ``true`` by writing
``Stdlib.Bool.true``. It is possible to get rid of the prefix by using
the ``open`` command.

Dependencies are transitively inherited: if A requires B and B
requires C, then the symbols of C are also imported in the current
environment.

A required module also can be aliased.

::

   require std.bool;
   require church.list as list;

Note that ``require`` always takes as arguments qualified
identifiers. See :doc:`module` for more details.

.. _rule:

``rule``
--------

Rewriting rules for definable symbols are declared using the ``rule``
command.

::

   rule add zero      $n ↪ $n;
   rule add (succ $n) $m ↪ succ (add $n $m);
   rule mul zero      _  ↪ zero;

Identifiers prefixed by ``$`` are pattern variables.

User-defined rules are assumed to form a confluent (the order of rule
applications is not important) and terminating (there is no infinite
rewrite sequences) rewriting system when combined with β-reduction.

The verification is left to the user, who can call external provers
for trying to check those properties automatically using the
:doc:`command line options <options>` ``--confluence`` and
``--termination``.

Lambdapi will however try to check at each ``rule`` command that the
added rules preserve local confluence, by checking the joinability of
critical pairs between the added rules and the rules already added in
the signature (critical pairs involving AC symbols or non-nullary
pattern variables are currently not checked). A warning is output if
Lambdapi finds a non-joinable critical pair. To avoid such a warning,
it may be useful to declare several rules in the same ``rule`` command
by using the keyword ``with``:

::

   rule add zero      $n ↪ $n
   with add (succ $n) $m ↪ succ (add $n $m);

Rules must also preserve typing (subject-reduction property), that is,
if an instance of a left-hand side has some type, then the
corresponding instance of the right-hand side should have the same
type. Lambdapi implements an algorithm trying to check this property
automatically, and will not accept a rule if it does not pass this
test.

**Higher-order pattern-matching**. Lambdapi allows higher-order
pattern-matching on patterns à la Miller but modulo β-equivalence only
(and not βη).

::

   rule diff (λx, sin $F.[x]) ↪ λx, diff (λx, $F.[x]) x × cos $F.[x];

Patterns can contain abstractions ``λx, _`` and the user may attach an
environment made of *distinct* bound variables to a pattern variable
to indicate which bound variable can occur in the matched term. The
environment is a semicolon-separated list of variables enclosed in
square brackets preceded by a dot: ``.[x;y;...]``. For instance, a
term of the form ``λx y,t`` matches the pattern ``λx y,$F.[x]`` only
if ``y`` does not freely occur in ``t``.

::

   rule lam (λx, app $F.[] x) ↪ $F; // η-reduction

Hence, the rule ``lam (λx, app $F.[] x) ↪ $F`` implements η-reduction
since no valid instance of ``$F`` can contain ``x``.

Pattern variables cannot appear at the head of an application:
``$F.[] x`` is not allowed. The converse ``x $F.[]`` is allowed.

A pattern variable ``$P.[]`` can be shortened to ``$P`` when there is no
ambiguity, i.e. when the variable is not under a binder (unlike in the
rule η above).

It is possible to define an unnamed pattern variable with the syntax
``$_.[x;y]``.

The unnamed pattern variable ``_`` is always the most general: if ``x``
and ``y`` are the only variables in scope, then ``_`` is equivalent to
``$_.[x;y]``.

In rule left-hand sides, λ-expressions cannot have type annotations.

**Important**. In contrast to languages like OCaml, Coq, Agda, etc. rule
left-hand sides can contain defined symbols:

::

   rule add (add x y) z ↪ add x (add y z);

They can overlap:

::

   rule add zero x ↪ x
   with add x zero ↪ x;

And they can be non-linear:

::

   rule minus x x ↪ zero;

Other examples of patterns are available in `patterns.lp <https://github.com/Deducteam/lambdapi/blob/master/tests/OK/patterns.lp>`__.

.. _symbol:

``symbol``
----------

Allows to declare or define a symbol as follows:

*modifiers* ``symbol`` *identifier* *parameters* [``:`` *type*] [``≔`` *term*] [``begin`` *proof* ``end``] ``;``

The identifier should not have already been used in the current module.
It must be followed by a type or a definition (or both).

The following proof (if any) allows the user to solve typing and
unification goals the system could not solve automatically. It can
also be used to give a definition interactively (if no defining term
is provided).

Without ``≔``, this is just a symbol declaration. Note that, in this
case, the following proof script does *not* provide a proof of *type*
but help the system solve unification constraints it couldn't solve
automatically for checking the well-sortedness of *type*.

For defining a symbol or proving a theorem, which is the same thing,
``≔`` is mandatory. If no defining *term* is provided, then the
following proof script must indeed include a proof of *type*. Note
that ``symbol f:A ≔ t`` is equivalent to ``symbol f:A ≔ begin refine t
end``.

Examples:

::

   symbol N:TYPE;

   // with no proof script
   symbol add : N → N → N; // a type but no definition (axiom)
   symbol double n ≔ add n n; // no type but a definition
   symbol triple n : N ≔ add n (double n); // a type and a definition

   // with a proof script (theorem or interactive definition)
   symbol F : N → TYPE;
   symbol idF n : F n → F n ≔
   begin
     assume n x; apply x;
   end;

**Modifiers:**

Modifiers are keywords that precede a symbol declaration to provide
the system with additional information on its properties and behavior.

- **Opacity modifier**:

  - ``opaque``: The symbol will never be reduced to its
    definition. This modifier is generally used for actual theorems.

- **Property modifiers** (used by the unification engine or the conversion):

  - ``constant``: No rule or definition can be given to the symbol
  - ``injective``: The symbol can be considered as injective, that is, if ``f t1 .. tn`` ≡ ``f u1 .. un``, then ``t1``\ ≡\ ``u1``, …, ``tn``\ ≡\ ``un``. For the moment, the verification is left to the user.
  - ``commutative``: Adds in the conversion the equation ``f t u ≡ f u t``.
  - ``associative``: Adds in the conversion the equation ``f (f t u) v ≡ f t (f u v)`` (in conjonction with ``commutative`` only).

    For handling commutative and associative-commutative symbols,
    terms are systemically put in some canonical form following a
    technique described `here
    <http://dx.doi.org/10.1007/978-3-540-71316-6_8>`__.

    If a symbol ``f`` is ``commutative`` and not ``associative`` then,
    for every canonical term of the form ``f t u``, we have ``t ≤ u``,
    where ``≤`` is a total ordering on terms left unspecified.

    If a symbol ``f`` is ``commutative`` and ``associative left`` then
    there is no canonical term of the form ``f t (f u v)`` and thus
    every canonical term headed by ``f`` is of the form ``f … (f (f t₁
    t₂) t₃) …  tₙ``. If a symbol ``f`` is ``commutative`` and
    ``associative`` or ``associative right`` then there is no
    canonical term of the form ``f (f t u) v`` and thus every
    canonical term headed by ``f`` is of the form ``f t₁ (f t₂ (f t₃ …
    tₙ) … )``. Moreover, in both cases, we have ``t₁ ≤ t₂ ≤ … ≤ tₙ``.

- **Exposition modifiers** define how a symbol can be used outside the
  module where it is defined. By default, the symbol can be used
  without restriction.

  - ``private``: The symbol cannot be used.
  - ``protected``: The symbol can only be used in left-hand side of
    rewrite rules.

  Exposition modifiers obey the following rules: inside a module,

  - Private symbols cannot appear in the type of public symbols.
  - Private symbols cannot appear in the right-hand side of a
    rewriting rule defining a public symbol.
  - Externally defined protected symbols cannot appear at the head of
    a left-hand side.
  - Externally defined protected symbols cannot appear in the right
    hand side of a rewriting rule.

- **Matching strategy modifier:**

  - ``sequential``: modifies the pattern matching algorithm. By default,
    the order of rule declarations is not taken into account. This
    modifier tells Lambdapi to apply rules defining a sequential symbol
    in the order they have been declared (note that the order of the
    rules may depend on the order of the ``require`` commands). An
    example can be seen in ``tests/OK/rule_order.lp``.
    *WARNING:* using this modifier can break important properties.

Examples:

::

   constant symbol Nat : TYPE;
   constant symbol zero : Nat;
   constant symbol succ (x:Nat) : Nat;
   symbol add : Nat → Nat → Nat;
   opaque symbol add0 n : add n 0 = n ≔ begin ... end; // theorem
   injective symbol double n ≔ add n n;
   constant symbol list : Nat → TYPE;
   constant symbol nil : List zero;
   constant symbol cons : Nat → Π n, List n → List(succ n);
   private symbol aux : Π n, List n → Nat;

**Implicit arguments:** Some arguments can be declared as implicit by
encloding them into square brackets ``[`` … ``]``. Then, they must not
be given by the user later.  Implicit arguments are replaced by ``_``
at parsing time, generating fresh metavariables. An argument declared
as implicit can be explicitly given by enclosing it between square
brackets ``[`` … ``]`` though. If a function symbol is prefixed by
``@`` then the implicit arguments mechanism is disabled and all the
arguments must be explicitly given.

::

   symbol eq [a:U] : T a → T a → Prop;
   // The first argument of "eq" is declared as implicit and must not be given
   // unless "eq" is prefixed by "@".
   // Hence, "eq t u", "eq [_] t u" and "@eq _ t u" are all valid and equivalent.

**Notations**: Some notation can be declared for a symbol using the
commands :ref:`notation` and :ref:`builtin`.

.. _unif_rule:

``unif_rule``
-----------------

The unification engine can be guided using
*unification rules*. Given a unification problem ``t ≡ u``, if the
engine cannot find a solution, it will try to match the pattern
``t ≡ u`` against the defined rules (modulo commutativity of ≡)
and rewrite the problem to the
right-hand side of the matched rule. Variables of the RHS that do
not appear in the LHS are replaced by fresh metavariables on rule application.

Examples:

::

   unif_rule Bool ≡ T $t ↪ [ $t ≡ bool ];
   unif_rule $x + $y ≡ 0 ↪ [ $x ≡ 0; $y ≡ 0 ];
   unif_rule $a → $b ≡ T $c ↪ [ $a ≡ T $a'; $b ≡ T $b'; $c ≡ arrow $a' $b' ];

Thanks to the first unification rule, a problem ``T ?x ≡ Bool`` is
transformed into ``?x ≡ bool``.

*WARNING* This feature is experimental and there is no sanity check
performed on the rules.


---


Queries (copied from `docs/lambdapi_docs_queries.rst`)
=======

.. _assert:
.. _assertnot:

``assert``, ``assertnot``
-------------------------

The ``assert`` and ``assertnot`` are convenient for checking that the
validity, or the invalidity, of typing judgments or equivalences.
This can be used for unit testing of Lambdapi, with both positive and
negative tests.

::

   assert ⊢ zero : Nat;
   assert ⊢ add (succ zero) zero ≡ succ zero;
   assertnot ⊢ zero ≡ succ zero;
   assertnot ⊢ succ : Nat;

.. _compute:

``compute``
-----------

Computes the normal form of a term.

.. _debug:
   
``debug``
---------

The user can activate (with ``+``) or deactivate (with ``-``) the
debug mode for some functionalities as follows:

::

   debug +ts;
   debug -s;

Each functionality is represented by a single character. To get the
list of all available flags, use the command ``debug`` with no
argument.

.. _flag:

``flag``
--------

Sets some flags ``on`` or ``off``, mainly for modifying the printing
behavior. Only the flag ``"eta_equality"`` changes the behavior of the
rewrite engine by reducing η-redexes. You can get the list of
available flags by using the command ``flag`` with no argument.

::

   flag "eta_equality" on; // default is off
   flag "print_implicits" on; // default is off
   flag "print_contexts" on; // default is off
   flag "print_domains" on; // default is off
   flag "print_meta_args" on; // default is off

.. _print:

``print``
---------

When called with a symbol identifier as argument, displays information
(type, notation, rules, etc.) about that symbol. When called with
``unif_rule`` as argument, displays the list of unification
rules. When called with ``coerce_rule`` as argument, displays the list
of coercions. Without argument, displays the list of current goals (in
proof mode only).

.. _proofterm:

``proofterm``
-------------

Outputs the current proof term (in proof mode only).

.. _prover:

``prover``
----------

Changes the prover used by the ``why3`` tactic. By default, it uses
*Alt-Ergo*.

::

   prover "Eprover";

.. _prover_timeout:
   
``prover_timeout``
------------------

Changes the timeout (in seconds) for the ``why3`` tactic. At the
beginning, the timeout is set to 2s.

::

   prover_timeout 60;

.. _search_cmd:

``search``
------------------

Runs a query between double quotes against the index file
``~/.LPSearch.db``. See :doc:`query_language` for the query language
specification.

::

  search "spine >= (nat → nat) , hyp >= bool";

.. _type:

``type``
--------

Returns the type of a term.

.. _verbose:

``verbose``
-----------

Takes as argument a non-negative integer. Higher is the verbose
level, more details are printed. At the beginning, the verbose is set
to 1.

::

   verbose 3;


---


Lambdapi tutorial (copied from `lambdapi-examples/lambdapi-examples-1-tutorial.lp`)
===============

// Learn the basics of Lambdapi in 15 minutes (this is a one-line comment).

/* Install support for Lambdapi files in Emacs or VSCode to better
visualize this file and the generated subgoals in proofs
(this is a multi-lines comment). */

/* Put this file and
https://github.com/Deducteam/lambdapi/blob/master/tests/lambdapi.pkg
in the same directory, and run emacs or vscode from this
directory. Make sure that lambdapi is in your path (do "eval `opam
env`" if you installed lambdapi with opam). */

/* In Lambdapi, you can declare type and object symbols. Symbol names
can contain unicode characters (utf8). */

/* Convention: identifiers starting with an uppercase letter denote
types, while identifiers starting with a lowercase letter denote objects. */

symbol ℕ : TYPE; // is a type declaration

// Commands are separated by semi-colons.

symbol zero : ℕ; // is an object declaration

symbol succ : ℕ → ℕ; /* means that "succ" takes an argument of type ℕ
  and returns something of type ℕ. */

// We can make definitions as follows:
symbol one ≔ succ zero;

// We can ask Lambdapi the type of a term:
type one;

// We can check that a term has a given type:
assert ⊢ one : ℕ;

// or that a term does not have a given type:
assertnot ⊢ succ : ℕ;

symbol + : ℕ → ℕ → ℕ;
notation + infix right 10;
/* means that + is declared as infix.
"right" means that "x + y + z" is the same as "x + (y + z)".
10 is the priority level of +. It is useful to parse expressions
with various infix operators (see below). */

symbol × : ℕ → ℕ → ℕ;
notation × infix right 20;
/* The priority level of × is higher than the one of +.
So "x + y × z" is parsed as "x + (y × z)". We can check it as follows: */

assert x y z ⊢ x + y × z ≡ x + (y × z);
assertnot x y z ⊢ x + y × z ≡ (x + y) × z;

/* We can now tell Lambdapi to identify any term of the form "t + 0" with "t"
by simply declaring the following rewrite rule: */
rule $x + zero ↪ $x; // rule variables must be prefixed by "$"

// We can also ask Lambdapi to evaluate a term using the declared rules:
compute zero + zero;
// and check the result:
assert ⊢ zero + zero ≡ zero;
  /* ≡ is the equational theory generated by the user-defined rules
     and β-reduction + η-reduction if the flag "eta_equality" is on. */

// The definition of + can be completed by adding a new rule later:
rule $x + succ $y ↪ succ ($x + $y);

// Several rules can also be given at once:
rule zero × $y ↪ zero
with succ $x × $y ↪ $y + $x × $y;

/* We now would like to prove some theorem about +. To this end, since
Lambdapi does not come with a pre-defined logic, we first need to
define what is a proposition and what is a proof.

You usually just need to install a package defining some logics and
require it in your development. For instance, using Opam, you can do:

opam repository -a --set-default add lambdapi https://github.com/deducteam/opam-lambdapi-repository.git # once
opam install lambdapi-stdlib

Then, in your development, you can use one of the logics defined in
this package (see https://github.com/Deducteam/lambdapi-stdlib for
more details) as follows:

require Stdlib.FOL;

This tells Lambdapi to load in the environment the symbols, rules,
etc.  declared in the package Stdlib.FOL, which defines polymorphic
first-order logic. A symbol f of Stdlib.FOL can then be refered to by
Stdlib.FOL.f.  To avoid writing Stdlib.FOL every time, you can do:

open Stdlib.FOL;

The two operations can also be done at the same time by simply writing;

require open Stdlib.FOL;

But we are going to define our own logic hereafter to show that it is
simple. */

// We first declare a type for propositions:
symbol Prop : TYPE;

// and symbols for building propositions:
symbol = : ℕ → ℕ → Prop;
notation = infix 1;

/* We then use the "proposition-as-type" technique to reduce
proof-checking to type-checking. To this end, we define a type for the
proofs of a proposition: */
injective symbol Prf : Prop → TYPE;
  /* Note that this is a type-level function, that is, a function that
     takes as argument a term of type Prop and return a term of type TYPE.

     Moreover, we declare Prf as injective. This means that Prf
     should satisfy the following property:
       if Prf(p) ≡ Prf(q) then p ≡ q.
     The verification of this property is left to the user.
     This information is used by Lambdapi to simplify a unification constraint
     of the form Prf(p) ≡ Prf(q) into p ≡ q (see below). */

/* We then say that a proof of a proposition "p" is any term of type
"Prf(p)". We therefore need to declare axioms saying which
propositions are true. For instance, a usual axiom for equality is
that it is a reflexive relation: */
symbol =-refl x : Prf(x = x);
  /* For all x, "=-refl x" is a proof of the proposition "x = x".
     Note that Lambdapi can infer the type of "x" automatically:
     the user does not need to write "symbol =-refl (x : ℕ) : Prf(x = x)". */

/* Another usual axiom is that function application preserves equality: */
symbol =-succ x y : Prf(x = y) → Prf(succ x = succ y);

/* We also need to declare that we can prove any proposition "p" on natural
numbers by induction: */
symbol ind_ℕ (p : ℕ → Prop)
  (case-zero : Prf(p zero))
  (case-succ : Π x : ℕ, Prf(p x) → Prf(p (succ x)))
     /* While "A → B" is the Lambdapi type of functions from "A" to "B",
        "Π x : A, B(x)" is the Lambdapi type of so-called "dependent" functions
        since x may occur in B(x). This is the type of functions mapping
        any element a of type A to some element of type B(a).
        It boils down to "A → B" if x does not occur in B.
        Hence, case-succ is a function that takes as arguments a natural
        number x and a proof that "p x" is true, and returns a proof that
        "p (succ x)" is true. */
  (n : ℕ)
  : Prf(p n);

/* We will later see that this induction principle can in fact be
automatically generated by Lambdapi by using the "inductive" command
when declaring ℕ, zero and succ. */
 
/* We are now ready to prove that, for any natural number "x",
"zero + x" is equal to "x", that is, to show that there exists a term, that
we will call "zero_is_neutral_for_+", of type "Π x : ℕ, Prf (zero + x = x)".
To this end, Lambdapi provides an interactive mode (launched by the keyword
"begin") to enable users to define this term step by step using tactics. */

opaque /* We declare the symbol as opaque as we do not want Lambdapi
to unfold it later. */
symbol zero_is_neutral_for_+ x : Prf (zero + x = x) ≔

begin
/* Here, in Emacs or VSCode, the system prints the following goal to prove:
?zero_is_neutral_for_+: Π x: ℕ, Prf ((zero + x) = x) */

/* To proceed by induction on x, we simply need to say that
?zero_is_neutral_for_+ should be of the form "ind_ℕ _ _ _"
where "_" stands for a term to be built.
This can be done by using the "refine" tactic: */

/* However, if we simply write "refine ind_ℕ _ _ _",
Lambdapi will complain with the following error message:
"Missing subproofs (0 subproofs for 2 subgoals)."
This is because we gave no subproof for the case-zero and case-succ arguments.
Indeed, in Lambdapi, proofs must be well structured, that is, a tactic
must be followed by as many subproofs enclosed between curly brackets
as the number of subgoals generated by the tactic. So, here, we need to write
"refine nat _ _ _ {} {}" and then write the missing subproofs. */

/* Remark: if we hadn't declared Prf as injective, we would have gotten
  4 subgoals. the first generated subgoal would not have been a typing goal
  but the following unification goal:
  "Prf (?4 n) ≡ Prf ((zero + n) = n)"
  where "?4" stands for the unknown predicate "p" that we try to prove,
  which would have been the second goal, the third goal being the case for
  zero, and the fourth goal being the case for succ.
  This is one of the interesting features of Lambdapi to have unification
  goals. However, currently, Lambdapi has only one tactic for unification
  goals, namely "solve", which is applied automatically and thus didn't work
  here. However, we can see that, to simplify this unification goal to
  "?4 n ≡ (zero + n) = n"
  we need Prf to be injective. */

refine ind_ℕ _ _ _
  { /* Here comes the proof of the first generated subgoal:
    "Prf ((zero + zero) = zero)".

    Note that Lambdapi infered the predicate to prove automatically.

    To prove the first subgoal, we can first ask Lambdapi to simplify it
    by applying user-defined rewriting rules with the tactic "simplify": */
    simplify;

    /* We then get the following goal:
    "Prf (zero = zero)"
    which can be solved by using =-refl: */
    refine =-refl zero;
  }
  { /* Here comes the proof of the second generated subgoal:
    "Π x: ℕ, Prf ((zero + x) = x) → Prf ((zero + succ x) = succ x)"

    We start by assuming a given x : ℕ such that "zero + x = x"
    using the tactic "assume": */
    assume x hyp_on_x;
    /* Again, we can simplify the goal: */
    simplify;
    /* We can then conclude by using the axiom =-succ and the assumption
    hyp_on_x: */
    refine =-succ (zero + x) x hyp_on_x;
    /* Alternatively, we could use the "rewrite" tactic of Lambdapi,
    to replace "zero + x" by "x", but this requires to set up a number
    of "builtins" (see below). */
  };
end;

/* Remark: now that we proved that "zero + x" is equal to "x", we can turn
this equality into a rewrite rule to reason modulo this rule automatically. */
rule zero + $y ↪ $y;

/* We are going to see below how this first proof can be simplified
by using more advanced features of Lambdapi. */

/* First, the induction principle on natural numbers can be automatically
generated by Lambdapi by using the command "inductive",
as long as the builtins "Prop" and "P" are set: */
builtin "Prop" ≔ Prop;
builtin "P" ≔ Prf;
inductive Nat : TYPE ≔ z : Nat | s : Nat → Nat;

/* To see what has been generated, you can write: */
print Nat;
/* prints:

constant symbol Nat: TYPE 

constructors:
  z: Nat
  s: Nat → Nat

induction principle:
  ind_Nat: Π p0: (Nat → Prop), P (p0 z) → (Π x0: Nat, P (p0 x0) → P (p0 (s x0))) → Π x0: Nat, P (p0 x0)
*/
print ind_Nat;
/* prints:

symbol ind_Nat
: Π p0: (Nat → Prop), P (p0 z) → (Π x0: Nat, P (p0 x0) → P (p0 (s x0))) → Π x0: Nat, P (p0 x0)

rules:
  ind_Nat $v0_p0 $v1_z $v2_s z ↪ $v1_z
  ind_Nat $v0_p0 $v1_z $v2_s (s $v3_x0) ↪ $v2_s $v3_x0 (ind_Nat $v0_p0 $v1_z $v2_s $v3_x0)
*/
print one; // to see the definition of ten
print +; // to see the type, notation and rules of +

/* It is also possible now to replace the tactic "refine ind_Nat _ _ _"
by a call to the tactic "induction" (see below). */

/* Similarly, we can define a type for lists of natural numbers: */
inductive List_Nat : TYPE ≔
| nil_Nat : List_Nat
| cons_Nat : Nat → List_Nat → List_Nat;

/* But what if we want to have lists of booleans, or lists of lists of
natural numbers, etc.? Lambdapi does not allow to quantify over
types. On the other hand, it is possible to interpret objects as types
using type-level rewriting rules, in the same way the function Prf
maps terms of type Prop to types. We can define polymorphic objects by
defining a type for type codes, and quantify over type codes instead
of types: */

symbol Set : TYPE; // type for type codes
injective symbol τ : Set → TYPE; // function interpreting type codes as types

// For instance, we can define a code for Nat:
symbol nat : Set;
rule τ nat ↪ Nat;

// We can now define polymorphic lists:

(a:Set) inductive 𝕃:TYPE ≔
| □ /* \Box */ : 𝕃 a
| ⸬ /* :: */ : τ a → 𝕃 a → 𝕃 a;

/* We are now going to see how to use tactics related to equality like
"reflexivity", "symmetry" and "rewrite". To this end, we need to use a
polymorphic equality and define a few more builtins that are necessary
for Lambdapi to generate the corresponding proofs. */

constant // means that we cannot add rules later
symbol ≃ [a] /* arguments between square brackets are implicit
and must not be written later, unless they are enclosed between square brackets
or if the symbol is prefixed by "@". */ 
: τ a → τ a → Prop;

notation ≃ infix 1;

constant symbol ≃-refl [a] (x:τ a) : Prf(x ≃ x);
constant symbol ≃-ind [a] [x y:τ a] : Prf(x ≃ y) → Π p, Prf(p y) → Prf(p x);
  // Leibniz principle.

builtin "T" ≔ τ;
builtin "eq" ≔ ≃;
builtin "refl"  ≔ ≃-refl;
builtin "eqind" ≔ ≃-ind;

/* We now reprove our theorem on the inductive type Nat instead of ℕ,
using the tactics "induction", "reflexivity" and "rewrite".
To this end, we first need to define addition on Nat: */

symbol ⊕ : Nat → Nat → Nat;
notation ⊕ infix right 10;
rule $x ⊕ z ↪ $x
with $x ⊕ s $y ↪ s ($x ⊕ $y);

opaque symbol zero_is_neutral_for_⊕ x : Prf(z ⊕ x ≃ x) ≔
begin
induction
  { simplify; reflexivity; }
  { assume x hyp_on_x; simplify; rewrite hyp_on_x; reflexivity; }
end;

/* Note finally that a development can be split into several
files. For instance, imagine that your development is made of file1.lp
and file2.lp, and that file2.lp uses symbols defined in
file1.lp. Then, you should create a file lambdapi.pkg with the
following two lines:

package_name = my_package
root_path = my_package

where my_package is the name of your package. Then, at the beginning
of file2.lp, you should add:

require my_package.file1;
*/
