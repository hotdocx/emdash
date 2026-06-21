BELOW IS RESPONSE OF THE OTHER AI AGENT:
---

Here is a summary of the checks and update actions:

1. Version Discovery:
    • The system's existing installation of Lambdapi was  3.0.0 .
    • After querying the GitHub repository, the latest tagged release is indeed  3.0.0 . However, the repository has active
    updates, bug fixes, and feature improvements (such as indexing improvements, token parsing changes, and evaluation tactic
    fixes) on its  master  branch.
2. Upgrading Lambdapi:
    • Pinned the  lambdapi  package to the latest master branch source:
    opam pin add -y lambdapi git+https://github.com/Deducteam/lambdapi.git

    • Compiled and reinstalled the package:
    opam reinstall lambdapi -y

    • Verified that the version is now updated to the development build:
    3.0.0-90-gdb4f780

3. Validation:
    • Ran  make check  to typecheck emdash3_2.lp and emdash3_2_checks.lp.
    • Ran the repository's full integration checks via  make ci . All examples, rule audits, and metrics passed successfully
    under the updated Lambdapi.



---

BELOW PARTIAL COPY-PASTE OF https://github.com/Deducteam/lambdapi/blob/master/CHANGES.md


All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/).

## Unreleased

### Added

- CLI command `deindex` to remove constants from the index.
- In interactive mode, indexing of symbols from current development (as well as currently required files) and their deindexing when files are closed are now automatically supported.
- Added filtering of search results using regular expressions.
- Added support for basic Rocq syntax when interpreting queries with the `search` or `websearch` commands (forall, ->, fun, exists).
- Allow the `--require` flag to be used multiple times with the `search` and `websearch` commands.
- Ambiguity due to overloaded symbols is now solved by normalisation.
- Added streaming of results in command line search.
- Supporting `Plac` in rewriting rules.
- Fixed Stack_overflow exception due large number of search results.
- Decimal numbers can now be qualified by a module path so that one can use the decimal notation with different types in the same file.

### Changed

- Tactic `simplify` now fails if the goal cannot be simplified.
- Parser: change lp parser based on Menhir by one written by hand to provide more helpful error messages while being equally efficient.
- Tactic `eval`: Replace full SNF reduction of tactic terms by a more incremental reduction strategy using WHNF and recursively reducing only subterms that are tactic terms. Infer the type and solve unification constraints of tactic terms before reduction and interpretation as tactics.
- Syntax: do not identify {|a|} and a when a is a regular identifier anymore.
- Dedukti export: translate a module path A.B.C to C, and check that C is a valid module name in Dedukti.
- LSP server: Position of the error is removed from diagnostics when the error occurs in the file currently open in the editor.
- Syntax of search query is modified as follows : `in` is used instead of `|` (filtering). `with` is used instead of `,` (conjunction). `|` is used instead of `;` (disjunction)

### Fixed

- Convertibility test of non-linear higher-order pattern variables in rule LHS.
- Syntactical errors in Dedukti export.
- Weak head normal form test.
- Handling of module aliases.
- Dedukti export.

## 3.0.0 (2025-07-16)

### Added

- Tactic `simplify rule off` to simplify the focused goal wrt β-reduction only.
- Tacticals `orelse` and `repeat`.
- Tactic `eval` which evaluates a term and interprets it as a tactic. This allows one to define tactics using rewriting.
- Builtin `"String"` for string literals between double quotes.
- Options `--header` and `--url` for the `websearch` command.
- In search queries, replace the substring `"forall"` and `"->"` by `"Π"` and `"→"` respectively.
- Websearch queries and responses are now recorded in the log.
- Commands `debug` and `flag` with no argument to get the list of debug flags and the list of flags respectively.
- Tactic `change`.
- Modifier `private` for `open` command to not be exported.

### Changed

- Replaced Bindlib by de Bruijn (Frédéric) and closures (Bruno). The performances are slightly better than with Bindlib, especially on rewriting intensive files (the new version is 3.7 times faster on `tests/OK/perf_rw_engine.lp`). Lambdapi is now 2 times faster than dkcheck on matita, and only 2 times slower than dkcheck on holide.
- Several improvements to use the search engine:
  * normalize queries in websearch/search
  * pre-load a file in websearch (e.g. to declare implicit args)
  * paginate the output in the generated webpage
  * allow to declare rewriting rules (e.g. alignments) over defined and constant symbols
  * improve error message for overloaded symbols
- Tactic set x ≔ t: replace all subterms equal to t by x.
- Enhance the formatting of the search results.
- `require` and `open` are now recursive.

### Fixed

- Notations on external symbols are now exported.
- Make the websearch server listen on all the interfaces instead of localhost only.

## 2.6.0 (2025-01-25)

[TRUNCATED] ...


---

BELOW IS COPY-PASTE OF: https://github.com/Deducteam/lambdapi/blob/master/doc/queries.rst


Queries
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

Runs a query against the index file updated
with the assets defined in the file under development including the
assets imported by the `require` commands.
See :doc:`query_language` for the query language
specification.

::

  search spine >= (nat → nat) with hyp >= bool;

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

BELOW IS COPY-PASTE OF https://github.com/Deducteam/lambdapi/blob/master/doc/query_language.rst

Query Language
==============

Queries can be expressed according to the following syntax:

::

   Q ::= B | Q with Q | Q|Q | Q in PATH
   B ::= WHERE HOW GENERALIZE? PATTERN
   PATH ::= <identifier> | "<regexp>"
   WHERE ::= name | anywhere | rule | lhs | rhs | type | concl | hyp | spine
   HOW ::= > | = | >= | ≥
   GENERALIZE ::= generalize
   PATTERN ::= << term possibly containing placeholders _ (for terms) and V# (for variable occurrences) >>

where

* the precedence order is ``with`` > ``|`` > ``in``
* parentheses can be used as usual to force a different precedence order
* ``anywhere`` can be paired only with ``>=`` and ``name`` can be paired only with ``>=`` and no ``generalize``
* a pattern is expressed using the Lambdapi syntax except with :ref:`search <search>` and :ref:`websearch <websearch>` where, for convenience, ``forall`` is interpreted as ``Π``, ``->`` as ``→``, ``exists x:A, t`` as ``∃ (λ x:A, t)``, and ``fun x:A => t`` as ``λ x:A, t``.

The semantics of the query language is the following:

* a query ``Q`` is either a base query ``B``, the conjunction ``Q1 with Q2`` of two queries ``Q1`` and ``Q2``, their disjunction ``Q1 | Q2`` or the query ``Q IN PATH`` that behaves as ``Q``, but only keeps the results whose path is a suffix of ``PATH`` (that must be a valid path prefix) or matches the regular expression between double quotes (``""``)
* a base query ``name = ID`` looks for symbols with name ``ID`` in the library.
  The identifier ``ID`` must not be qualified.
* a base query ``WHERE HOW GENERALIZE? PATTERN`` looks in the library for occurrences of the pattern ``PATTERN`` **up to normalization rules** and, if ``generalize`` is specified, also **up to generalization** of the pattern. The normalization rules are library specific and are employed during indexing. They can be used, for example, to remove the clutter associated to encodings, to align concepts by mapping symbols to cross-library standard ones, or to standardize the shape of statements to improve recall (e.g. replacing occurrence of ``x > y`` with ``y < x``).
* ``WHERE`` restricts the set of occurrences we are interested in as follow:

  * ``anywhere`` matches without restrictions
  * ``rule``  matches only in rewriting rules
  * ``lhs``/``rhs``  matches only in the left-hand-side/right-hand-side of rewriting rules
  * ``type``  matches only in the type of symbols
  * ``spine`` matches only in the spine of the type of symbols, i.e. what is left of the type skipping zero or more (but not all) universal quantifications/implications
  * ``concl`` matches only in the conclusion of the type of symbols, i.e. what is left skipping all universal quantifications/implications
  * ``hyp`` matches only in the hypotheses of the type of symbols, i.e. in the type of an universal quantification/in the right left of an implication that occur in the spine

* ``HOW`` further restricts the set of occurrences we are interested in as follows, where positions have already been restricted by ``WHERE``:

  * ``>=`` and ``≥`` matches without restrictions
  * ``=`` the pattern must match the whole position
  * ``>`` the pattern must match a strict subterm of the position

Examples:

  *  ``hyp = (nat → bool) with hyp >= (list nat)``
     searches for theorem that have an hypothesis ``nat → bool`` and such that ``list nat`` occurs in some (other) hypothesis. The query can return ``filter_nat_list: list nat → (nat → bool) → list nat``
  *  ``concl > plus in math.arithmetics``
     searches for theorems having an hypothesis containing ``plus`` and located
     in a module whose path is a suffix of ``math.arithmetics``. The query
     can return ``plus_O : ∀x: nat. plus x O = x`` where ``plus_O`` has
     fully qualified name ``math.arithmetics.addition.plus``
  * ``concl > plus | "*.arithmetics"`` 
     searches for theorems having an hypothesis containing ``plus`` and located
     in a module whose path matches ``*.arithmetics``. The query
     can return ``math.arithmetics.addition.plus`` and ``mathematics.arithmetics.addition.plus``
  *  ``name = nat | name = NAT``
     searches for symbols named either ``nat`` or ``NAT``


---

BELOW IS COPY-PASTE OF https://raw.githubusercontent.com/Deducteam/lambdapi/refs/heads/master/doc/dtrees.rst


Decision trees
==============

The pattern matching algorithm uses decision trees. These decision trees
are attached to symbols and can be inspected for debugging purposes.
To print the decision tree of a symbol ``s`` of a module whose *module path* is
``M`` (see :doc:`Module path <module>`), its decision tree may be printed with

::

   lambdapi decision-tree M.s

The package configuration file of module ``M`` must be above the current working
directory (closer to the root of the file system), or in the same directory.

The decision trees are printed to the standard output in the `dot`_ language. A
dot file ``tree.gv`` can be converted to a png image using
``dot -Tpng tree.gv > tree.png``. The one-liner

.. code:: shell

   lambdapi decision-tree M.s | dot -Tpng | display

displays the decision tree of symbol ``M.s`` (``display`` is part of
`imagemagick`_). For other output formats, see `graphviz documentation`_.

Description of the generated graphs
-----------------------------------

Decision trees are interpreted during evaluation of terms to get the
correct rule to apply. A node is thus an instruction for the evaluation
algorithm. There are labeled nodes, labeled edges and leaves.

* Circle represent *regular* nodes. Let ``n`` be the label of the node, the next
  node is reached by performing an atomic match between the ``n``\ th term of
  the stack and the labels of the edges between the node and its children. Let
  ``t`` be the term taken from the stack and matched against the labels. The
  labels of the edges can be

  * ``s_n``, the atomic match succeeds if ``t`` is the symbol ``s`` applied to
    ``n`` arguments, the ``n`` arguments are put back in the stack;

  * ``λvn``, the atomic match succeeds if ``t`` is an abstraction. the body is
    substituted with (fresh) variable ``vn``. Both the domain of the abstraction
    and the substituted body are put back into the stack;

  * ``Πvn``, the atomic match succeeds if ``t`` is a product. The body is
    substituted with a (fresh) variable ``vn``. Both the domain of the product
    and the substituted body are put back into the stack

  * ``*``, the atomic match succeeds whatever ``t`` is.

* Rectangles represent *storage* nodes. They behave like regular nodes,
  except that the term of the stack is saved for later use.

* Diamonds represent *condition* nodes. The next node is reached by
  performing a condition check on terms that have been saved. If the
  condition is validated, the ``✓``-labeled edge is followed, and the
  ``✗``-labeled one is followed otherwise. The label of the nodes
  indicates the condition, it can be

  * ``n ≡ m`` which succeeds if the ``n``\ th and ``m``\ th saved terms are
    convertible,
  * ``xs ⊆ FV(n)`` which succeeds if the free variables of the ``n``\ th saved
    term is a superset of the free variables ``xs``.

* Triangles represent *stack check* nodes. The next node is the left child if
  the stack of arguments is empty, the right child otherwise. These nodes can
  only appear in trees built for sequential symbols.

**Note for developers:** the decision tree of ghost symbols can be printed as
well using the ``--ghost`` flag. For instance,

::

   lambdapi decision-tree --ghost M.≡

.. _dot: https://www.graphviz.org/doc/info/lang.html
.. _imagemagick: https://imagemagick.org
.. _graphviz documentation: https://graphviz.gitlab.io/_pages/doc/info/output.html
