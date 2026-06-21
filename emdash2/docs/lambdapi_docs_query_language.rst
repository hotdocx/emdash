Query Language
==============

Search queries use the following grammar:

::

   Q ::= B | Q with Q | Q|Q | Q in PATH
   B ::= WHERE HOW GENERALIZE? PATTERN
   PATH ::= <identifier> | "<regexp>"
   WHERE ::= name | anywhere | rule | lhs | rhs | type | concl | hyp | spine
   HOW ::= > | = | >= | ≥
   GENERALIZE ::= generalize
   PATTERN ::= << term possibly containing placeholders _ and V# >>

The precedence order is ``with`` before ``|`` before ``in``. Parentheses can
force a different grouping.

``name`` can be paired only with ``=`` and without ``generalize``.
``anywhere`` can be paired only with ``>=``. Search and websearch accept basic
Rocq-style spellings such as ``forall``, ``->``, ``exists``, and ``fun`` and
translate them to the corresponding Lambdapi syntax.

Semantics
---------

``with`` forms a conjunction, ``|`` forms a disjunction, and ``in PATH``
filters results by a module-path suffix or by a quoted regular expression.

``name = ID`` searches for an unqualified symbol name. Other base queries
search for occurrences of ``PATTERN`` up to the normalization rules stored in
the index. With ``generalize``, matching also works up to generalization of the
pattern.

The location selectors are:

* ``anywhere``: any indexed occurrence;
* ``rule``: rewriting rules;
* ``lhs`` and ``rhs``: rule left- and right-hand sides;
* ``type``: symbol types;
* ``spine``: a type after skipping zero or more, but not all, products or
  implications;
* ``concl``: a type after skipping all products or implications;
* ``hyp``: product domains and implication hypotheses in a type spine.

The match operators are:

* ``>=`` or ``≥``: unrestricted occurrence;
* ``=``: the pattern matches the complete selected position;
* ``>``: the pattern matches a strict subterm of the selected position.

Examples
--------

::

   hyp = (nat → bool) with hyp >= (list nat)
   concl > plus in math.arithmetics
   name = nat | name = NAT

Project batch workflow
----------------------

For the EMDASH development, use the explicit ignored database maintained by:

::

   scripts/lambdapi_search.sh 'name = hom_int'
   scripts/lambdapi_search.sh 'type >= Prof_imply_cov'

This semantic search supplements ordinary lexical inspection with ``rg``.
