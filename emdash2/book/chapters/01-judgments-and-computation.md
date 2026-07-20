<a id="chapter-1"></a>

# 1. Judgments, Universes, And Computation

A foundation does not begin by placing mathematical objects in a previously
given container. It begins by saying which expressions may be formed, which
expressions inhabit which classifiers, and which calculations count without
further proof. The elementary judgments have the familiar shape

$$
A;mathsf{classifier},qquad a:A,qquad a\equiv b:A.
$$

The last display uses `equiv` only as the glyph for *judgmental* or
definitional equality. It is not an inhabitant of an identity type. This
distinction will matter throughout the book: computation may make two
expressions the same input to every later rule, while a path is mathematical
data that can itself be transported, inverted, and compared.

Emdash represents its small type-like classifiers by a universe called
`Grpd`. A classifier `A:Grpd` decodes to the ambient type of its
elements, written mathematically simply as `a:A` and represented in the
kernel by `a:tau(A)`. This two-level presentation is an implementation
device. Unless a decoding boundary is at issue, we suppress `tau` and
reason in ordinary type-theoretic notation.

<a id="chapter-1-1"></a>

## 1.1 Contexts And Families

A judgment rarely stands alone. It is made in a context:

$$
x:A,quad y:B(x),quad z:C(x,y)\;\vdash\;t:D(x,y,z).
$$

Each declaration may depend on those before it. Substitution replaces a
variable by a term of the right classifier and acts through every expression
that follows. In ordinary dependent type theory this action is often left
implicit in notation. Functorial type theory will progressively expose it:
first as path action, then as functor action on directed arrows, and finally
as coherent action on higher cells.

An ordinary function classifier is written

$$
A\longrightarrow B,
$$

and a dependent function classifier as

$$
\prod_{x:A}B(x).
$$

An element `f` of the second classifier assigns `f(x):B(x)`.
Lambda abstraction introduces such an element, and application to an
argument computes by beta reduction. The nondependent function classifier is
the constant-family case.

A dependent pair classifier is

$$
\sum_{x:A}B(x).
$$

An element is a pair `(x,u)` with `u:B(x)`. Equality of dependent
pairs is not merely a pair of unrelated equalities: it consists of a base
path together with a fibre path lying over that base path. Emdash exposes this
observation explicitly. For dependent functions it exposes pointwise path
observation and a converse function-extensionality constructor. Thus the
basic Sigma and Pi layers already carry the path structure later used in
equivalence and truncation arguments.

<!-- evidence:TT-SIGMA-PI-PATHS -->

> **Formal status — checked.** Evidence `TT-SIGMA-PI-PATHS` covers
> dependent-pair projections and path views together with the checked
> `happly`/`funext` equivalence for dependent functions. This is an
> implemented equality interface, not a claim that every future categorical
> section category is merely a pointwise Pi type.

<a id="chapter-1-2"></a>

## 1.2 Three Ways Expressions Agree

The word “equal” hides three operationally different relations in the current
development.

First, a **runtime rewrite** chooses a normal form. For example, applying the
Nat eliminator to zero returns its zero branch, while applying it to a
successor returns the successor branch with the recursive result. Such a rule
is part of computation: later expressions literally see the reduced term.

Second, a **proof-time comparison** helps elaboration recognize two typed
presentations without orienting either as the other's runtime normal form.
This is useful when a mathematical construction has two stable categorical
views—for example, a displayed-family facade and the corresponding ordinary
functor-category view. Proof-time comparison is intentionally narrower than
an equation available to the mathematician.

Third, an **identity term**

$$
p:x=_A y
$$

is internal evidence. It may be an argument to a function, the index of a
dependent family, or the object of a higher identity type. Its existence does
not by itself make `x` and `y` judgmentally interchangeable.

These layers cooperate, but they should not be conflated. A rewrite is chosen
because a form is intended to compute. A proof-time comparison is chosen
because two rigid presentations should elaborate together. A path is chosen
because equality is part of the mathematics. Much of emdash's engineering is
the discipline of putting a law at the right one of these layers.

As a small example, Nat addition is defined by recursion in its left input:

$$
0+n\equiv n,qquad
\mathsf{succ}(m)+n\equiv\mathsf{succ}(m+n).
$$

Associativity is an identity term proved by Nat induction; it is not installed
as a global reassociation rewrite. The distinction keeps computation
predictable while leaving the algebra available propositionally.

> **Formal status — mathematical development.** The three-layer terminology
> is the book's explanation of the active kernel discipline. Exact rewrite
> and unification ownership remains an implementation matter governed by the
> current SOP; the mathematical chapters rely only on the checked interfaces
> cited in their evidence notes.

<a id="chapter-1-3"></a>

## 1.3 Elementary Inductive Classifiers

The initial object language contains classifiers for Empty, Unit, Bool, and
Nat. Their constructors have the expected readings:

$$
\begin{array}{c|c}
\mathsf{Empty} & \text{no constructor}\\
\mathsf{Unit} & \mathsf{tt}\\
\mathsf{Bool} & \mathsf{false},\mathsf{true}\\
\mathbb N & 0,\mathsf{succ}(n).
\end{array}
$$

An inductive classifier is characterized computationally by how dependent
data are defined from its constructors. For Nat, a motive
`P:Nat -> Grpd`, a base value `z:P(0)`, and a step

$$
s:\prod_{n:\mathbb N}P(n)\longrightarrow P(n+1)
$$

determine

$$
\mathsf{ind}_{\mathbb N}(P,z,s,n):P(n)
$$

with the zero and successor computations. Recursion is the constant-motive
special case; induction retains the dependence on the number being analyzed.
The power function in Chapter 8 is exactly such a Nat elimination, with a hom
carrier as its motive.

The equality classifiers of visible Unit, Bool, and Nat constructors also
have bounded observational computations. In particular, zero cannot equal a
visible successor, and equality of two visible successors reduces to equality
of their predecessors. These classifier computations do not erase a generic
reflexivity proof into the unique constructor of Unit, nor do they establish a
global normalization or canonicity theorem for every open Nat term.

<!-- evidence:TT-ELEMENTARY-INDUCTION -->

> **Formal status — checked.** Evidence `TT-ELEMENTARY-INDUCTION` covers
> the decoded elementary classifiers and their dependent eliminators. The
> currently selected reusable Nat library additionally supplies addition,
> associativity, successor action, and sethood. A retired experimental binary
> coproduct is not part of this edition's active elementary API.

<a id="chapter-1-4"></a>

## 1.4 Identity And Path Induction

For `x,y:A`, the classifier `x=y` records identity paths.
Reflexivity gives

$$
\mathsf{refl}_x:x=x.
$$

The fundamental elimination rule says that a property of paths can be proved
by treating the reflexive path. In the right-based form used by emdash, fix
`y:A`, take a motive

$$
P:\prod_{x:A}(x=y)\longrightarrow\mathsf{Grpd},
$$

and provide `u:P(y,refl_y)`. Then every `p:x=y` receives an
element of `P(x,p)`, and the construction computes to `u` on
literal reflexivity.

Path symmetry, transitivity, and action follow from this eliminator:

$$
\begin{aligned}
p^{-1}&:y=x,\\
q\mathbin{\cdot}p&:x=z,\\
\mathsf{ap}_f(p)&:f(x)=f(y).
\end{aligned}
$$

For a dependent function `f:prod_(x:A) B(x)`, ordinary `ap` is
not well typed because its two outputs lie in different fibres. Dependent path
action instead gives a path over `p`, written

$$
\mathsf{apd}_f(p):f(x)=_{p}^{B}f(y).
$$

This is the first appearance of a recurring idea: motion in the base changes
the classifier in which the endpoint lives. In the equality-local fragment,
the motion is invertible and is handled by path induction. In a directed
family over a category, Chapter 2 will replace it with an explicit functor
between fibres.

<!-- evidence:TT-EQUALITY-INDUCTION -->

> **Formal status — checked.** Evidence `TT-EQUALITY-INDUCTION` covers
> reflexivity, right-based dependent equality induction, `ap`, and
> `apd`. Emdash does not assume equality reflection: possessing a term
> `p:x=y` does not turn an arbitrary expression containing `x` into
> the same runtime term containing `y`.

<a id="chapter-1-5"></a>

## 1.5 Propositions As Classifiers

Under the broad propositions-as-types reading, to prove a statement is to
construct an inhabitant of its classifier. Conjunction is represented by a
pair, implication by a function, universal quantification by a dependent
function, and existential data by a dependent pair. Negation of `A` is
the function classifier

$$
\neg A:=A\longrightarrow\mathsf{Empty}.
$$

This reading is constructive: an inhabitant of an existential Sigma type
contains a witness, and an inhabitant of an implication is an operation on
evidence. It does not make every classifier proof-irrelevant. A Boolean, for
example, carries the information of which constructor was chosen. Chapter 3
will isolate the narrower classifiers whose inhabitants are all equal and
will call those *proposition-valued*.

No classical principle is needed for the WalkingEnd calculation. The negative
results there are constructive functions: an alleged equality or inverse is
sent to the empty classifier by inspecting its Nat code.

<a id="chapter-1-6"></a>

## 1.6 From Terms To Actions

The material so far is groupoidal. Identity paths are reversible, and an
ordinary function acts on them through `ap`. That is enough for
homotopy type theory's slogan that functions behave functorially on paths.
Functorial type theory retains this layer but adds a second one: a function
between object carriers is not automatically the whole meaning of a directed
functor. A directed functor must act on arrows, on arrows between arrows, and
so on.

The transition is therefore not from “types” to an unrelated category theory.
It is from implicit action generated by identity induction to explicit action
over possibly noninvertible arrows. The next chapter makes that action part of
the primary syntax.
