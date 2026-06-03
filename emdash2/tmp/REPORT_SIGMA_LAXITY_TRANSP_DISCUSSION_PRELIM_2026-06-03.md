# Preliminary Temporary Report: Sigma Laxity Transport Discussion

Date: 2026-06-03

Status: temporary, approximate reconstruction from the pre-compaction discussion
and the local context fragments `tmp/tmp-B10.md` and `tmp/tmp-C11.md`.

## Scope

This report summarizes the current discussion around the problematic
`functord_transport_fibre_fapp1_fapp0` and
`functord_laxity_precomp_fapp0` design in `emdash3_2.lp`.

The active implementation currently expresses the Sigma-map arrow action by
first building a transported fibre functor action:

```text
FF[y][alpha]
```

through `functord_transport_fibre_fapp1_fapp0`, then feeding that into
precomposition by the displayed laxity cell:

```text
precompose_by(laxity(FF,p)[u])[FF[y][alpha]]
```

through `functord_laxity_precomp_func` /
`functord_laxity_precomp_fapp0`.

The concern is that this splits one mathematically meaningful operation into
two independent stable heads and then relies on special consumer rules to make
the identity/canonical-transport case collapse.

## Current Problem

The intended Sigma-map fibre component is:

```text
alpha |-> FF[y][alpha] o laxity(FF,p)[u]
```

where:

```text
alpha : Hom_{E[y]}(E[p]u, v)
laxity(FF,p)[u] : D[p](FF[x]u) -> FF[y](E[p]u)
```

so the result is:

```text
D[p](FF[x]u) -> FF[y]v
```

The current code creates a stable head for only the `FF[y][alpha]` part:

```text
functord_transport_fibre_fapp1_fapp0(FF,p,u,v,alpha)
```

and separately creates a stable capped precomposition head:

```text
functord_laxity_precomp_fapp0(FF,p,u,w,beta)
```

This is technically usable in some cases, but it is misleading. The stable
head that should own computation is not `FF[y][alpha]` alone; it is the whole
operation:

```text
FF[y](-) o laxity(FF,p)[u]
```

The existing special collapse:

```text
precompose_by(laxity)[FF[y][canonical_id]] -> laxity
```

is also too dependent on the artificial intermediate head.

## B10 Stage: Functoriality In Alpha

The discussion in `tmp/tmp-B10.md` corrected an earlier too-capped proposal.
The key point was that the desired primitive should be functorial in `alpha`,
not merely a one-off value for a single `alpha`.

The first general candidate was:

```text
hom_postcomp_eval_func(F,W,X,Y,g)
  : Hom_B(X,Y) -> Hom_A(W,F[Y])
```

with intended object action:

```text
alpha |-> F[alpha] o g
```

and higher action:

```text
theta |-> F[theta] o g
```

This was motivated by the existing covariant hom package:

```text
hom_(F,W)[Y] = Hom_A(W,F[Y])
```

and by the existing stable projection:

```text
fapp1_func (hom_ F W) -> hom_postcomp_tele_func(F,W,X,Y)
```

The important conclusion from this stage remains valid:

```text
the needed head must be a functor in alpha.
```

This matters immediately for the capped Sigma action, and later for a possible
`fapp1_func(sigma_map_func eta)` rule.

## B10 Infrastructure Issue: Evaluation And Logic Operations

The B10 discussion also exposed a broader infrastructure problem: the natural
semantic definition of `hom_postcomp_eval_func` is not an isolated new
operation. It wants to be a fold from ordinary evaluation after a telescope:

```text
fapp0_func(g) o hom_postcomp_tele_func(F,W,X,Y)
  -> hom_postcomp_eval_func(F,W,X,Y,g)
```

More explicitly, for:

```text
g : Hom_A(W,F[X])

hom_postcomp_tele_func(F,W,X,Y)
  : Hom_B(X,Y)
      -> Functor(Hom_A(W,F[X]), Hom_A(W,F[Y]))

fapp0_func(g)
  : Functor(Hom_A(W,F[X]), Hom_A(W,F[Y]))
      -> Hom_A(W,F[Y])
```

their composite has the desired object action:

```text
alpha |-> hom_postcomp_tele_func(F,W,X,Y)[alpha][g]
       = F[alpha] o g
```

So the intended fold is:

```text
comp_cat_fapp0
  (fapp0_func(g))
  (hom_postcomp_tele_func(F,W,X,Y))
  -> hom_postcomp_eval_func(F,W,X,Y,g)
```

This is conceptually clean, but it revealed that `fapp0_func` is currently only
a fixed-object evaluation tool, not part of a general structural calculus for
multi-argument functors.

The more general missing layer is ordinary logical structure on curried
functors. In particular, there should eventually be stable operations for:

```text
exchange/symmetry:
  sym(H : Functor A (Functor B C))
    : Functor B (Functor A C)

  sym(H)[b][a] = H[a][b]
```

Object-level evaluation by `fapp0_func(b)` can be seen as one projection of
this exchange/evaluation behavior:

```text
sym(H)[b] = fapp0_func(b) o H
```

The corresponding `fapp1_func` / `fapp1_fapp0` projections of `sym` would be
useful later, because they would expose stable heads for varying the argument
that was previously inner.

The same family of structural operations should eventually include
contraction/diagonal and weakening/constant operations. The exact kernel
orientation still needs design, but the intended logic is:

```text
contraction/diagonal:
  duplicate or identify two functorial inputs

weakening/constant:
  ignore an input, already partly represented by Const_func
```

For example, a future diagonal package might turn a two-input curried functor:

```text
H : Functor A (Functor A B)
```

into:

```text
diag(H) : Functor A B
diag(H)[a] = H[a][a]
```

and weakening is already represented in the one-input case by:

```text
Const_func(b) : Functor A B
Const_func(b)[a] = b
```

This broader structural layer is not required for the immediate specialized
Sigma/laxity primitive, but it explains why `hom_postcomp_eval_func` was a
promising but nontrivial generic direction. A robust future implementation
should probably develop this exchange/evaluation/diagonal/weakening calculus
instead of adding ad hoc folds for each curried helper.

## C11 Stage: Generic Postcomposition Probe

The discussion in `tmp/tmp-C11.md` explored making the generic postcomposition
evaluation itself a primitive package:

```text
hom_postcomp_eval_func(F,W,X,Y,g)
```

At one point a primitive capped head was considered:

```text
hom_postcomp_eval_fapp0(F,W,X,Y,g,alpha)
```

with identity rules such as:

```text
hom_postcomp_eval_fapp0(F,W,X,X,g,id_X) -> g
hom_postcomp_eval_fapp0(..., homd_id_canonical_triangle(E,p,u)) -> g
```

The probe reportedly showed that the generic heads and some identity rules
could typecheck. It also showed that writing the Sigma action as:

```text
fapp0 (hom_postcomp_eval_func ...) alpha
```

was lighter than writing a capped head directly.

However, this stage was later refined. The primitive capped
`hom_postcomp_eval_fapp0` is no longer the preferred direction.

## Superseded Intermediate Conclusion

After C11, the tentative generic plan was:

```text
fapp0 (hom_postcomp_eval_func F W X Y g) alpha
  -> comp_fapp0 (F[alpha]) g
```

and then use existing composition identity rules to recover:

```text
F[id] o g -> g
```

This is cleaner for ordinary strict functors, but it is not sufficient for the
Sigma/laxity problem under discussion.

The issue is that the critical identity case is not just ordinary strict
postcomposition. In the Sigma transport path, the relevant source identity
often normalizes first to:

```text
homd_id_canonical_triangle(E,p,u)
```

and expanding through:

```text
comp_fapp0 (FF[y][canonical_id]) fdapp1_int_cell
```

would again require an additional rule about `FF[y]` applied to that canonical
identity, or would pressure the system toward a strict-functor identity
collapse in a place where the intended owner is really the displayed laxity
transport package.

So the generic `hom_postcomp_eval_func` idea is useful background, but it is
not the final owner for this Sigma/laxity computation.

## Current Preferred Direction

The current preferred design is a specialized primitive functor head:

```text
functord_laxity_precomp_transp_func(FF,p,u,v)
```

with intended type:

```text
Functor
  (Hom_{E[y]}(E[p]u, v))
  (Hom_{D[y]}(D[p](FF[x]u), FF[y]v))
```

and intended surface meaning:

```text
alpha |-> FF[y][alpha] o fdapp1_int_cell(FF,p,u)
```

but it should not be definitionally expanded to that composite. It should be a
primitive stable head whose rewrite behavior is owned directly by the
Sigma/laxity transport calculus.

The key rules should be Došen-style cut-elimination/accumulation rules:

```text
functord_laxity_precomp_transp_func(FF,p,u,E[p]u)[canonical_id]
  -> fdapp1_int_cell(FF,p,u)

FF[y][beta] o
  functord_laxity_precomp_transp_func(FF,p,u,v)[alpha]
  ->
functord_laxity_precomp_transp_func(FF,p,u,w)[beta o alpha]
```

The first rule should probably consume `homd_id_canonical_triangle`, because
the current code folds the raw fibre identity at `E[p]u` to that canonical head.

## Sigma Rule Shape

The capped `fapp1_fapp0` rule for `sigma_map_func` should eventually be
rewritten from the old two-head expression to:

```text
sigma_map_func(eta)[(p,alpha)]
  =
sigma_arrow
  ...
  p
  (fapp0
    (functord_laxity_precomp_transp_func eta p u v)
    alpha)
```

This keeps the functor object visible and functorial in `alpha`, without
exposing `FF[y][alpha]` as the stable owner of the computation.

The `fapp1_func(sigma_map_func eta)` version is explicitly deferred.

## Old Heads To Retire Or Isolate

The following old heads/rules should not remain as alternate normal-form
owners once the new design is implemented:

```text
functord_laxity_precomp_func
functord_laxity_precomp_fapp0
functord_transport_fibre_fapp1_fapp0
```

In particular, the existing special consumer rule of the form:

```text
functord_laxity_precomp_fapp0(...,
  functord_transport_fibre_fapp1_fapp0(..., homd_id_canonical_triangle))
  -> fdapp1_int_cell
```

should be removed or replaced, not kept in parallel.

Assertions that mention the old heads must be rewritten to the new expected
stable form.

## Placement Constraints

The new functor head can be declared before `fdapp1_int_cell`, because its type
does not need to mention `fdapp1_int_cell`.

The identity/canonical collapse rule must be placed after:

```text
fdapp1_int_cell
homd_id_canonical_triangle
```

because its RHS is `fdapp1_int_cell` and its LHS likely consumes
`homd_id_canonical_triangle`.

## Probe Status

Known from the discussion:

- Generic `hom_postcomp_eval_*` heads were probed and appeared feasible.
- A direct Sigma rule using `fapp0 (hom_postcomp_eval_func ...) alpha` was
  lighter than using an explicit capped primitive head.
- That generic route is now considered partially superseded for this specific
  Sigma/laxity issue.
- A very rough post-compaction probe of the specialized
  `functord_laxity_precomp_transp_func` shape timed out under a 60 second
  check, but the probe was not refined enough to count as negative evidence.

## Current Working Assessment

The likely feasible implementation plan is:

1. Add `functord_laxity_precomp_transp_func` as a primitive functor head.
2. Rewrite the capped `sigma_map_func` action to use it directly.
3. Add the canonical identity collapse:

   ```text
   fapp0 (functord_laxity_precomp_transp_func ... E[p]u)
         homd_id_canonical_triangle
     -> fdapp1_int_cell
   ```

4. Add the accumulation rule:

   ```text
   FF[y][beta] o transp(alpha) -> transp(beta o alpha)
   ```

5. Remove or comment the old two-head consumer rules and update assertions.
6. Probe incrementally in a temporary copy, keeping reducible endpoint slots
   implicit on LHSs where possible.

This report is intentionally preliminary. The next step should be a more
precise implementation plan with exact Lambdapi declarations, placement edits,
old-rule removal list, and focused assertions.
