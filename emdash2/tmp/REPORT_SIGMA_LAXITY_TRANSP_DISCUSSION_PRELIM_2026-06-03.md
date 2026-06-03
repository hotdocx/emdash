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

## Superseded Specialized-Transp Direction

After the generic `hom_postcomp_eval_func` direction, we briefly considered a
specialized primitive functor head:

```text
functord_laxity_precomp_transp_func(FF,p,u,v)
```

with intended object action:

```text
alpha |-> FF[y][alpha] o fdapp1_int_cell(FF,p,u)
```

This was an improvement over the old two-head expression because it made the
whole operation the stable owner. However, it was still one abstraction too
many.

The later review observed that the existing internal-hom extraction already
has the correct functor:

```text
fdapp1_int_hom_func(FF,p,u,v)
  : Hom_Cat(
      homd_(id_E,x,u,y,v)[p],
      homd_(FF,x,FF[x]u,y,v)[p])
```

So the Sigma-map fibre component should be one more projection of this existing
functor, not a new standalone laxity-transport functor.

## Current Preferred Direction

The current preferred and now probed design is the capped projection:

```text
fdapp1_int_hom_fapp0(FF,p,u,alpha)
```

with type:

```text
alpha : Hom_{E[y]}(E[p]u, v)

fdapp1_int_hom_fapp0(FF,p,u,alpha)
  : Hom_{D[y]}(D[p](FF[x]u), FF[y]v)
```

It is linked to the existing internal-hom functor by:

```text
fapp0 (fdapp1_int_hom_func(FF,p,u,v)) alpha
  -> fdapp1_int_hom_fapp0(FF,p,u,alpha)
```

The identity collapse is now direct on the transported fibre identity:

```text
fdapp1_int_hom_fapp0(FF,p,u,id_{E[p]u})
  -> fdapp1_int_cell(FF,p,u)
```

An intermediate `homd_id_canonical_triangle` head was initially used to name
that transported identity, but a later probe showed that the raw identity LHS
typechecks and does not reintroduce the earlier search problem after the
Sigma-map fibre component was simplified.

The terminal-source specialization similarly routes through
`fdapp1_int_hom_fapp0` before reaching `fdapp1_int_cell`.

This is cleaner than both the old two-head reconstruction and the proposed
`functord_laxity_precomp_transp_func`: the laxness comes from the original
internal displayed hom-action, and no rule has to assert that
`fdapp1_int_hom_fapp0(beta o alpha)` decomposes as a composite.

## Sigma Rule Shape

The capped `fapp1_fapp0` rule for `sigma_map_func` now has the intended shape:

```text
sigma_map_func(eta)[(p,alpha)]
  =
sigma_arrow
  ...
  p
  (fdapp1_int_hom_fapp0(eta,p,u,alpha))
```

The old surface reading:

```text
FF[y][alpha] o laxity(FF,p)[u]
```

is still a useful mathematical explanation, but it is no longer the kernel
normal form.

The `fapp1_func(sigma_map_func eta)` version remains explicitly deferred.

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

## Removed Canonical-Triangle Head

After `fdapp1_int_hom_fapp0` became the owner of the Sigma-map fibre component,
we retried the older goal of deleting:

```text
homd_id_canonical_triangle
```

and its folding rule:

```text
id_{E[p]u} -> homd_id_canonical_triangle(E,p,u)
```

The replacement rules match directly on the raw transported identity:

```text
@id
  (E[y])
  (E[p]u)
```

in both consumers:

```text
fdapp1_int_hom_fapp0(..., id_{E[p]u})
  -> fdapp1_int_cell(...)

fapp0 (tdapp1_int_hom_func ...) id_{E[p]u}
  -> tdapp1_int_cell(...)
```

The raw-identity probe passed, and the active file now contains no
`homd_id_canonical_triangle` references.

## Placement Constraints

The new capped projection head can be declared before `fdapp1_int_cell`, because
its type does not need to mention `fdapp1_int_cell`. This is necessary because
the early `sigma_map_func` capped action rule needs the head before the full
`fdapp1_int_hom_func` extraction section is reached.

The identity collapse rule must be placed after:

```text
fdapp1_int_cell
```

because its RHS is `fdapp1_int_cell`.

The fold from nested functor action:

```text
fapp0 (fdapp1_int_hom_func ...) alpha
  -> fdapp1_int_hom_fapp0 ...
```

must live after `fdapp1_int_hom_func` is declared.

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
- A later complete probe replaced the old two-head Sigma/laxity machinery with
  `fdapp1_int_hom_fapp0`, deleted the unused
  `sigma_map_transport_fibre_arrow` helper, and updated the dependent
  path-out/transitivity assertions.
- That complete probe passed:

  ```bash
  timeout 60s lambdapi check -w tmp_sigma_fdapp_complete_probe.lp
  ```

- The active file was then updated and passed:

  ```bash
  timeout 60s lambdapi check -w emdash3_2.lp
  ```

- A follow-up probe removed `homd_id_canonical_triangle` entirely and matched
  directly on the transported raw identity. The probe and the active file both
  passed:

  ```bash
  timeout 60s lambdapi check -w tmp_raw_id_probe.lp
  timeout 60s lambdapi check -w emdash3_2.lp
  ```

## PathOut Transport Finding

The path-out transitivity assertion showed why a broad strictness rule for
`PathOut_transport_func` is not the right diagnosis. `PathOut_transport_func`
is defined through:

```text
PathOut_cat_func(Z) = Sigma_func(Z) o Rep_catd_func(Z)
PathOut_transport_func(p) = PathOut_cat_func(Z)[p]
```

So its computation on canonical total arrows goes through the Sigma-map action
for the representable displayed functor:

```text
Rep_transport_func(p)
```

The focused replacement rule is therefore:

```text
fdapp1_int_hom_fapp0(Rep_transport_func(p), q, id_y)
  -> id_{q o p}
```

This is the new-head replacement for the old representable-specific
`functord_laxity_precomp_fapp0` / `functord_transport_fibre_fapp1_fapp0`
consumer.

## Current Working Assessment

The implementation performed by the successful probe is:

1. Replace `functord_laxity_precomp_func`,
   `functord_laxity_precomp_fapp0`, and
   `functord_transport_fibre_fapp1_fapp0` with
   `fdapp1_int_hom_fapp0`.
2. Rewrite the capped `sigma_map_func` action to use
   `fdapp1_int_hom_fapp0` directly.
3. Delete `sigma_map_transport_fibre_arrow`, which was only defined and
   asserted locally.
4. Add the raw transported-identity collapse:

   ```text
   fdapp1_int_hom_fapp0(..., id_{E[p]u})
     -> fdapp1_int_cell
   ```

5. Add the terminal-source and representable/cartesian specializations at the
   new head.
6. Update assertions to expect `fdapp1_int_hom_fapp0`.
7. Remove `homd_id_canonical_triangle` and consume the raw transported identity
   directly.

This report remains preliminary as a discussion record, but the core design has
now been implemented and typechecked in `emdash3_2.lp`.
