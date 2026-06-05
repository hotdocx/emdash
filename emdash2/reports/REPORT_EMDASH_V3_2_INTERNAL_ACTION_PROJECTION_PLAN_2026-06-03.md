# EMDASH v3.2 Internal-Action Projection Plan

> Notation warning: this report predates the 2026-06-05 canonical surface syntax. Use `REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md` for current notation; older formulas may use retired arrow/transformation glyphs.


Date: 2026-06-03

This report records the implementation plan and current status for three related
cleanup and extension tasks in `emdash3_2.lp`:

- add the missing ordinary identity-specialized projection
  `fapp1_at_transf`;
- add a generic projection ladder for `tdapp1_int_fapp0_transfd`, the object
  action of `tdapp1_int_func_transfd`;
- complete the neutral canonical naming of the displayed internal-action
  projection heads as `fdapp1_int_*`.

The plan follows the v3.2 stable-head SOP: introduce small projection heads only
where they expose a meaningful semantic layer, keep reducible endpoint families
out of rewrite-rule left-hand sides, and validate each new rewrite by a focused
assertion in a temporary probe before editing the active file.

## Implementation Status

Implemented in `emdash3_2.lp` on 2026-06-03:

- `fapp1_at_transf` and its projection rules;
- generic displayed internal-action projections:
  `homd_tdapp1_src_sec`, `homd_tdapp1_tgt_func`,
  `tdapp1_int_section_arrow`, `tdapp1_int_tgt_arrow`,
  `tdapp1_int_presheaf_arrow`, `tdapp1_int_hom_func`, and
  `tdapp1_int_cell`;
- identity-specialization folds from the generic `tdapp1_int_*` heads back to
  the canonical `fdapp1_int_*` heads;
- canonical identity-specialized displayed projection heads:
  `fdapp1_int_section_arrow`, `fdapp1_int_tgt_arrow`,
  `fdapp1_int_presheaf_arrow`, `fdapp1_int_hom_func`, and
  `fdapp1_int_cell`.

The canonical rename is complete. No compatibility aliases for the earlier
displayed-laxity projection names are kept in `emdash3_2.lp`.

Validation after implementation:

```bash
timeout 60s lambdapi check -w emdash3_2.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
```

## Current Reviewed State

The ordinary internal hom-action already has the generic transfor ladder:

```text
tapp1_int_fapp0_transf(epsilon)
  -> tapp1_at_transf(X,epsilon)
  -> tapp1_func(X,Y,epsilon)
  -> tapp1_fapp0(epsilon,f).
```

The identity-specialized ordinary functor action exists as:

```text
fapp1_int_transf(F)
```

and the later projections exist as:

```text
fapp1_func(F,X,Y)
fapp1_fapp0(F,f).
```

The missing ordinary rung is:

```text
fapp1_at_transf(F,X).
```

The displayed internal hom-action has the high-level generic package:

```text
tdapp1_int_func_transfd(FF,GG)
tdapp1_int_fapp0_transfd(epsilon)
tdapp1_int_fapp1_func_transfd(epsilon,epsilon')
```

and the identity-specialized package:

```text
fdapp1_int_transfd(FF).
```

For `fdapp1_int_transfd`, the checked component extraction ladder already
exists, but its names are application-specific:

```text
fdapp1_int_transfd(FF)
  -> fdapp1_int_section_arrow(FF,x,u)
  -> fdapp1_int_tgt_arrow(FF,x,u,y)
  -> fdapp1_int_presheaf_arrow(FF,x,u,y,v)
  -> fdapp1_int_hom_func(FF,p,u,v)
  -> fdapp1_int_cell(FF,p,u).
```

That ladder is currently used by Sigma-map laxity, Pi target transport, and
path-induction computations. It should not be disrupted casually.

## Phase 1: Add `fapp1_at_transf`

Add a stable fixed-source projection for the identity-specialized ordinary
internal action:

```text
fapp1_at_transf(F,X)
  : Transf(hom_A(X,-), hom_B(F[X],F[-])).
```

The intended declaration shape is:

```text
symbol fapp1_at_transf : Π [A B : Cat], Π (F : τ (Functor A B)),
  Π (X : τ (Obj A)),
  τ (Transf
      (@hom_ A A (@id_func A) X)
      (@hom_ B A F (@fapp0 A B F X)));
```

Install the projection rules:

```text
tapp0_fapp0 X (fapp1_int_transf F)
  -> fapp1_at_transf(F,X)

tapp1_at_transf(X,id_F)
  -> fapp1_at_transf(F,X)

tapp0_fapp0 Y (fapp1_at_transf(F,X))
  -> fapp1_func(F,X,Y).
```

The middle identity-specialization fold is important for confluence. Without it,
the term

```text
tapp0_fapp0 X (tapp1_int_fapp0_transf(id_F))
```

can reduce through the generic path to `tapp1_at_transf(X,id_F)` or through the
identity fold to `tapp0_fapp0 X (fapp1_int_transf F)`. Both paths should join at
`fapp1_at_transf(F,X)`.

Required regression assertions:

```text
tapp0_fapp0 X (fapp1_int_transf F)
  == fapp1_at_transf(F,X)

tapp1_at_transf(X,id_F)
  == fapp1_at_transf(F,X)

tapp0_fapp0 Y (fapp1_at_transf(F,X))
  == fapp1_func(F,X,Y)

tapp0_fapp0 Y (tapp0_fapp0 X (fapp1_int_transf F))
  == fapp1_func(F,X,Y)

fapp0 (fapp1_func(F,X,Y)) f
  == fapp1_fapp0(F,f).
```

Implementation notes:

- Put this near the existing `fapp1_int_transf` and `tapp1_at_transf` section.
- Keep source/target endpoint arguments as `_` on rule left-hand sides unless a
  probe shows Lambdapi needs them.
- Probe in a temporary copy first, because this overlaps the existing
  `tapp1_int_fapp0_transf(id_F) -> fapp1_int_transf(F)` fold.

## Phase 2: Add Generic `tdapp1_int` Projections

The displayed generic object action should receive a projection ladder analogous
to the checked `fdapp1` ladder, but parameterized by an arbitrary displayed
transfor:

```text
epsilon : Transfd(FF,GG).
```

The intended conceptual ladder is:

```text
tdapp1_int_fapp0_transfd(epsilon)
  -> tdapp1_int_section_arrow(epsilon,x,u)
  -> tdapp1_int_tgt_arrow(epsilon,x,u,y)
  -> tdapp1_int_presheaf_arrow(epsilon,x,u,y,v)
  -> tdapp1_int_hom_func(epsilon,p,u,v)
  -> tdapp1_int_cell(epsilon,p,u).
```

The target endpoint differs from the identity-specialized `fdapp1` case. For an
arbitrary `epsilon : FF => GG`, the final canonical-triangle cell should have
the shape:

```text
tdapp1_int_cell(epsilon,p,u)
  : D[p](FF[x](u)) -> GG[y](E[p](u)).
```

This specializes to the displayed-functor laxity cell when
`epsilon = id_transfd(FF)`:

```text
tdapp1_int_cell(id_FF,p,u)
  -> fdapp1_int_cell(FF,p,u).
```

Add neutral helper endpoints before the projection heads:

```text
homd_tdapp1_src_sec(FF,GG,x,u)
  = homd_src_sec(GG,x,FF[x](u))

homd_tdapp1_tgt_func(FF,GG,x,u,y)
  = homd_tdapp1_src_sec(FF,GG,x,u)[y].
```

These are definitions, not rewrite discriminators.

The generic projection heads should then mirror the existing `fdapp1` heads:

```text
tdapp1_int_section_arrow(epsilon,x,u)
  : homd_int(id_E)[x](u)
      -> homd_int(GG)[x](FF[x](u))

tdapp1_int_tgt_arrow(epsilon,x,u,y)
  : homd_int(id_E)[x](u)[y]
      => homd_int(GG)[x](FF[x](u))[y]

tdapp1_int_presheaf_arrow(epsilon,x,u,y,v)
  : homd_int(id_E)[x](u)[y](v)
      -> homd_int(GG)[x](FF[x](u))[y](v)

tdapp1_int_hom_func(epsilon,p,u,v)
  : homd_(id_E,x,u,y,v)[p]
      -> homd_(GG,x,FF[x](u),y,v)[p].
```

Install projection rules in the same stable-head style as the existing
`fdapp1_int_*` rules:

```text
tapp0_fapp0 u
  (tdapp0_fapp0 x (tdapp1_int_fapp0_transfd(epsilon)))
  -> tdapp1_int_section_arrow(epsilon,x,u)

tapp0_fapp0 Terminal_obj
  (tdapp0_fapp0 y (tdapp1_int_section_arrow(epsilon,x,u)))
  -> tdapp1_int_tgt_arrow(epsilon,x,u,y)

tapp0_fapp0 v
  (tdapp1_int_tgt_arrow(epsilon,x,u,y))
  -> tdapp1_int_presheaf_arrow(epsilon,x,u,y,v)

fapp1_fapp0 (fapp0_func p)
  (tdapp1_int_presheaf_arrow(epsilon,x,u,y,v))
  -> tdapp1_int_hom_func(epsilon,p,u,v)

tapp0_fapp0 p
  (tdapp1_int_presheaf_arrow(epsilon,x,u,y,v))
  -> tdapp1_int_hom_func(epsilon,p,u,v)

fapp0
  (tdapp1_int_hom_func(epsilon,p,u,E[p]u))
  (homd_id_canonical_triangle(E,p,u))
  -> tdapp1_int_cell(epsilon,p,u).
```

Required regression assertions:

- object action of `tdapp1_int_func_transfd` still reduces to
  `tdapp1_int_fapp0_transfd`;
- first, second, third, and fourth generic projections reduce to the new heads;
- the canonical-triangle endpoint reduces to `tdapp1_int_cell`;
- the identity-specialized generic ladder joins the existing `fdapp1` ladder.

Do not add a whole-transfor `functord_laxity_transf` yet. The current reports
defer that interface until the source object `u` can be internalized cleanly.
The generic `tdapp1_int_cell` is a component-level interface and is therefore
compatible with the current architecture.

## Phase 3: Naming And Compatibility Strategy

The neutral `fdapp1_int_*` names are now the canonical kernel names for the
identity-specialized displayed internal-action projection ladder:

```text
fdapp1_int_section_arrow
fdapp1_int_tgt_arrow
fdapp1_int_presheaf_arrow
fdapp1_int_hom_func
fdapp1_int_cell
```

No compatibility aliases are retained. The canonical normal form is the neutral
`fdapp1_int_*` family.

The `functord_laxity_precomp_func` and `functord_laxity_precomp_fapp0` names
should stay for now. They are not merely projection rungs; they are
consumer-local precomposition heads used by Sigma-map normalization.

## Validation Checklist

For each phase:

1. Copy `emdash3_2.lp` to a temporary probe file.
2. Add only the proposed symbols, rules, and focused assertions for that phase.
3. Run:

   ```bash
   timeout 30s lambdapi check -w tmp_internal_action_projection_probe.lp
   ```

4. If the probe passes, move the minimal working change into `emdash3_2.lp`.
5. Run:

   ```bash
   EMDASH_TYPECHECK_TIMEOUT=60s make check
   ```

6. Remove the temporary probe file.

The first implementation step should be Phase 1 only. It is small, has a clear
missing rung, and will exercise the same identity-specialization join pattern
needed later for the displayed projection rename.
