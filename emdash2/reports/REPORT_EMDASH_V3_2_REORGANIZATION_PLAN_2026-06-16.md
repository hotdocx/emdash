# Emdash v3.2 Single-File Reorganization Plan

Date: 2026-06-16

Active file: `emdash3_2.lp`

Purpose: reorganize `emdash3_2.lp` into a coherent, split-ready sequential order while keeping a single file for now. The future split should have a mostly linear dependency structure and coherent logical units.

## Current Findings

The present structure is typechecking, but a few sections are doing mixed jobs:

- Section 11 mixes reusable classifiers (`Rep_catd`, `Edge_catd_func`, `HomPresheaf_catd_func`) with applications (`PathOut`, path induction, transitivity benchmark).
- Section 13 mixes generic covariant fibre transport, path-induction computation rules, transitivity benchmark terms, and the `homd_int` projection cascade.
- Section 16 mixes generic displayed-component notation with path-induction-specific and Sigma-uncurrying projection rules.
- Section 17 is a "late bridge" section: Sigma/Pi helpers, product-pair telescope rules, ordinary structural logic, internal Pi action, and PathOut target transport aliases.
- Some declarations are intentionally early while their projection rules are delayed because dependencies were not available yet. Those should become explicit "bridge/extension" slices.

## Proposed Target Organization

Keep one file for now, but reorganize as if these were future modules:

1. Header, TOC, SOP Notes
   - Surface syntax authority.
   - Table of contents.
   - Future split map, e.g. `kernel`, `ordinary`, `directed`, `homd`, `structural`, `applications`.

2. Kernel Foundations
   - `Grpd`, `τ`, equality.
   - Encoded Sigma object layers.
   - Core `Cat`, `Obj`, `Hom_cat`, `id`, `comp_fapp0`, `Op_cat`, `Path_cat`.

3. Ordinary Category Calculus
   - `Functor_cat`, `fapp*`.
   - `Cat_cat`, `Grpd_cat`.
   - `Transf_cat`, `tapp0`, `tapp1`.
   - Ordinary identity/composition/op/terminal/constant functors.
   - Products, product projections/pairing.
   - Ordinary composition actions, naturality, product functor packages, evaluation, curry/uncurry, adjunctions, ordinary internal hom-action.

4. Directed Family Calculus
   - `Catd_cat`, `Functord_cat`, `Transfd_cat`.
   - `Fibre_cat`, `Pullback_catd`, `catd_transport_func`.
   - `Const_catd`, `Terminal_catd`, `Op_catd`, `Op_funcd`.
   - `Pi_cat`, `Pi_func`, `Pi_int_funcd`, `Pi_pullback_funcd`.
   - `homd_` endpoint notation.
   - `Sigma_cat`, Sigma homs, Sigma maps, Sigma-induced families.
   - `Functor_catd`, `Hom_catd`, `Transf_catd`.

5. Representables and Dependent Hom Infrastructure
   - `Rep_catd`, `Rep_transport_func`.
   - `Edge_catd_func`, `Presheaf_catd_func`, `HomPresheaf_catd_func`.
   - `Homd_target_section_catd`, `Homd_target_catd`, `homd_int`.
   - `homd_src_func`, `homd_src_sec`, `homd_tgt_func`.
   - `FibCov_target_catd`, `fib_cov_int`, `fib_cov_transf`.

6. Displayed Hom-Action and Laxity Extraction
   - `tdapp1_int_func_transfd`, `fdapp1_int_transfd`.
   - `tdapp0_func`, `tdapp0_fapp0`, `Fibre_func`, `Fibre_transf`.
   - `functord_transport_*`.
   - `fdapp1_int_*`, `tdapp1_int_*`, `fdapp1_int_cell`, `tdapp1_int_cell`.
   - Sigma-map fixed-endpoint hom-action rules that depend on displayed hom-action.

7. Structural Logic and Bridges
   - Sigma/Pi weakening/evaluation helpers.
   - `const_section_func`.
   - Product-pair telescope projection rules.
   - Ordinary `Const_func_func`, exchange, diagonal.
   - Generic ordinary functor hom-action.
   - `section_pullback_func`, `section_pullback_transf`.
   - Internal Pi action rules through `fdapp1_int_cell`.

8. Applications
   - `PathOut_cat`, `PathOutMotives_catd`.
   - Path induction source/target packages.
   - `PathInd_transfd`, `PathInd_funcd`, component rules.
   - PathOut target transport aliases.
   - Transitivity/composition benchmark: `CompTarget_catd`, `CompMotive_catd`, `path_comp_sec`, `path_comp_func`.
   - Nested telescope stress examples.

9. Check Catalog
   - Human-readable normal-form catalog only.
   - Keep executable checks in `emdash3_2_checks.lp`.

## Important Dependency Constraints

A few moves need special care:

- Product-valued transfor rules require `Product_cat` before `Transf_cat` product projections.
- Product-pair telescope rules depend on `Const_transf`, `Pi_cat`, and `const_section_func`, so the declaration can stay with products but its projection rules belong later in a bridge section.
- `PathInd_transfd` component rules depend on `tdapp0_fapp0`; if `PathInd_transfd` moves to Applications, its component rules should move with it.
- Sigma-map full hom-action depends on `fdapp1_int_presheaf_arrow`; base Sigma rules should stay earlier, but fixed-endpoint Sigma hom-action belongs in the displayed hom-action extension layer.
- Internal Pi action via `fdapp1_int_cell` must stay after `fdapp1_int_cell`.

## Implementation Plan

1. Create a temporary probe file, e.g. `tmp/emdash3_2_reorg_probe.lp`, copied from the current file.
2. Produce a symbol/rule inventory before moving anything, so we can compare that no declaration disappeared.
3. Reorder the probe in coarse contiguous blocks first, not symbol-by-symbol.
4. After each major block move, run:
   - `lambdapi check -w tmp/emdash3_2_reorg_probe.lp`
5. Once the probe is stable, apply the same ordering to `emdash3_2.lp`.
6. Run final validation:
   - `EMDASH_TYPECHECK_TIMEOUT=60s make check`
   - `git diff --check`
   - symbol/rule inventory comparison
7. Only after the reorganization typechecks should we add/refine the top-level TOC and future split map.

## Recommendation

The first implementation pass should reorganize at the section/block level and add the TOC. Avoid trying to rename symbols, split files, or redesign dependencies during the same pass.
