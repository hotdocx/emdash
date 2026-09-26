# Action-Profile Integration: Baseline Homology Import Repair

Date: 2026-09-26

Status: validated import-only correction discovered by the bounded suite

This supports the [integration plan](EMDASH_ACTION_PROFILE_INTEGRATION_PLAN.md).
The ordinary classifier work remains a separate, unfinished semantic tranche.

The standalone check of
[homology cycle maps](../emdash2/emdash3_2_homology_cycle_maps.lp) failed with
`Unknown symbol computational_homology_preadditive`, receipt
`20260926T041048Z-fcc00bb406084bb7a9bf640fb5354562`.
Its original sixteen-file LP import closure is byte-identical to baseline
main `37ce19d5` and excludes the changed profile owner.

The used definitions already belong to the active
[computational homology owner](../emdash2/emdash3_2_computational_homology.lp).
That owner contains the retained kernel/lift/cokernel construction and imports
the shared homology record. It is not one of the retired model facades.
Adding its explicit import repairs the missing dependency; every declaration
and proof body in the cycle-map module remains byte-identical to baseline.
No rewrite, unifier, supplied law, compatibility facade or runtime cut is added.

A full-file probe with only the import added passes:
`20260926T041305Z-3fb3832a4c0244f0b37c67f4d235c9f6`.
The promoted owner, its laws and the direct
[homology-map reviewer](../emdash2/examples/homology_maps.lp) then pass under
the default 2 GiB/90-second guard:

| Target | Seconds | Receipt ID |
| --- | --- | --- |
| `emdash3_2_homology_cycle_maps.lp` | 2.410 | `20260926T041504Z-226c8156992b447cbb520dc72733fef0` |
| `emdash3_2_homology_cycle_map_laws.lp` | 1.449 | `20260926T041507Z-89cdd99046004d838c2dc283e63a1785` |
| `examples/homology_maps.lp` | 1.508 | `20260926T041509Z-1af447669ab34281a409b466bdab0f68` |

The registry resolves all 1,293 registered source/reviewer dependency graphs;
exact diff hygiene passes. Logs and immutable inputs remain in the existing
`emdash2/logs/check-runs/` and `emdash2/logs/check-inputs/` stores.
The broad suite resumes with exact matching earlier receipts; this correction
does not claim that the remaining profile migration or formal CI is complete.
