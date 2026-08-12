/**
 * Curated browser-safe workspace entry for AI-authored emdash developments.
 *
 * These APIs keep proof plans and workspace state explicit and serializable.
 * Remote acquisition, filesystem persistence, hashing, and CLIs remain outer
 * adapters and are not part of this package entry.
 */

export * from './package_authoring';
export * from './proof';
export * from './proof_checker';
export * from './proof_simplifier';
export * from './proof_goal_graph';
export * from './proof_plan';
export * from './proof_plan_patch';
export * from './proof_obvious';
export * from './proof_template';
export * from './proof_document';
export * from './lf_workspace';
export * from './lf_premise_index';
export * from './lf_workspace_proof';
export * from './lf_proof_development';
export * from './lf_proof_development_source';
export * from './lf_development_diff';
export * from './lf_proof_maintenance';
export * from './lf_fragment_workspace';
export * from './lf_fragment_module_workspace';
export * from './lf_fragment_workspace_proof';
export * from './lf_fragment_proof_development';
export * from './research_document';
export * from './research_goal_graph';
export * from './research_goal_view';
