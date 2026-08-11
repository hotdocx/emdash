/**
 * Isolated browser-safe package entry for reproducible proof-agent evaluation.
 *
 * The evaluator never invokes a provider. The corpus reference attempts are
 * freshly replayed baselines, not proof authority or model-performance data.
 * Node file/process adapters remain outside this entry.
 */

export * from './lf_proof_agent_benchmark';
export * from './lf_proof_agent_interchange';
export * from './lf_proof_agent_public_corpus';
