/**
 * Curated browser-safe package entry for backend-neutral emdash Core.
 *
 * This is intentionally narrower than the contributor-only `index.ts`
 * barrel. In particular, it does not expose the feasibility-era categorical
 * surface/elaborator, filesystem or process adapters, CLIs, demos, proposals,
 * or Lambdapi execution.
 */

export * from './schema';
export * from './kernel';
export * from './core_serialization';
export * from './signature';
export * from './context';
export * from './structural';
export * from './context_dependencies';
export * from './session';
export * from './checker';
export * from './manifest';
export * from './runtime';
export * from './evaluator';
export * from './conversion';
