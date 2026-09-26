/** Optional TypeScript authoring surface for the plugin's inert source contract. */
export * from './package_algebra';
export {
    ALGEBRA_GOAL_SOURCE_PROFILE, createAlgebraGoalSource, createAlgebraGoalExampleSource,
    normalizeAlgebraGoalSource, serializeAlgebraGoalSource
} from './algebra_goal_source';
export type { AlgebraGoalSource, AlgebraGoalTermSource, AlgebraGoalPolynomialSource } from './algebra_goal_source';
