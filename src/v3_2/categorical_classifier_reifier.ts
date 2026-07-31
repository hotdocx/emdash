/**
 * Bounded runtime-backed category-object classifier reification.
 *
 * This is an elaboration view only. It never rewrites the term being
 * classified, never invokes proof-time unification, and never inserts a
 * coercion. The ordinary generic checker remains responsible for validating
 * the unchanged term against the returned rich Core type.
 */

import {
    KernelExpression,
    Provenance,
    SourceSpan
} from './kernel';
import {
    CoreLfCatalogRuntime,
    CoreLfComparisonTraceEntry,
    coreLfCombinedNormalize
} from './lf_conversion';
import {
    CoreLfDeclarationEnvironment
} from './lf_declarations';
import {
    CoreType,
    coreTypeForCategoryObject
} from './surface';

export const CORE_CATEGORICAL_CLASSIFIER_REIFIER_REVISION =
    'RECURSIVE-MIXED-REFLECT-1A' as const;

export interface CoreCategoricalClassifierFormerNames {
    readonly oppositeCategory: string;
    readonly displayedFunctorCategory: string;
    readonly displayedTransforCategory: string;
}

export type CoreCategoricalClassifierCanonicalHead =
    | 'displayed-functor'
    | 'displayed-transfor'
    | 'generic-rich'
    | 'plain-object';

interface CoreCategoricalClassifierReificationBase {
    readonly originalCategory: KernelExpression;
    readonly normalizedCategory: KernelExpression;
    readonly steps: number;
    readonly trace: readonly CoreLfComparisonTraceEntry[];
}

export interface CoreCategoricalClassifierReified
extends CoreCategoricalClassifierReificationBase {
    readonly status: 'reified';
    readonly canonicalHead: CoreCategoricalClassifierCanonicalHead;
    readonly type: CoreType;
}

export interface CoreCategoricalClassifierReificationStuck
extends CoreCategoricalClassifierReificationBase {
    readonly status: 'stuck';
    readonly reason: 'plicity-mismatch';
}

export interface CoreCategoricalClassifierReificationStepLimit
extends CoreCategoricalClassifierReificationBase {
    readonly status: 'step-limit-exceeded';
}

export type CoreCategoricalClassifierReificationResult =
    | CoreCategoricalClassifierReified
    | CoreCategoricalClassifierReificationStuck
    | CoreCategoricalClassifierReificationStepLimit;

export interface CoreCategoricalCategoryObjectReifier {
    readonly revision:
        typeof CORE_CATEGORICAL_CLASSIFIER_REIFIER_REVISION;
    readonly stepLimit: number;
    reify(
        category: KernelExpression,
        provenance: Provenance,
        detail: string
    ): CoreCategoricalClassifierReificationResult;
}

export interface CoreCategoricalCategoryObjectReifierOptions {
    readonly environment: CoreLfDeclarationEnvironment;
    readonly runtime: CoreLfCatalogRuntime;
    readonly formerNames: CoreCategoricalClassifierFormerNames;
    readonly stepLimit?: number;
}

const referenceCall = (
    expression: KernelExpression,
    name: string,
    arity: number
): readonly KernelExpression[] | undefined => {
    if (
        expression.tag !== 'call' ||
        expression.callee.tag !== 'reference' ||
        expression.callee.namespace !== 'free' ||
        expression.callee.name !== name ||
        expression.arguments.length !== arity
    ) {
        return undefined;
    }
    return expression.arguments.map(argument => argument.value);
};

const reifyCanonicalCategory = (
    category: KernelExpression,
    formerNames: CoreCategoricalClassifierFormerNames,
    span: SourceSpan,
    detail: string
): {
    readonly canonicalHead: CoreCategoricalClassifierCanonicalHead;
    readonly type: CoreType;
} => {
    const opposite = category.tag === 'application' &&
            category.owner === 'opposite-category' &&
            category.arguments.length === 1
        ? category.arguments.map(argument => argument.value)
        : referenceCall(
            category,
            formerNames.oppositeCategory,
            1
        );
    if (opposite !== undefined) {
        const underlying = reifyCanonicalCategory(
            opposite[0],
            formerNames,
            span,
            detail
        );
        if (
            underlying.type.tag === 'displayed-functor' ||
            underlying.type.tag === 'displayed-transfor'
        ) {
            return Object.freeze({
                canonicalHead: underlying.canonicalHead,
                type: Object.freeze({
                    ...underlying.type,
                    // Object classifiers of C and Op(C) agree. Retaining
                    // the inferred opposite category here lets final LF
                    // checking validate that exact active computation.
                    category
                })
            });
        }
    }

    const displayedFunctor = referenceCall(
        category,
        formerNames.displayedFunctorCategory,
        3
    );
    if (displayedFunctor !== undefined) {
        return Object.freeze({
            canonicalHead: 'displayed-functor' as const,
            type: Object.freeze({
                tag: 'displayed-functor' as const,
                category,
                baseCategory: displayedFunctor[0],
                sourceFamily: displayedFunctor[1],
                targetFamily: displayedFunctor[2]
            })
        });
    }

    const displayedTransfor = referenceCall(
        category,
        formerNames.displayedTransforCategory,
        5
    );
    if (displayedTransfor !== undefined) {
        return Object.freeze({
            canonicalHead: 'displayed-transfor' as const,
            type: Object.freeze({
                tag: 'displayed-transfor' as const,
                category,
                baseCategory: displayedTransfor[0],
                sourceFamily: displayedTransfor[1],
                targetFamily: displayedTransfor[2],
                sourceFunctor: displayedTransfor[3],
                targetFunctor: displayedTransfor[4]
            })
        });
    }

    const generic = coreTypeForCategoryObject(
        category,
        span,
        detail
    );
    return Object.freeze({
        canonicalHead:
            generic.tag === 'object'
                ? 'plain-object' as const
                : 'generic-rich' as const,
        type: generic
    });
};

export function createCoreCategoricalCategoryObjectReifier(
    options: CoreCategoricalCategoryObjectReifierOptions
): CoreCategoricalCategoryObjectReifier {
    const stepLimit = options.stepLimit ?? 512;
    if (!Number.isSafeInteger(stepLimit) || stepLimit < 0) {
        throw new RangeError(
            'Categorical classifier reifier step limit must be a ' +
            `nonnegative safe integer; received ${stepLimit}`
        );
    }
    const formerNames = Object.freeze({ ...options.formerNames });

    return Object.freeze({
        revision: CORE_CATEGORICAL_CLASSIFIER_REIFIER_REVISION,
        stepLimit,
        reify(
            category: KernelExpression,
            provenance: Provenance,
            detail: string
        ): CoreCategoricalClassifierReificationResult {
            // Stable backend-neutral category formers and already exposed
            // active rich heads need no normalization. In particular, an
            // iterated Hom category must not spend the bounded budget walking
            // increasingly large endpoint terms merely to rediscover its
            // unchanged outer classifier.
            const direct = reifyCanonicalCategory(
                category,
                formerNames,
                provenance.span,
                detail
            );
            if (direct.canonicalHead !== 'plain-object') {
                return Object.freeze({
                    status: 'reified' as const,
                    originalCategory: category,
                    normalizedCategory: category,
                    steps: 0,
                    trace: Object.freeze([]),
                    ...direct
                });
            }

            const normalized = coreLfCombinedNormalize(
                options.environment,
                category,
                stepLimit,
                undefined,
                options.runtime,
                expression =>
                    referenceCall(
                        expression,
                        formerNames.displayedFunctorCategory,
                        3
                    ) !== undefined ||
                    referenceCall(
                        expression,
                        formerNames.displayedTransforCategory,
                        5
                    ) !== undefined
            );
            const base = {
                originalCategory: category,
                normalizedCategory: normalized.expression,
                steps: normalized.steps,
                trace: normalized.trace
            };
            if (normalized.status === 'step-limit-exceeded') {
                return Object.freeze({
                    status: 'step-limit-exceeded' as const,
                    ...base
                });
            }
            if (normalized.status === 'stuck') {
                return Object.freeze({
                    status: 'stuck' as const,
                    reason: normalized.reason,
                    ...base
                });
            }
            const reified = reifyCanonicalCategory(
                normalized.expression,
                formerNames,
                provenance.span,
                detail
            );
            return Object.freeze({
                status: 'reified' as const,
                ...base,
                ...reified
            });
        }
    });
}
