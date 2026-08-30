/** Minimal strict computable categories and weighted derived operations. */

import {
    AlgebraRuntimeSchema
} from './algebra_engine';

export const ALGEBRA_CATEGORY_PROFILE = Object.freeze({
    revision: 'emdash-computable-category-v1' as const,
    operationRevision: 'emdash-category-operation-v1' as const,
    methodRevision: 'emdash-category-method-v1' as const,
    planRevision: 'emdash-category-operation-plan-v1' as const,
    semantics: 'strict-set-level-runtime-category' as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraCategoryErrorCode =
    | 'INVALID_CATEGORY'
    | 'INVALID_OPERATION'
    | 'INVALID_METHOD'
    | 'DUPLICATE_METHOD'
    | 'UNAVAILABLE_OPERATION'
    | 'DERIVATION_CYCLE'
    | 'FOREIGN_OPERATION'
    | 'SOURCE_RANGE_MISMATCH'
    | 'METHOD_FAILURE';

export class AlgebraCategoryError extends Error {
    constructor(
        public readonly code: AlgebraCategoryErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraCategoryError';
    }
}

const fail = (
    code: AlgebraCategoryErrorCode,
    path: string,
    message: string,
    underlying?: unknown
): never => {
    throw new AlgebraCategoryError(
        code,
        path,
        message,
        underlying instanceof Error ? underlying : undefined
    );
};

const SAFE_ID = /^[A-Za-z][A-Za-z0-9._/-]*$/u;
const SAFE_REVISION = /^[A-Za-z0-9][A-Za-z0-9._+-]*$/u;

export interface ComputableCategoryIdentity {
    readonly kind: 'computable-category';
    readonly id: string;
    readonly revision: string;
}

export interface CategoryOperation<I, O> {
    readonly profileRevision:
        typeof ALGEBRA_CATEGORY_PROFILE.operationRevision;
    readonly id: string;
    readonly revision: string;
    readonly input: AlgebraRuntimeSchema<I>;
    readonly output: AlgebraRuntimeSchema<O>;
}

export const defineCategoryOperation = <I, O>(input: {
    readonly id: string;
    readonly revision: string;
    readonly input: AlgebraRuntimeSchema<I>;
    readonly output: AlgebraRuntimeSchema<O>;
}): CategoryOperation<I, O> => {
    if (!SAFE_ID.test(input.id) || !SAFE_REVISION.test(input.revision)) {
        return fail(
            'INVALID_OPERATION',
            'operation',
            'Category operation requires stable identity'
        );
    }
    return Object.freeze({
        profileRevision: ALGEBRA_CATEGORY_PROFILE.operationRevision,
        ...input
    });
};

export interface CategoryMethodContext {
    call<I, O>(operation: CategoryOperation<I, O>, input: unknown): Promise<O>;
}

export interface CategoryMethod {
    readonly profileRevision: typeof ALGEBRA_CATEGORY_PROFILE.methodRevision;
    readonly id: string;
    readonly operation: CategoryOperation<unknown, unknown>;
    readonly kind: 'primitive' | 'derived';
    readonly weight: number;
    readonly prerequisites: readonly CategoryOperation<unknown, unknown>[];
    execute(input: unknown, context: CategoryMethodContext): unknown | Promise<unknown>;
}

export function defineCategoryMethod<I, O>(input: {
    readonly id: string;
    readonly operation: CategoryOperation<I, O>;
    readonly kind: 'primitive' | 'derived';
    readonly weight?: number;
    readonly prerequisites?: readonly CategoryOperation<unknown, unknown>[];
    readonly execute: (
        value: I,
        context: CategoryMethodContext
    ) => O | Promise<O>;
}): CategoryMethod {
    const weight = input.weight ?? 1;
    if (
        !SAFE_ID.test(input.id) ||
        !Number.isSafeInteger(weight) ||
        weight <= 0 ||
        typeof input.execute !== 'function'
    ) {
        return fail('INVALID_METHOD', 'method', 'Invalid category method');
    }
    return Object.freeze({
        profileRevision: ALGEBRA_CATEGORY_PROFILE.methodRevision,
        id: input.id,
        operation: input.operation as CategoryOperation<unknown, unknown>,
        kind: input.kind,
        weight,
        prerequisites: Object.freeze([...(input.prerequisites ?? [])]),
        execute: input.execute as (value: unknown, context: CategoryMethodContext) =>
            unknown | Promise<unknown>
    });
}

const operationKey = (operation: CategoryOperation<unknown, unknown>): string =>
    `${operation.id}\u0000${operation.revision}`;

export interface CategoryOperationPlan {
    readonly profileRevision: typeof ALGEBRA_CATEGORY_PROFILE.planRevision;
    readonly operation: CategoryOperation<unknown, unknown>;
    readonly method: CategoryMethod;
    readonly prerequisites: readonly CategoryOperationPlan[];
    readonly totalWeight: number;
}

export interface CategoryOperationRegistry {
    readonly methods: readonly CategoryMethod[];
}

export const createCategoryOperationRegistry = (
    methodInput: readonly CategoryMethod[]
): CategoryOperationRegistry => {
    const seen = new Set<string>();
    const methods = methodInput.map((method, index) => {
        if (method.profileRevision !== ALGEBRA_CATEGORY_PROFILE.methodRevision) {
            return fail('INVALID_METHOD', `methods[${index}]`, 'Stale method');
        }
        const key = `${operationKey(method.operation)}\u0000${method.id}`;
        if (seen.has(key)) {
            return fail(
                'DUPLICATE_METHOD',
                `methods[${index}]`,
                `Duplicate category method '${method.id}'`
            );
        }
        seen.add(key);
        return method;
    });
    return Object.freeze({ methods: Object.freeze(methods) });
};

export const planCategoryOperation = (
    registry: CategoryOperationRegistry,
    operation: CategoryOperation<unknown, unknown>
): CategoryOperationPlan => {
    const memo = new Map<string, CategoryOperationPlan>();
    const active = new Set<string>();
    const resolve = (
        target: CategoryOperation<unknown, unknown>
    ): CategoryOperationPlan => {
        const key = operationKey(target);
        const cached = memo.get(key);
        if (cached) return cached;
        if (active.has(key)) {
            return fail(
                'DERIVATION_CYCLE',
                `operation.${target.id}`,
                `Derived operation cycle at '${target.id}'`
            );
        }
        active.add(key);
        const candidates: CategoryOperationPlan[] = [];
        registry.methods
            .filter(method => operationKey(method.operation) === key)
            .forEach(method => {
                try {
                    const prerequisites = method.prerequisites.map(resolve);
                    candidates.push(Object.freeze({
                        profileRevision: ALGEBRA_CATEGORY_PROFILE.planRevision,
                        operation: target,
                        method,
                        prerequisites: Object.freeze(prerequisites),
                        totalWeight: method.weight + prerequisites.reduce(
                            (sum, plan) => sum + plan.totalWeight,
                            0
                        )
                    }));
                } catch (error: unknown) {
                    if (
                        error instanceof AlgebraCategoryError &&
                        error.code === 'UNAVAILABLE_OPERATION'
                    ) return;
                    throw error;
                }
            });
        active.delete(key);
        candidates.sort((left, right) =>
            left.totalWeight - right.totalWeight ||
            (left.method.id < right.method.id ? -1 : 1)
        );
        const selected = candidates[0];
        if (!selected) {
            return fail(
                'UNAVAILABLE_OPERATION',
                `operation.${target.id}`,
                `No computable method for '${target.id}'`
            );
        }
        memo.set(key, selected);
        return selected;
    };
    return resolve(operation);
};

export interface ComputableCategory<ObjectValue, MorphismValue> {
    readonly profileRevision: typeof ALGEBRA_CATEGORY_PROFILE.revision;
    readonly identity: ComputableCategoryIdentity;
    readonly objectSchema: AlgebraRuntimeSchema<ObjectValue>;
    readonly morphismSchema: AlgebraRuntimeSchema<MorphismValue>;
    readonly operations: CategoryOperationRegistry;
    source(morphism: MorphismValue): ObjectValue;
    target(morphism: MorphismValue): ObjectValue;
    identityMorphism(object: ObjectValue): MorphismValue;
    compose(after: MorphismValue, before: MorphismValue): MorphismValue;
    equalObjects(left: ObjectValue, right: ObjectValue): boolean;
    equalMorphisms(left: MorphismValue, right: MorphismValue): boolean;
}

export const defineComputableCategory = <O, M>(input: Omit<
    ComputableCategory<O, M>,
    'profileRevision' | 'identity'
> & {
    readonly id: string;
    readonly revision: string;
}): ComputableCategory<O, M> => {
    if (!SAFE_ID.test(input.id) || !SAFE_REVISION.test(input.revision)) {
        return fail('INVALID_CATEGORY', 'category.identity', 'Invalid category ID');
    }
    return Object.freeze({
        profileRevision: ALGEBRA_CATEGORY_PROFILE.revision,
        identity: Object.freeze({
            kind: 'computable-category',
            id: input.id,
            revision: input.revision
        }),
        objectSchema: input.objectSchema,
        morphismSchema: input.morphismSchema,
        operations: input.operations,
        source: input.source,
        target: input.target,
        identityMorphism: input.identityMorphism,
        compose: input.compose,
        equalObjects: input.equalObjects,
        equalMorphisms: input.equalMorphisms
    });
};

export async function executeCategoryOperation<I, O>(
    category: ComputableCategory<unknown, unknown>,
    operation: CategoryOperation<I, O>,
    input: unknown
): Promise<{ readonly plan: CategoryOperationPlan; readonly value: O }> {
    const rootPlan = planCategoryOperation(
        category.operations,
        operation as CategoryOperation<unknown, unknown>
    );
    const execute = async (
        target: CategoryOperation<unknown, unknown>,
        value: unknown
    ): Promise<unknown> => {
        const plan = planCategoryOperation(category.operations, target);
        const normalized = target.input.normalize(value, `operation.${target.id}.input`);
        const context: CategoryMethodContext = {
            call: (nested, nestedInput) => execute(
                nested as CategoryOperation<unknown, unknown>,
                nestedInput
            ) as Promise<never>
        };
        try {
            const result = await plan.method.execute(normalized, context);
            return target.output.normalize(result, `operation.${target.id}.output`);
        } catch (error: unknown) {
            if (error instanceof AlgebraCategoryError) throw error;
            return fail(
                'METHOD_FAILURE',
                `operation.${target.id}`,
                `Category method '${plan.method.id}' failed`,
                error
            );
        }
    };
    return Object.freeze({
        plan: rootPlan,
        value: await execute(operation as CategoryOperation<unknown, unknown>, input) as O
    });
}
