/** Category constructors, towers, opposite categories, and reinterpretations. */

import { defineAlgebraRuntimeSchema } from './algebra_engine';
import {
    ComputableCategory,
    createCategoryOperationRegistry,
    defineComputableCategory
} from './algebra_category';
import {
    DoctrineRegistry
} from './algebra_doctrine';

export const ALGEBRA_TOWER_PROFILE = Object.freeze({
    revision: 'emdash-category-tower-v1' as const,
    constructorRevision: 'emdash-category-constructor-v1' as const,
    reinterpretationRevision: 'emdash-category-reinterpretation-v1' as const,
    compiler: false as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraTowerErrorCode =
    | 'INVALID_CONSTRUCTOR'
    | 'DUPLICATE_LOWERING_RULE'
    | 'DOCTRINE_MISMATCH'
    | 'INVALID_TOWER'
    | 'FOREIGN_OPPOSITE_MORPHISM'
    | 'INVALID_REINTERPRETATION';

export class AlgebraTowerError extends Error {
    constructor(
        public readonly code: AlgebraTowerErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraTowerError';
    }
}

const fail = (code: AlgebraTowerErrorCode, path: string, message: string): never => {
    throw new AlgebraTowerError(code, path, message);
};

const SAFE_ID = /^[A-Za-z][A-Za-z0-9._/-]*$/u;

export interface ConstructorLoweringRule {
    readonly id: string;
    readonly kind:
        | 'box-unbox-cancellation'
        | 'operation-lowering'
        | 'dual-operation'
        | 'reinterpretation';
    readonly source: string;
    readonly target: string;
}

export interface CategoryConstructorDescriptor {
    readonly profileRevision:
        typeof ALGEBRA_TOWER_PROFILE.constructorRevision;
    readonly id: string;
    readonly inputDoctrineId: string;
    readonly outputDoctrineId: string;
    readonly introducedRoles: readonly string[];
    readonly objectLayer: string;
    readonly morphismLayer: string;
    readonly dualConstructorId: string;
    readonly loweringRules: readonly ConstructorLoweringRule[];
}

export const defineCategoryConstructorDescriptor = (input: Omit<
    CategoryConstructorDescriptor,
    'profileRevision'
>): CategoryConstructorDescriptor => {
    if (
        !SAFE_ID.test(input.id) ||
        !SAFE_ID.test(input.inputDoctrineId) ||
        !SAFE_ID.test(input.outputDoctrineId) ||
        !SAFE_ID.test(input.dualConstructorId)
    ) return fail('INVALID_CONSTRUCTOR', 'constructor', 'Invalid constructor IDs');
    const seen = new Set<string>();
    input.loweringRules.forEach((rule, index) => {
        if (!SAFE_ID.test(rule.id) || seen.has(rule.id)) {
            fail(
                seen.has(rule.id)
                    ? 'DUPLICATE_LOWERING_RULE'
                    : 'INVALID_CONSTRUCTOR',
                `constructor.loweringRules[${index}]`,
                'Invalid or duplicate lowering rule'
            );
        }
        seen.add(rule.id);
    });
    return Object.freeze({
        profileRevision: ALGEBRA_TOWER_PROFILE.constructorRevision,
        ...input,
        introducedRoles: Object.freeze([...input.introducedRoles]),
        loweringRules: Object.freeze(input.loweringRules.map(rule =>
            Object.freeze({ ...rule })
        ))
    });
};

export interface CategoricalTower {
    readonly profileRevision: typeof ALGEBRA_TOWER_PROFILE.revision;
    readonly id: string;
    readonly baseDoctrineId: string;
    readonly constructors: readonly CategoryConstructorDescriptor[];
    readonly outputDoctrineId: string;
    readonly introducedRoles: readonly string[];
    readonly loweringRules: readonly ConstructorLoweringRule[];
}

export const buildCategoricalTower = (
    id: string,
    registry: DoctrineRegistry,
    baseDoctrineId: string,
    constructors: readonly CategoryConstructorDescriptor[]
): CategoricalTower => {
    if (!SAFE_ID.test(id) || !registry.byId.has(baseDoctrineId)) {
        return fail('INVALID_TOWER', 'tower', 'Invalid tower identity or base');
    }
    let current = baseDoctrineId;
    const roles = new Set<string>();
    const rules: ConstructorLoweringRule[] = [];
    constructors.forEach((constructor, index) => {
        if (
            constructor.profileRevision !==
                ALGEBRA_TOWER_PROFILE.constructorRevision ||
            constructor.inputDoctrineId !== current ||
            !registry.byId.has(constructor.outputDoctrineId)
        ) {
            fail(
                'DOCTRINE_MISMATCH',
                `tower.constructors[${index}]`,
                `Constructor '${constructor.id}' does not accept '${current}'`
            );
        }
        constructor.introducedRoles.forEach(role => roles.add(role));
        rules.push(...constructor.loweringRules);
        current = constructor.outputDoctrineId;
    });
    return Object.freeze({
        profileRevision: ALGEBRA_TOWER_PROFILE.revision,
        id,
        baseDoctrineId,
        constructors: Object.freeze([...constructors]),
        outputDoctrineId: current,
        introducedRoles: Object.freeze([...roles].sort()),
        loweringRules: Object.freeze(rules)
    });
};

export const additiveClosureConstructor = (): CategoryConstructorDescriptor =>
    defineCategoryConstructorDescriptor({
        id: 'category-constructor.additive-closure',
        inputDoctrineId: 'preadditive-category',
        outputDoctrineId: 'additive-category',
        introducedRoles: ['zero-object', 'biproduct'],
        objectLayer: 'finite-list-of-underlying-objects',
        morphismLayer: 'matrix-of-underlying-morphisms',
        dualConstructorId: 'category-constructor.additive-closure',
        loweringRules: [{
            id: 'additive-closure.matrix-lowering',
            kind: 'operation-lowering',
            source: 'matrix-of-underlying-morphisms',
            target: 'algebra-matrix'
        }]
    });

export const freydConstructor = (): CategoryConstructorDescriptor =>
    defineCategoryConstructorDescriptor({
        id: 'category-constructor.freyd',
        inputDoctrineId: 'additive-category',
        outputDoctrineId: 'additive-category',
        introducedRoles: ['cokernel'],
        objectLayer: 'arrow-presentation',
        morphismLayer: 'commuting-square-modulo-factorization',
        dualConstructorId: 'category-constructor.cofreyd',
        loweringRules: [{
            id: 'freyd.presentation-lowering',
            kind: 'operation-lowering',
            source: 'arrow-presentation',
            target: 'algebra-presented-module'
        }]
    });

export const cofreydConstructor = (): CategoryConstructorDescriptor =>
    defineCategoryConstructorDescriptor({
        id: 'category-constructor.cofreyd',
        inputDoctrineId: 'additive-category',
        outputDoctrineId: 'additive-category',
        introducedRoles: ['kernel'],
        objectLayer: 'opposite-arrow-presentation',
        morphismLayer: 'opposite-commuting-square-modulo-factorization',
        dualConstructorId: 'category-constructor.freyd',
        loweringRules: [{
            id: 'cofreyd.presentation-lowering',
            kind: 'operation-lowering',
            source: 'opposite-arrow-presentation',
            target: 'algebra-presented-comodule'
        }]
    });

export const oppositeConstructorDescriptor = (
    registry: DoctrineRegistry,
    doctrineId: string
): CategoryConstructorDescriptor => {
    const doctrine = registry.byId.get(doctrineId);
    if (!doctrine) {
        return fail(
            'INVALID_CONSTRUCTOR',
            'opposite.doctrine',
            `Unknown doctrine '${doctrineId}'`
        );
    }
    return defineCategoryConstructorDescriptor({
        id: `category-constructor.opposite/${doctrineId}`,
        inputDoctrineId: doctrineId,
        outputDoctrineId: doctrine.dual.doctrineId,
        introducedRoles: [],
        objectLayer: 'same-objects',
        morphismLayer: 'reversed-underlying-morphisms',
        dualConstructorId: `category-constructor.opposite/${doctrine.dual.doctrineId}`,
        loweringRules: [{
            id: `opposite.${doctrineId}.dual-lowering`,
            kind: 'dual-operation',
            source: doctrineId,
            target: doctrine.dual.doctrineId
        }]
    });
};

export interface OppositeMorphism<M> {
    readonly kind: 'opposite-morphism';
    readonly underlying: M;
}

export function oppositeComputableCategory<O, M>(
    category: ComputableCategory<O, M>
): ComputableCategory<O, OppositeMorphism<M>> {
    const morphismSchema = defineAlgebraRuntimeSchema<OppositeMorphism<M>>({
        id: `algebra.category.opposite-morphism/${category.identity.id}`,
        revision: category.identity.revision,
        normalize(value: unknown, path: string) {
            if (
                typeof value !== 'object' || value === null ||
                (value as { kind?: unknown }).kind !== 'opposite-morphism'
            ) throw new Error(`opposite morphism expected at ${path}`);
            return Object.freeze({
                kind: 'opposite-morphism',
                underlying: category.morphismSchema.normalize(
                    (value as OppositeMorphism<M>).underlying,
                    `${path}.underlying`
                )
            });
        }
    });
    const wrap = (underlying: M): OppositeMorphism<M> => Object.freeze({
        kind: 'opposite-morphism',
        underlying
    });
    return defineComputableCategory({
        id: `algebra.category.opposite/${category.identity.id}`,
        revision: category.identity.revision,
        objectSchema: category.objectSchema,
        morphismSchema,
        operations: createCategoryOperationRegistry([]),
        source: morphism => category.target(morphism.underlying),
        target: morphism => category.source(morphism.underlying),
        identityMorphism: object => wrap(category.identityMorphism(object)),
        compose: (after, before) => wrap(category.compose(
            before.underlying,
            after.underlying
        )),
        equalObjects: category.equalObjects,
        equalMorphisms: (left, right) => category.equalMorphisms(
            left.underlying,
            right.underlying
        )
    });
}

export interface ComputationalReinterpretation<PublicObject, ModelObject> {
    readonly profileRevision:
        typeof ALGEBRA_TOWER_PROFILE.reinterpretationRevision;
    readonly id: string;
    readonly publicCategoryId: string;
    readonly modelingCategoryId: string;
    readonly loweringRules: readonly ConstructorLoweringRule[];
    toModel(value: PublicObject): ModelObject;
    fromModel(value: ModelObject): PublicObject;
}

export const defineComputationalReinterpretation = <PublicObject, ModelObject>(
    input: Omit<ComputationalReinterpretation<PublicObject, ModelObject>,
        'profileRevision'>
): ComputationalReinterpretation<PublicObject, ModelObject> => {
    if (
        !SAFE_ID.test(input.id) ||
        !SAFE_ID.test(input.publicCategoryId) ||
        !SAFE_ID.test(input.modelingCategoryId) ||
        typeof input.toModel !== 'function' ||
        typeof input.fromModel !== 'function'
    ) return fail('INVALID_REINTERPRETATION', 'reinterpretation', 'Invalid reinterpretation');
    return Object.freeze({
        profileRevision: ALGEBRA_TOWER_PROFILE.reinterpretationRevision,
        ...input,
        loweringRules: Object.freeze(input.loweringRules.map(rule =>
            Object.freeze({ ...rule })
        ))
    });
};
