/** Relation-checked semilinear maps between presented-algebra modules. */

import {
    AlgebraElement,
    AlgebraParent,
    sameAlgebraParent
} from './algebra_parent';
import {
    AlgebraRuntimeSchema,
    defineAlgebraRuntimeSchema
} from './algebra_engine';
import {
    AlgebraPolynomialModuleVector
} from './algebra_polynomial_module';
import {
    AlgebraPresentedAlgebraMap,
    algebraPresentedAlgebraEquals,
    algebraPresentedAlgebraMapApply,
    algebraPresentedAlgebraMapApplyPolynomial,
    algebraPresentedAlgebraMapCompose,
    algebraPresentedAlgebraMapEquals,
    algebraPresentedAlgebraMapIdentity
} from './algebra_presented_algebra';
import {
    algebraQuotientText
} from './algebra_quotient';
import {
    AlgebraPresentedAlgebraModule,
    AlgebraPresentedAlgebraModuleElement,
    algebraPresentedAlgebraModuleBasisVector,
    algebraPresentedAlgebraModuleElement,
    algebraPresentedAlgebraModuleElementAdd,
    algebraPresentedAlgebraModuleElementEquals,
    algebraPresentedAlgebraModuleElementIsZero,
    algebraPresentedAlgebraModuleElementScale,
    algebraPresentedAlgebraModuleElementSchema,
    algebraPresentedAlgebraModuleElementZero
} from './algebra_presented_module';

export const ALGEBRA_PRESENTED_MODULE_MAP_PROFILE = Object.freeze({
    revision: 'emdash-presented-algebra-module-map-v1' as const,
    representation: 'ordered-generator-images-over-explicit-algebra-map' as const,
    validation: 'all-source-relations-reduce-to-target-zero' as const,
    ordinaryLinearSpecialization: 'identity-algebra-map' as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraPresentedModuleMapErrorCode =
    | 'INVALID_ENDPOINTS'
    | 'INVALID_GENERATOR_IMAGES'
    | 'FOREIGN_TARGET_ELEMENT'
    | 'SOURCE_RELATION_FAILED'
    | 'FOREIGN_SOURCE_ELEMENT'
    | 'NON_COMPOSABLE_MAPS';

export class AlgebraPresentedModuleMapError extends Error {
    constructor(
        public readonly code: AlgebraPresentedModuleMapErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraPresentedModuleMapError';
    }
}

const fail = (
    code: AlgebraPresentedModuleMapErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraPresentedModuleMapError(code, path, message);
};

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

export interface AlgebraPresentedModuleRelationImage<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly family: 'algebra-action' | 'module';
    readonly relation: AlgebraPolynomialModuleVector<P, C, I>;
    readonly image: AlgebraPresentedAlgebraModuleElement<P, C, I>;
}

export interface AlgebraPresentedAlgebraModuleSemilinearMap<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-presented-module-semilinear-map';
    readonly source: AlgebraPresentedAlgebraModule<P, C, I>;
    readonly target: AlgebraPresentedAlgebraModule<P, C, I>;
    readonly scalarMap: AlgebraPresentedAlgebraMap<P, C, I>;
    readonly generatorImages:
        readonly AlgebraPresentedAlgebraModuleElement<P, C, I>[];
    readonly algebraActionRelationImages:
        readonly AlgebraPresentedModuleRelationImage<P, C, I>[];
    readonly relationImages:
        readonly AlgebraPresentedModuleRelationImage<P, C, I>[];
}

const applyPolynomialVector = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    scalarMap: AlgebraPresentedAlgebraMap<P, C, I>,
    target: AlgebraPresentedAlgebraModule<P, C, I>,
    generatorImages: readonly AlgebraPresentedAlgebraModuleElement<P, C, I>[],
    vector: AlgebraPolynomialModuleVector<P, C, I>
): AlgebraPresentedAlgebraModuleElement<P, C, I> => {
    let result = algebraPresentedAlgebraModuleElementZero(target);
    vector.components.forEach((component, index) => {
        const scalar = algebraPresentedAlgebraMapApplyPolynomial(
            scalarMap,
            component
        );
        result = algebraPresentedAlgebraModuleElementAdd(
            result,
            algebraPresentedAlgebraModuleElementScale(
                scalar,
                generatorImages[index]
            )
        );
    });
    return result;
};

export function algebraPresentedAlgebraModuleSemilinearMap<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    source: AlgebraPresentedAlgebraModule<P, C, I>,
    target: AlgebraPresentedAlgebraModule<P, C, I>,
    scalarMap: AlgebraPresentedAlgebraMap<P, C, I>,
    imageInput: readonly AlgebraPresentedAlgebraModuleElement<P, C, I>[]
): AlgebraPresentedAlgebraModuleSemilinearMap<P, C, I> {
    if (
        !algebraPresentedAlgebraEquals(
            scalarMap.source,
            source.freeModule.algebra
        ) ||
        !algebraPresentedAlgebraEquals(
            scalarMap.target,
            target.freeModule.algebra
        )
    ) {
        return fail(
            'INVALID_ENDPOINTS',
            'presentedModuleMap.scalarMap',
            'Scalar map does not connect the source and target module algebras'
        );
    }
    if (!Array.isArray(imageInput) ||
        imageInput.length !== source.freeModule.rank) {
        return fail(
            'INVALID_GENERATOR_IMAGES',
            'presentedModuleMap.generatorImages',
            `Expected ${source.freeModule.rank} module-generator images`
        );
    }
    const targetSchema = algebraPresentedAlgebraModuleElementSchema(target);
    const generatorImages = Object.freeze(imageInput.map((image, index) => {
        try {
            return targetSchema.normalize(
                image,
                `presentedModuleMap.generatorImages[${index}]`
            );
        } catch {
            return fail(
                'FOREIGN_TARGET_ELEMENT',
                `presentedModuleMap.generatorImages[${index}]`,
                'Generator image belongs to a foreign target module'
            );
        }
    }));
    const validateRelations = (
        family: 'algebra-action' | 'module',
        relations: readonly AlgebraPolynomialModuleVector<P, C, I>[]
    ): readonly AlgebraPresentedModuleRelationImage<P, C, I>[] =>
        Object.freeze(relations.map((relation, index) => {
            const image = applyPolynomialVector(
                scalarMap,
                target,
                generatorImages,
                relation
            );
            if (!algebraPresentedAlgebraModuleElementIsZero(image)) {
                return fail(
                    'SOURCE_RELATION_FAILED',
                    `presentedModuleMap.${family}RelationImages[${index}]`,
                    'A source module relation does not vanish in the target'
                );
            }
            return Object.freeze({ family, relation, image });
        }));
    return Object.freeze({
        kind: 'algebra-presented-module-semilinear-map',
        source,
        target,
        scalarMap,
        generatorImages,
        algebraActionRelationImages: validateRelations(
            'algebra-action',
            source.algebraActionRelations
        ),
        relationImages: validateRelations('module', source.liftedRelations)
    });
}

export function algebraPresentedAlgebraModuleSemilinearMapApply<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    map: AlgebraPresentedAlgebraModuleSemilinearMap<P, C, I>,
    element: AlgebraPresentedAlgebraModuleElement<P, C, I>
): AlgebraPresentedAlgebraModuleElement<P, C, I> {
    if (!sameAlgebraParent(element.parent, map.source)) {
        return fail(
            'FOREIGN_SOURCE_ELEMENT',
            'presentedModuleMapApply.element',
            'Map application requires an element of the source module'
        );
    }
    return element.representative.components.reduce(
        (result, component, index) =>
            algebraPresentedAlgebraModuleElementAdd(
                result,
                algebraPresentedAlgebraModuleElementScale(
                    algebraPresentedAlgebraMapApply(map.scalarMap, component),
                    map.generatorImages[index]
                )
            ),
        algebraPresentedAlgebraModuleElementZero(map.target)
    );
}

export const algebraPresentedAlgebraModuleSemilinearMapIdentity = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(module: AlgebraPresentedAlgebraModule<P, C, I>):
    AlgebraPresentedAlgebraModuleSemilinearMap<P, C, I> =>
    algebraPresentedAlgebraModuleSemilinearMap(
        module,
        module,
        algebraPresentedAlgebraMapIdentity(module.freeModule.algebra),
        Array.from({ length: module.freeModule.rank }, (_, position) =>
            algebraPresentedAlgebraModuleElement(
                module,
                algebraPresentedAlgebraModuleBasisVector(
                    module.freeModule,
                    position
                )
            )
        )
    );

export function algebraPresentedAlgebraModuleLinearMap<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    source: AlgebraPresentedAlgebraModule<P, C, I>,
    target: AlgebraPresentedAlgebraModule<P, C, I>,
    generatorImages:
        readonly AlgebraPresentedAlgebraModuleElement<P, C, I>[]
): AlgebraPresentedAlgebraModuleSemilinearMap<P, C, I> {
    if (!algebraPresentedAlgebraEquals(
        source.freeModule.algebra,
        target.freeModule.algebra
    )) {
        return fail(
            'INVALID_ENDPOINTS',
            'presentedModuleLinearMap.target',
            'An ordinary linear map requires one presented scalar algebra'
        );
    }
    return algebraPresentedAlgebraModuleSemilinearMap(
        source,
        target,
        algebraPresentedAlgebraMapIdentity(source.freeModule.algebra),
        generatorImages
    );
}

export function algebraPresentedAlgebraModuleSemilinearMapCompose<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    after: AlgebraPresentedAlgebraModuleSemilinearMap<P, C, I>,
    before: AlgebraPresentedAlgebraModuleSemilinearMap<P, C, I>
): AlgebraPresentedAlgebraModuleSemilinearMap<P, C, I> {
    if (!sameAlgebraParent(before.target, after.source)) {
        return fail(
            'NON_COMPOSABLE_MAPS',
            'presentedModuleMapCompose',
            'Semilinear module maps are not composable'
        );
    }
    return algebraPresentedAlgebraModuleSemilinearMap(
        before.source,
        after.target,
        algebraPresentedAlgebraMapCompose(after.scalarMap, before.scalarMap),
        before.generatorImages.map(image =>
            algebraPresentedAlgebraModuleSemilinearMapApply(after, image)
        )
    );
}

export const algebraPresentedAlgebraModuleSemilinearMapEquals = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPresentedAlgebraModuleSemilinearMap<P, C, I>,
    right: AlgebraPresentedAlgebraModuleSemilinearMap<P, C, I>
): boolean => sameAlgebraParent(left.source, right.source) &&
    sameAlgebraParent(left.target, right.target) &&
    algebraPresentedAlgebraMapEquals(left.scalarMap, right.scalarMap) &&
    left.generatorImages.every((image, index) =>
        algebraPresentedAlgebraModuleElementEquals(
            image,
            right.generatorImages[index]
        )
    );

export const algebraPresentedAlgebraModuleSemilinearMapIsZero = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(map: AlgebraPresentedAlgebraModuleSemilinearMap<P, C, I>): boolean =>
    map.generatorImages.every(algebraPresentedAlgebraModuleElementIsZero);

export function algebraPresentedAlgebraModuleSemilinearMapSchema<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    source: AlgebraPresentedAlgebraModule<P, C, I>,
    target: AlgebraPresentedAlgebraModule<P, C, I>,
    scalarMap: AlgebraPresentedAlgebraMap<P, C, I>
): AlgebraRuntimeSchema<AlgebraPresentedAlgebraModuleSemilinearMap<P, C, I>> {
    const targetSchema = algebraPresentedAlgebraModuleElementSchema(target);
    return defineAlgebraRuntimeSchema({
        id: `algebra.presented-module-map/${source.identity.id}/` +
            `${target.identity.id}/${scalarMap.source.quotient.identity.id}/` +
            scalarMap.target.quotient.identity.id,
        revision: ALGEBRA_PRESENTED_MODULE_MAP_PROFILE.revision,
        normalize(value: unknown, path: string) {
            if (
                !record(value) ||
                value.kind !== 'algebra-presented-module-semilinear-map' ||
                !record(value.source) ||
                !sameAlgebraParent(value.source as unknown as AlgebraParent, source) ||
                !record(value.target) ||
                !sameAlgebraParent(value.target as unknown as AlgebraParent, target) ||
                !record(value.scalarMap) ||
                !algebraPresentedAlgebraMapEquals(
                    value.scalarMap as unknown as AlgebraPresentedAlgebraMap<P, C, I>,
                    scalarMap
                ) ||
                !Array.isArray(value.generatorImages)
            ) throw new Error(`presented semilinear map expected at ${path}`);
            return algebraPresentedAlgebraModuleSemilinearMap(
                source,
                target,
                scalarMap,
                value.generatorImages.map((image, index) =>
                    targetSchema.normalize(
                        image,
                        `${path}.generatorImages[${index}]`
                    )
                )
            );
        }
    });
}

export const serializeAlgebraPresentedAlgebraModuleSemilinearMap = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(map: AlgebraPresentedAlgebraModuleSemilinearMap<P, C, I>): string =>
    `${JSON.stringify({
        revision: ALGEBRA_PRESENTED_MODULE_MAP_PROFILE.revision,
        kind: map.kind,
        source: map.source.identity,
        target: map.target.identity,
        scalarMap: {
            source: map.scalarMap.source.quotient.identity,
            target: map.scalarMap.target.quotient.identity,
            generatorImages: map.scalarMap.generatorImages.map(algebraQuotientText)
        },
        generatorImages: map.generatorImages.map(image =>
            image.representative.components.map(algebraQuotientText)
        ),
        relationCounts: {
            algebraAction: map.algebraActionRelationImages.length,
            module: map.relationImages.length
        }
    })}\n`;
