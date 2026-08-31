/** Functorial base change for modules over presented commutative algebras. */

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
    AlgebraPresentedAlgebraMap,
    algebraPresentedAlgebraEquals,
    algebraPresentedAlgebraMapApply,
    algebraPresentedAlgebraMapEquals,
    algebraPresentedAlgebraMapIdentity
} from './algebra_presented_algebra';
import { algebraQuotientText } from './algebra_quotient';
import {
    AlgebraPresentedAlgebraModule,
    AlgebraPresentedAlgebraModuleElement,
    AlgebraPresentedAlgebraModuleOptions,
    AlgebraPresentedAlgebraModuleVector,
    algebraPresentedAlgebraFreeModule,
    algebraPresentedAlgebraModule,
    algebraPresentedAlgebraModuleBasisVector,
    algebraPresentedAlgebraModuleElement,
    algebraPresentedAlgebraModuleVector
} from './algebra_presented_module';
import {
    AlgebraPresentedAlgebraModuleSemilinearMap,
    algebraPresentedAlgebraModuleLinearMap,
    algebraPresentedAlgebraModuleSemilinearMap,
    algebraPresentedAlgebraModuleSemilinearMapApply,
    algebraPresentedAlgebraModuleSemilinearMapCompose,
    algebraPresentedAlgebraModuleSemilinearMapEquals,
    algebraPresentedAlgebraModuleSemilinearMapIdentity
} from './algebra_presented_module_map';

export const ALGEBRA_PRESENTED_MODULE_BASE_CHANGE_PROFILE = Object.freeze({
    revision: 'emdash-presented-module-base-change-v1' as const,
    objectConstruction: 'transport-user-relations-and-rebuild-target-action' as const,
    canonicalMap: 'basis-to-basis-semilinear-map' as const,
    morphismScope: 'linear-maps-over-one-source-algebra' as const,
    comparison: 'computed-generator-image-equality' as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraPresentedModuleBaseChangeErrorCode =
    | 'INVALID_ENDPOINTS'
    | 'FOREIGN_MODULE'
    | 'NONLINEAR_SOURCE_MAP'
    | 'NATURALITY_COMPARISON_FAILED';

export class AlgebraPresentedModuleBaseChangeError extends Error {
    constructor(
        public readonly code: AlgebraPresentedModuleBaseChangeErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraPresentedModuleBaseChangeError';
    }
}

const fail = (
    code: AlgebraPresentedModuleBaseChangeErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraPresentedModuleBaseChangeError(code, path, message);
};

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

export interface AlgebraPresentedModuleBaseChange<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-presented-module-base-change';
    readonly scalarMap: AlgebraPresentedAlgebraMap<P, C, I>;
    readonly source: AlgebraPresentedAlgebraModule<P, C, I>;
    readonly transportedRelations:
        readonly AlgebraPresentedAlgebraModuleVector<P, C, I>[];
    readonly target: AlgebraPresentedAlgebraModule<P, C, I>;
    readonly unit: AlgebraPresentedAlgebraModuleSemilinearMap<P, C, I>;
}

export function algebraPresentedModuleBaseChange<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    scalarMap: AlgebraPresentedAlgebraMap<P, C, I>,
    source: AlgebraPresentedAlgebraModule<P, C, I>,
    options: AlgebraPresentedAlgebraModuleOptions = {}
): AlgebraPresentedModuleBaseChange<P, C, I> {
    if (!algebraPresentedAlgebraEquals(
        scalarMap.source,
        source.freeModule.algebra
    )) {
        return fail(
            'INVALID_ENDPOINTS',
            'moduleBaseChange.scalarMap',
            'Base-change map does not start at the module scalar algebra'
        );
    }
    const targetFreeModule = algebraPresentedAlgebraFreeModule(
        scalarMap.target,
        source.freeModule.rank,
        source.freeModule.termOrder
    );
    const transportedRelations = Object.freeze(source.relations.map(relation =>
        algebraPresentedAlgebraModuleVector(
            targetFreeModule,
            relation.components.map(component =>
                algebraPresentedAlgebraMapApply(scalarMap, component)
            )
        )
    ));
    const target = algebraPresentedAlgebraModule(
        targetFreeModule,
        transportedRelations,
        options
    );
    const unit = algebraPresentedAlgebraModuleSemilinearMap(
        source,
        target,
        scalarMap,
        Array.from({ length: source.freeModule.rank }, (_, position) =>
            algebraPresentedAlgebraModuleElement(
                target,
                algebraPresentedAlgebraModuleBasisVector(
                    target.freeModule,
                    position
                )
            )
        )
    );
    return Object.freeze({
        kind: 'algebra-presented-module-base-change',
        scalarMap,
        source,
        transportedRelations,
        target,
        unit
    });
}

export const algebraPresentedModuleBaseChangeElement = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    baseChange: AlgebraPresentedModuleBaseChange<P, C, I>,
    element: AlgebraPresentedAlgebraModuleElement<P, C, I>
): AlgebraPresentedAlgebraModuleElement<P, C, I> =>
    algebraPresentedAlgebraModuleSemilinearMapApply(baseChange.unit, element);

export interface AlgebraPresentedModuleMapBaseChange<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-presented-module-map-base-change';
    readonly scalarMap: AlgebraPresentedAlgebraMap<P, C, I>;
    readonly sourceMap: AlgebraPresentedAlgebraModuleSemilinearMap<P, C, I>;
    readonly sourceBaseChange: AlgebraPresentedModuleBaseChange<P, C, I>;
    readonly targetBaseChange: AlgebraPresentedModuleBaseChange<P, C, I>;
    readonly map: AlgebraPresentedAlgebraModuleSemilinearMap<P, C, I>;
    readonly mapAfterUnit: AlgebraPresentedAlgebraModuleSemilinearMap<P, C, I>;
    readonly unitAfterMap: AlgebraPresentedAlgebraModuleSemilinearMap<P, C, I>;
    readonly naturalityHolds: true;
}

export function algebraPresentedModuleBaseChangeMap<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    scalarMap: AlgebraPresentedAlgebraMap<P, C, I>,
    map: AlgebraPresentedAlgebraModuleSemilinearMap<P, C, I>,
    options: AlgebraPresentedAlgebraModuleOptions = {}
): AlgebraPresentedModuleMapBaseChange<P, C, I> {
    const sourceAlgebra = map.source.freeModule.algebra;
    const targetAlgebra = map.target.freeModule.algebra;
    if (!algebraPresentedAlgebraEquals(sourceAlgebra, targetAlgebra) ||
        !algebraPresentedAlgebraMapEquals(
            map.scalarMap,
            algebraPresentedAlgebraMapIdentity(sourceAlgebra)
        )) {
        return fail(
            'NONLINEAR_SOURCE_MAP',
            'moduleMapBaseChange.map',
            'Morphism base change currently requires one ordinary linear map'
        );
    }
    if (!algebraPresentedAlgebraEquals(scalarMap.source, sourceAlgebra)) {
        return fail(
            'INVALID_ENDPOINTS',
            'moduleMapBaseChange.scalarMap',
            'Base-change scalar map has a foreign source algebra'
        );
    }
    const sourceBaseChange = algebraPresentedModuleBaseChange(
        scalarMap,
        map.source,
        options
    );
    const targetBaseChange = algebraPresentedModuleBaseChange(
        scalarMap,
        map.target,
        options
    );
    const changedMap = algebraPresentedAlgebraModuleLinearMap(
        sourceBaseChange.target,
        targetBaseChange.target,
        map.generatorImages.map(image =>
            algebraPresentedModuleBaseChangeElement(targetBaseChange, image)
        )
    );
    const mapAfterUnit = algebraPresentedAlgebraModuleSemilinearMapCompose(
        changedMap,
        sourceBaseChange.unit
    );
    const unitAfterMap = algebraPresentedAlgebraModuleSemilinearMapCompose(
        targetBaseChange.unit,
        map
    );
    if (!algebraPresentedAlgebraModuleSemilinearMapEquals(
        mapAfterUnit,
        unitAfterMap
    )) {
        return fail(
            'NATURALITY_COMPARISON_FAILED',
            'moduleMapBaseChange.naturality',
            'Computed base-change morphism does not satisfy its canonical square'
        );
    }
    return Object.freeze({
        kind: 'algebra-presented-module-map-base-change',
        scalarMap,
        sourceMap: map,
        sourceBaseChange,
        targetBaseChange,
        map: changedMap,
        mapAfterUnit,
        unitAfterMap,
        naturalityHolds: true
    });
}

export const algebraPresentedModuleBaseChangeIdentityHolds = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(baseChange: AlgebraPresentedModuleBaseChange<P, C, I>): boolean =>
    algebraPresentedAlgebraMapEquals(
        baseChange.scalarMap,
        algebraPresentedAlgebraMapIdentity(baseChange.source.freeModule.algebra)
    ) &&
    sameAlgebraParent(baseChange.source, baseChange.target) &&
    algebraPresentedAlgebraModuleSemilinearMapEquals(
        baseChange.unit,
        algebraPresentedAlgebraModuleSemilinearMapIdentity(baseChange.source)
    );

export function algebraPresentedModuleBaseChangeSchema<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    scalarMap: AlgebraPresentedAlgebraMap<P, C, I>,
    source: AlgebraPresentedAlgebraModule<P, C, I>
): AlgebraRuntimeSchema<AlgebraPresentedModuleBaseChange<P, C, I>> {
    return defineAlgebraRuntimeSchema({
        id: `algebra.presented-module-base-change/${source.identity.id}/` +
            `${scalarMap.target.quotient.identity.id}`,
        revision: ALGEBRA_PRESENTED_MODULE_BASE_CHANGE_PROFILE.revision,
        normalize(value: unknown, path: string) {
            if (
                !record(value) ||
                value.kind !== 'algebra-presented-module-base-change' ||
                !record(value.source) ||
                !sameAlgebraParent(value.source as unknown as AlgebraParent, source) ||
                !record(value.scalarMap) ||
                !algebraPresentedAlgebraMapEquals(
                    value.scalarMap as unknown as AlgebraPresentedAlgebraMap<P, C, I>,
                    scalarMap
                )
            ) throw new Error(`presented module base change expected at ${path}`);
            return algebraPresentedModuleBaseChange(scalarMap, source);
        }
    });
}

export const serializeAlgebraPresentedModuleBaseChange = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(baseChange: AlgebraPresentedModuleBaseChange<P, C, I>): string =>
    `${JSON.stringify({
        revision: ALGEBRA_PRESENTED_MODULE_BASE_CHANGE_PROFILE.revision,
        kind: baseChange.kind,
        source: baseChange.source.identity,
        scalarSource: baseChange.scalarMap.source.quotient.identity,
        scalarTarget: baseChange.scalarMap.target.quotient.identity,
        transportedRelations: baseChange.transportedRelations.map(relation =>
            relation.components.map(algebraQuotientText)
        ),
        target: baseChange.target.identity,
        unitGeneratorImages: baseChange.unit.generatorImages.map(image =>
            image.representative.components.map(algebraQuotientText)
        )
    })}\n`;
