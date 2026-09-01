/** Presented polynomial modules, free-module maps, and Schreyer resolutions. */

import {
    AlgebraElement,
    AlgebraParent,
    sameAlgebraParent
} from './algebra_parent';
import {
    AlgebraPolynomial,
    algebraPolynomialOne,
    algebraPolynomialZero
} from './algebra_polynomial';
import {
    AlgebraPolynomialFreeModule,
    AlgebraPolynomialModuleGroebnerBasis,
    AlgebraPolynomialModuleGroebnerOptions,
    AlgebraPolynomialModuleMembership,
    AlgebraPolynomialModuleSchreyerSyzygies,
    AlgebraPolynomialModuleVector,
    AlgebraPolynomialSubmodule,
    algebraPolynomialModuleAdd,
    algebraPolynomialModuleCombination,
    algebraPolynomialModuleEquals,
    algebraPolynomialModuleGroebnerBasis,
    algebraPolynomialModuleMembership,
    algebraPolynomialModuleSchreyerSyzygies,
    algebraPolynomialModuleSubtract,
    algebraPolynomialModuleVector,
    algebraPolynomialModuleZero,
    algebraPolynomialSchreyerModule,
    algebraPolynomialSubmodule
} from './algebra_polynomial_module';

export const ALGEBRA_POLYNOMIAL_PRESENTATION_PROFILE = Object.freeze({
    revision: 'emdash-algebra-polynomial-presentation-v1' as const,
    quotientNormalForm: 'module-groebner-remainder' as const,
    resolution: 'bounded-recursive-schreyer' as const,
    defaultMaximumLength: 4,
    maximumLength: 64,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraPolynomialPresentationErrorCode =
    | 'INVALID_MODULE_MAP'
    | 'NON_COMPOSABLE_MAPS'
    | 'CHAIN_CONDITION_FAILED'
    | 'INVALID_RESOLUTION_LIMIT';

export class AlgebraPolynomialPresentationError extends Error {
    constructor(
        public readonly code: AlgebraPolynomialPresentationErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraPolynomialPresentationError';
    }
}

const fail = (
    code: AlgebraPolynomialPresentationErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraPolynomialPresentationError(code, path, message);
};

export interface AlgebraPolynomialModuleMap<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-module-map';
    readonly source: AlgebraPolynomialFreeModule<P, C, I>;
    readonly target: AlgebraPolynomialFreeModule<P, C, I>;
    /** Image of each ordered source basis vector. */
    readonly columns: readonly AlgebraPolynomialModuleVector<P, C, I>[];
}

export function algebraPolynomialModuleMap<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    source: AlgebraPolynomialFreeModule<P, C, I>,
    target: AlgebraPolynomialFreeModule<P, C, I>,
    columnInput: readonly AlgebraPolynomialModuleVector<P, C, I>[]
): AlgebraPolynomialModuleMap<P, C, I> {
    if (!Array.isArray(columnInput) || columnInput.length !== source.rank) {
        return fail(
            'INVALID_MODULE_MAP',
            'polynomialModuleMap.columns',
            `Expected ${source.rank} module-map columns`
        );
    }
    const columns = columnInput.map((column, index) => {
        if (!sameAlgebraParent(column.parent, target)) {
            return fail(
                'INVALID_MODULE_MAP',
                `polynomialModuleMap.columns[${index}]`,
                'Module-map column belongs to a foreign target'
            );
        }
        return column;
    });
    return Object.freeze({
        kind: 'algebra-polynomial-module-map',
        source,
        target,
        columns: Object.freeze(columns)
    });
}

export function algebraPolynomialModuleMapApply<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    map: AlgebraPolynomialModuleMap<P, C, I>,
    vector: AlgebraPolynomialModuleVector<P, C, I>
): AlgebraPolynomialModuleVector<P, C, I> {
    if (!sameAlgebraParent(vector.parent, map.source)) {
        return fail(
            'INVALID_MODULE_MAP',
            'polynomialModuleMapApply.vector',
            'Map input belongs to a foreign source module'
        );
    }
    if (map.columns.length === 0) return algebraPolynomialModuleZero(map.target);
    return algebraPolynomialModuleCombination(map.columns, vector.components);
}

export const algebraPolynomialModuleMapIdentity = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(module: AlgebraPolynomialFreeModule<P, C, I>):
    AlgebraPolynomialModuleMap<P, C, I> => algebraPolynomialModuleMap(
        module,
        module,
        Array.from({ length: module.rank }, (_, index) =>
            algebraPolynomialModuleVector(
                module,
                Array.from({ length: module.rank }, (_, position) =>
                    position === index
                        ? algebraPolynomialOne(module.ring)
                        : algebraPolynomialZero(module.ring)
                )
            )
        )
    );

export const algebraPolynomialModuleMapZero = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    source: AlgebraPolynomialFreeModule<P, C, I>,
    target: AlgebraPolynomialFreeModule<P, C, I>
): AlgebraPolynomialModuleMap<P, C, I> => algebraPolynomialModuleMap(
    source,
    target,
    Array.from({ length: source.rank }, () =>
        algebraPolynomialModuleZero(target)
    )
);

export function algebraPolynomialModuleMapAdd<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomialModuleMap<P, C, I>,
    right: AlgebraPolynomialModuleMap<P, C, I>
): AlgebraPolynomialModuleMap<P, C, I> {
    if (
        !sameAlgebraParent(left.source, right.source) ||
        !sameAlgebraParent(left.target, right.target)
    ) {
        return fail(
            'INVALID_MODULE_MAP',
            'polynomialModuleMapAdd',
            'Map addition requires identical free-module endpoints'
        );
    }
    return algebraPolynomialModuleMap(
        left.source,
        left.target,
        left.columns.map((column, index) =>
            algebraPolynomialModuleAdd(column, right.columns[index])
        )
    );
}

export const algebraPolynomialModuleMapNegate = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(map: AlgebraPolynomialModuleMap<P, C, I>):
    AlgebraPolynomialModuleMap<P, C, I> => algebraPolynomialModuleMap(
    map.source,
    map.target,
    map.columns.map(column => algebraPolynomialModuleSubtract(
        algebraPolynomialModuleZero(map.target),
        column
    ))
);

export function algebraPolynomialModuleMapCompose<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    after: AlgebraPolynomialModuleMap<P, C, I>,
    before: AlgebraPolynomialModuleMap<P, C, I>
): AlgebraPolynomialModuleMap<P, C, I> {
    if (!sameAlgebraParent(before.target, after.source)) {
        return fail(
            'NON_COMPOSABLE_MAPS',
            'polynomialModuleMapCompose',
            'Polynomial-module maps are not composable'
        );
    }
    return algebraPolynomialModuleMap(
        before.source,
        after.target,
        before.columns.map(column => algebraPolynomialModuleMapApply(
            after,
            column
        ))
    );
}

export const algebraPolynomialModuleMapIsZero = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(map: AlgebraPolynomialModuleMap<P, C, I>): boolean => map.columns.every(
    column => algebraPolynomialModuleEquals(
        column,
        algebraPolynomialModuleZero(map.target)
    )
);

export interface AlgebraPresentedPolynomialModule<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-presented-polynomial-module';
    readonly ambient: AlgebraPolynomialFreeModule<P, C, I>;
    readonly relations: AlgebraPolynomialSubmodule<P, C, I>;
    readonly relationBasis: AlgebraPolynomialModuleGroebnerBasis<P, C, I>;
}

export function algebraPresentedPolynomialModule<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    relations: AlgebraPolynomialSubmodule<P, C, I>,
    options: AlgebraPolynomialModuleGroebnerOptions = {}
): AlgebraPresentedPolynomialModule<P, C, I> {
    return Object.freeze({
        kind: 'algebra-presented-polynomial-module',
        ambient: relations.module,
        relations,
        relationBasis: algebraPolynomialModuleGroebnerBasis(relations, options)
    });
}

export function algebraPresentedPolynomialModuleNormalForm<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    module: AlgebraPresentedPolynomialModule<P, C, I>,
    vector: AlgebraPolynomialModuleVector<P, C, I>
): AlgebraPolynomialModuleMembership<P, C, I> {
    return algebraPolynomialModuleMembership(vector, module.relationBasis);
}

export interface AlgebraPolynomialSchreyerResolutionStage<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly degree: number;
    readonly basis: AlgebraPolynomialModuleGroebnerBasis<P, C, I>;
    readonly differential: AlgebraPolynomialModuleMap<P, C, I>;
    readonly syzygies: AlgebraPolynomialModuleSchreyerSyzygies<P, C, I>;
}

export interface AlgebraPolynomialSchreyerResolution<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-schreyer-resolution';
    readonly module: AlgebraPresentedPolynomialModule<P, C, I>;
    readonly freeModules: readonly AlgebraPolynomialFreeModule<P, C, I>[];
    readonly differentials: readonly AlgebraPolynomialModuleMap<P, C, I>[];
    readonly stages: readonly AlgebraPolynomialSchreyerResolutionStage<P, C, I>[];
    readonly length: number;
    readonly complete: boolean;
    readonly maximumLength: number;
}

export function algebraPolynomialSchreyerResolution<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    module: AlgebraPresentedPolynomialModule<P, C, I>,
    maximumLengthInput: number =
        ALGEBRA_POLYNOMIAL_PRESENTATION_PROFILE.defaultMaximumLength,
    options: AlgebraPolynomialModuleGroebnerOptions = {}
): AlgebraPolynomialSchreyerResolution<P, C, I> {
    if (
        !Number.isSafeInteger(maximumLengthInput) ||
        maximumLengthInput < 0 ||
        maximumLengthInput > ALGEBRA_POLYNOMIAL_PRESENTATION_PROFILE.maximumLength
    ) {
        return fail(
            'INVALID_RESOLUTION_LIMIT',
            'schreyerResolution.maximumLength',
            'Resolution length must be a bounded nonnegative safe integer'
        );
    }
    const freeModules: AlgebraPolynomialFreeModule<P, C, I>[] = [module.ambient];
    const differentials: AlgebraPolynomialModuleMap<P, C, I>[] = [];
    const stages: AlgebraPolynomialSchreyerResolutionStage<P, C, I>[] = [];
    let currentBasis = module.relationBasis;
    let complete = currentBasis.basis.length === 0;
    while (!complete && differentials.length < maximumLengthInput) {
        const target = freeModules[freeModules.length - 1];
        const source = algebraPolynomialSchreyerModule(
            target,
            currentBasis.basis
        );
        const differential = algebraPolynomialModuleMap(
            source,
            target,
            currentBasis.basis
        );
        if (differentials.length > 0) {
            const composite = algebraPolynomialModuleMapCompose(
                differentials[differentials.length - 1],
                differential
            );
            if (!algebraPolynomialModuleMapIsZero(composite)) {
                return fail(
                    'CHAIN_CONDITION_FAILED',
                    `schreyerResolution.differentials[${differentials.length}]`,
                    'Consecutive Schreyer differentials do not compose to zero'
                );
            }
        }
        freeModules.push(source);
        differentials.push(differential);
        const syzygies = algebraPolynomialModuleSchreyerSyzygies(currentBasis);
        stages.push(Object.freeze({
            degree: differentials.length,
            basis: currentBasis,
            differential,
            syzygies
        }));
        if (syzygies.generators.length === 0) {
            complete = true;
            break;
        }
        currentBasis = algebraPolynomialModuleGroebnerBasis(
            algebraPolynomialSubmodule(source, syzygies.generators),
            options
        );
    }
    return Object.freeze({
        kind: 'algebra-polynomial-schreyer-resolution',
        module,
        freeModules: Object.freeze(freeModules),
        differentials: Object.freeze(differentials),
        stages: Object.freeze(stages),
        length: differentials.length,
        complete,
        maximumLength: maximumLengthInput
    });
}
