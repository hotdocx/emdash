/** Finitely presented modules over finitely presented commutative algebras. */

import {
    AlgebraElement,
    AlgebraParent,
    defineAlgebraParent,
    sameAlgebraParent
} from './algebra_parent';
import {
    AlgebraRuntimeSchema,
    defineAlgebraRuntimeSchema
} from './algebra_engine';
import {
    AlgebraPolynomial,
    algebraPolynomialText,
    algebraPolynomialZero
} from './algebra_polynomial';
import {
    AlgebraPolynomialModuleBaseTermOrder,
    AlgebraPolynomialFreeModule,
    AlgebraPolynomialModuleGroebnerOptions,
    AlgebraPolynomialModuleMembership,
    AlgebraPolynomialModuleVector,
    AlgebraPolynomialSubmodule,
    AlgebraReducedPolynomialModuleGroebnerBasis,
    algebraPolynomialFreeModule,
    algebraPolynomialModuleGroebnerBasis,
    algebraPolynomialModuleMembership,
    algebraPolynomialModuleVector,
    algebraPolynomialSubmodule,
    algebraReducedPolynomialModuleGroebnerBasis
} from './algebra_polynomial_module';
import {
    AlgebraQuotientElement,
    algebraQuotientAdd,
    algebraQuotientElement,
    algebraQuotientElementSchema,
    algebraQuotientEquals,
    algebraQuotientMultiply,
    algebraQuotientNegate,
    algebraQuotientOne,
    algebraQuotientText,
    algebraQuotientZero
} from './algebra_quotient';
import {
    AlgebraPresentedAlgebra
} from './algebra_presented_algebra';

export const ALGEBRA_PRESENTED_MODULE_PROFILE = Object.freeze({
    revision: 'emdash-presented-algebra-module-v1' as const,
    representation: 'polynomial-module-modulo-algebra-and-module-relations' as const,
    normalForm: 'reduced-module-groebner-remainder' as const,
    defaultTermOrder: 'term-over-position' as const,
    identityOwner: 'algebra-rank-order-and-reduced-relation-basis' as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraPresentedModuleErrorCode =
    | 'INVALID_FREE_MODULE'
    | 'INVALID_VECTOR'
    | 'INVALID_BASIS_POSITION'
    | 'FOREIGN_ALGEBRA'
    | 'FOREIGN_FREE_MODULE'
    | 'FOREIGN_PRESENTED_MODULE';

export class AlgebraPresentedModuleError extends Error {
    constructor(
        public readonly code: AlgebraPresentedModuleErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraPresentedModuleError';
    }
}

const fail = (
    code: AlgebraPresentedModuleErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraPresentedModuleError(code, path, message);
};

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

const hexText = (value: string): string => Array.from(new TextEncoder().encode(value))
    .map(byte => byte.toString(16).padStart(2, '0'))
    .join('');

export interface AlgebraPresentedAlgebraFreeModule<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> extends AlgebraParent<'presented-algebra-free-module'> {
    readonly algebra: AlgebraPresentedAlgebra<P, C, I>;
    readonly rank: number;
    readonly termOrder: AlgebraPolynomialModuleBaseTermOrder;
    readonly polynomialModule: AlgebraPolynomialFreeModule<P, C, I>;
}

export function algebraPresentedAlgebraFreeModule<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    algebra: AlgebraPresentedAlgebra<P, C, I>,
    rank: number,
    termOrder: AlgebraPolynomialModuleBaseTermOrder =
        ALGEBRA_PRESENTED_MODULE_PROFILE.defaultTermOrder
): AlgebraPresentedAlgebraFreeModule<P, C, I> {
    const polynomialModule = algebraPolynomialFreeModule(
        algebra.quotient.polynomialRing,
        rank,
        termOrder
    );
    const parent = defineAlgebraParent(
        'presented-algebra-free-module',
        `algebra.presented-free-module/${algebra.quotient.identity.id}/` +
            `${polynomialModule.rank}/${polynomialModule.termOrder}`,
        `v1.${algebra.quotient.identity.revision}`
    );
    return Object.freeze({
        ...parent,
        algebra,
        rank: polynomialModule.rank,
        termOrder,
        polynomialModule
    });
}

export interface AlgebraPresentedAlgebraModuleVector<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> extends AlgebraElement<AlgebraPresentedAlgebraFreeModule<P, C, I>> {
    readonly kind: 'algebra-presented-algebra-module-vector';
    readonly components: readonly AlgebraQuotientElement<P, C, I>[];
}

export function algebraPresentedAlgebraModuleVector<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    module: AlgebraPresentedAlgebraFreeModule<P, C, I>,
    componentInput: readonly AlgebraQuotientElement<P, C, I>[]
): AlgebraPresentedAlgebraModuleVector<P, C, I> {
    if (!Array.isArray(componentInput) || componentInput.length !== module.rank) {
        return fail(
            'INVALID_VECTOR',
            'presentedModuleVector.components',
            `Expected exactly ${module.rank} quotient components`
        );
    }
    const schema = algebraQuotientElementSchema(module.algebra.quotient);
    const components = componentInput.map((component, index) => {
        try {
            return schema.normalize(
                component,
                `presentedModuleVector.components[${index}]`
            );
        } catch {
            return fail(
                'FOREIGN_ALGEBRA',
                `presentedModuleVector.components[${index}]`,
                'Module-vector component belongs to a foreign algebra'
            );
        }
    });
    return Object.freeze({
        kind: 'algebra-presented-algebra-module-vector',
        parent: module,
        components: Object.freeze(components)
    });
}

export const algebraPresentedAlgebraModuleVectorZero = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(module: AlgebraPresentedAlgebraFreeModule<P, C, I>):
    AlgebraPresentedAlgebraModuleVector<P, C, I> =>
    algebraPresentedAlgebraModuleVector(
        module,
        Array.from({ length: module.rank }, () =>
            algebraQuotientZero(module.algebra.quotient)
        )
    );

export function algebraPresentedAlgebraModuleBasisVector<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    module: AlgebraPresentedAlgebraFreeModule<P, C, I>,
    position: number
): AlgebraPresentedAlgebraModuleVector<P, C, I> {
    if (!Number.isSafeInteger(position) || position < 0 || position >= module.rank) {
        return fail(
            'INVALID_BASIS_POSITION',
            'presentedModuleBasisVector.position',
            'Basis position is outside the selected free module'
        );
    }
    return algebraPresentedAlgebraModuleVector(
        module,
        Array.from({ length: module.rank }, (_, index) => index === position
            ? algebraQuotientOne(module.algebra.quotient)
            : algebraQuotientZero(module.algebra.quotient))
    );
}

const sameFreeModule = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPresentedAlgebraModuleVector<P, C, I>,
    right: AlgebraPresentedAlgebraModuleVector<P, C, I>,
    path: string
): AlgebraPresentedAlgebraFreeModule<P, C, I> => {
    if (!sameAlgebraParent(left.parent, right.parent)) {
        return fail(
            'FOREIGN_FREE_MODULE',
            path,
            'Module vectors belong to different free modules'
        );
    }
    return left.parent;
};

export const algebraPresentedAlgebraModuleVectorAdd = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPresentedAlgebraModuleVector<P, C, I>,
    right: AlgebraPresentedAlgebraModuleVector<P, C, I>
): AlgebraPresentedAlgebraModuleVector<P, C, I> => {
    const module = sameFreeModule(left, right, 'presentedModuleVectorAdd');
    return algebraPresentedAlgebraModuleVector(
        module,
        left.components.map((component, index) =>
            algebraQuotientAdd(component, right.components[index])
        )
    );
};

export const algebraPresentedAlgebraModuleVectorNegate = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(vector: AlgebraPresentedAlgebraModuleVector<P, C, I>):
    AlgebraPresentedAlgebraModuleVector<P, C, I> =>
    algebraPresentedAlgebraModuleVector(
        vector.parent,
        vector.components.map(algebraQuotientNegate)
    );

export function algebraPresentedAlgebraModuleVectorScale<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    scalar: AlgebraQuotientElement<P, C, I>,
    vector: AlgebraPresentedAlgebraModuleVector<P, C, I>
): AlgebraPresentedAlgebraModuleVector<P, C, I> {
    if (!sameAlgebraParent(scalar.parent, vector.parent.algebra.quotient)) {
        return fail(
            'FOREIGN_ALGEBRA',
            'presentedModuleVectorScale.scalar',
            'Scalar belongs to a foreign presented algebra'
        );
    }
    return algebraPresentedAlgebraModuleVector(
        vector.parent,
        vector.components.map(component =>
            algebraQuotientMultiply(scalar, component)
        )
    );
}

export const algebraPresentedAlgebraModuleVectorEquals = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPresentedAlgebraModuleVector<P, C, I>,
    right: AlgebraPresentedAlgebraModuleVector<P, C, I>
): boolean => sameAlgebraParent(left.parent, right.parent) &&
    left.components.every((component, index) =>
        algebraQuotientEquals(component, right.components[index])
    );

export const algebraPresentedAlgebraModuleVectorLift = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(vector: AlgebraPresentedAlgebraModuleVector<P, C, I>):
    AlgebraPolynomialModuleVector<P, C, I> => algebraPolynomialModuleVector(
        vector.parent.polynomialModule,
        vector.components.map(component => component.representative)
    );

const vectorFromPolynomial = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    module: AlgebraPresentedAlgebraFreeModule<P, C, I>,
    vector: AlgebraPolynomialModuleVector<P, C, I>
): AlgebraPresentedAlgebraModuleVector<P, C, I> => {
    if (!sameAlgebraParent(module.polynomialModule, vector.parent)) {
        return fail(
            'FOREIGN_FREE_MODULE',
            'presentedModuleVectorFromPolynomial.vector',
            'Polynomial vector belongs to a foreign free module'
        );
    }
    return algebraPresentedAlgebraModuleVector(
        module,
        vector.components.map(component =>
            algebraQuotientElement(module.algebra.quotient, component)
        )
    );
};

export interface AlgebraPresentedAlgebraModuleOptions
    extends AlgebraPolynomialModuleGroebnerOptions {
    readonly maximumReductionSteps?: number;
}

export interface AlgebraPresentedAlgebraModule<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> extends AlgebraParent<'presented-algebra-module'> {
    readonly freeModule: AlgebraPresentedAlgebraFreeModule<P, C, I>;
    readonly relations: readonly AlgebraPresentedAlgebraModuleVector<P, C, I>[];
    readonly algebraActionRelations:
        readonly AlgebraPolynomialModuleVector<P, C, I>[];
    readonly liftedRelations: readonly AlgebraPolynomialModuleVector<P, C, I>[];
    readonly combinedRelations: AlgebraPolynomialSubmodule<P, C, I>;
    readonly relationBasis: AlgebraReducedPolynomialModuleGroebnerBasis<P, C, I>;
}

const basisFingerprint = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(basis: AlgebraReducedPolynomialModuleGroebnerBasis<P, C, I>): string =>
    basis.basis.length === 0
        ? 'free'
        : basis.basis.map(vector => hexText(
            vector.components.map(algebraPolynomialText).join('|')
        )).join('--');

const algebraActionRelations = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(module: AlgebraPresentedAlgebraFreeModule<P, C, I>):
    readonly AlgebraPolynomialModuleVector<P, C, I>[] => Object.freeze(
        module.algebra.quotient.basis.basis.flatMap(relation =>
            Array.from({ length: module.rank }, (_, position) =>
                algebraPolynomialModuleVector(
                    module.polynomialModule,
                    Array.from({ length: module.rank }, (_, index) =>
                        index === position
                            ? relation
                            : algebraPolynomialZero(
                                module.algebra.quotient.polynomialRing
                            )
                    )
                )
            )
        )
    );

export function algebraPresentedAlgebraModule<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    freeModule: AlgebraPresentedAlgebraFreeModule<P, C, I>,
    relationInput: readonly AlgebraPresentedAlgebraModuleVector<P, C, I>[],
    options: AlgebraPresentedAlgebraModuleOptions = {}
): AlgebraPresentedAlgebraModule<P, C, I> {
    if (!Array.isArray(relationInput)) {
        return fail(
            'INVALID_VECTOR',
            'presentedModule.relations',
            'Module relations must be one ordered array'
        );
    }
    const relations = Object.freeze(relationInput.map((relation, index) => {
        if (!sameAlgebraParent(relation.parent, freeModule)) {
            return fail(
                'FOREIGN_FREE_MODULE',
                `presentedModule.relations[${index}]`,
                'Module relation belongs to a foreign free module'
            );
        }
        return algebraPresentedAlgebraModuleVector(
            freeModule,
            relation.components
        );
    }));
    const actionRelations = algebraActionRelations(freeModule);
    const liftedRelations = Object.freeze(relations.map(
        algebraPresentedAlgebraModuleVectorLift
    ));
    const combinedRelations = algebraPolynomialSubmodule(
        freeModule.polynomialModule,
        [...actionRelations, ...liftedRelations]
    );
    const completeBasis = algebraPolynomialModuleGroebnerBasis(
        combinedRelations,
        options
    );
    const relationBasis = algebraReducedPolynomialModuleGroebnerBasis(
        completeBasis,
        options.maximumReductionSteps
    );
    const parent = defineAlgebraParent(
        'presented-algebra-module',
        `algebra.presented-module/${freeModule.algebra.quotient.identity.id}/` +
            `${freeModule.rank}/${freeModule.termOrder}/` +
            basisFingerprint(relationBasis),
        `v1.${freeModule.algebra.quotient.identity.revision}`
    );
    return Object.freeze({
        ...parent,
        freeModule,
        relations,
        algebraActionRelations: actionRelations,
        liftedRelations,
        combinedRelations,
        relationBasis
    });
}

export interface AlgebraPresentedAlgebraModuleNormalization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-presented-algebra-module-normalization';
    readonly module: AlgebraPresentedAlgebraModule<P, C, I>;
    readonly input: AlgebraPresentedAlgebraModuleVector<P, C, I>;
    readonly lift: AlgebraPolynomialModuleVector<P, C, I>;
    readonly membership: AlgebraPolynomialModuleMembership<P, C, I>;
    readonly algebraActionCoefficients: readonly AlgebraPolynomial<P, C, I>[];
    readonly relationCoefficients: readonly AlgebraPolynomial<P, C, I>[];
    readonly representative: AlgebraPresentedAlgebraModuleVector<P, C, I>;
}

export function algebraPresentedAlgebraModuleNormalize<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    module: AlgebraPresentedAlgebraModule<P, C, I>,
    vector: AlgebraPresentedAlgebraModuleVector<P, C, I>
): AlgebraPresentedAlgebraModuleNormalization<P, C, I> {
    if (!sameAlgebraParent(vector.parent, module.freeModule)) {
        return fail(
            'FOREIGN_FREE_MODULE',
            'presentedModuleNormalize.vector',
            'Vector belongs to a foreign free module'
        );
    }
    const input = algebraPresentedAlgebraModuleVector(
        module.freeModule,
        vector.components
    );
    const lift = algebraPresentedAlgebraModuleVectorLift(input);
    const membership = algebraPolynomialModuleMembership(
        lift,
        module.relationBasis
    );
    const actionCount = module.algebraActionRelations.length;
    return Object.freeze({
        kind: 'algebra-presented-algebra-module-normalization',
        module,
        input,
        lift,
        membership,
        algebraActionCoefficients: Object.freeze(
            membership.coefficients.slice(0, actionCount)
        ),
        relationCoefficients: Object.freeze(
            membership.coefficients.slice(actionCount)
        ),
        representative: vectorFromPolynomial(module.freeModule, membership.remainder)
    });
}

export interface AlgebraPresentedAlgebraModuleElement<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> extends AlgebraElement<AlgebraPresentedAlgebraModule<P, C, I>> {
    readonly kind: 'algebra-presented-algebra-module-element';
    readonly representative: AlgebraPresentedAlgebraModuleVector<P, C, I>;
}

export function algebraPresentedAlgebraModuleElement<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    module: AlgebraPresentedAlgebraModule<P, C, I>,
    vector: AlgebraPresentedAlgebraModuleVector<P, C, I>
): AlgebraPresentedAlgebraModuleElement<P, C, I> {
    const normalization = algebraPresentedAlgebraModuleNormalize(module, vector);
    return Object.freeze({
        kind: 'algebra-presented-algebra-module-element',
        parent: module,
        representative: normalization.representative
    });
}

const samePresentedModule = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPresentedAlgebraModuleElement<P, C, I>,
    right: AlgebraPresentedAlgebraModuleElement<P, C, I>,
    path: string
): AlgebraPresentedAlgebraModule<P, C, I> => {
    if (!sameAlgebraParent(left.parent, right.parent)) {
        return fail(
            'FOREIGN_PRESENTED_MODULE',
            path,
            'Elements belong to different presented modules'
        );
    }
    return left.parent;
};

export const algebraPresentedAlgebraModuleElementZero = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(module: AlgebraPresentedAlgebraModule<P, C, I>):
    AlgebraPresentedAlgebraModuleElement<P, C, I> =>
    algebraPresentedAlgebraModuleElement(
        module,
        algebraPresentedAlgebraModuleVectorZero(module.freeModule)
    );

export const algebraPresentedAlgebraModuleElementAdd = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPresentedAlgebraModuleElement<P, C, I>,
    right: AlgebraPresentedAlgebraModuleElement<P, C, I>
): AlgebraPresentedAlgebraModuleElement<P, C, I> => {
    const module = samePresentedModule(left, right, 'presentedModuleElementAdd');
    return algebraPresentedAlgebraModuleElement(
        module,
        algebraPresentedAlgebraModuleVectorAdd(
            left.representative,
            right.representative
        )
    );
};

export const algebraPresentedAlgebraModuleElementNegate = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(element: AlgebraPresentedAlgebraModuleElement<P, C, I>):
    AlgebraPresentedAlgebraModuleElement<P, C, I> =>
    algebraPresentedAlgebraModuleElement(
        element.parent,
        algebraPresentedAlgebraModuleVectorNegate(element.representative)
    );

export function algebraPresentedAlgebraModuleElementScale<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    scalar: AlgebraQuotientElement<P, C, I>,
    element: AlgebraPresentedAlgebraModuleElement<P, C, I>
): AlgebraPresentedAlgebraModuleElement<P, C, I> {
    if (!sameAlgebraParent(
        scalar.parent,
        element.parent.freeModule.algebra.quotient
    )) {
        return fail(
            'FOREIGN_ALGEBRA',
            'presentedModuleElementScale.scalar',
            'Scalar belongs to a foreign presented algebra'
        );
    }
    return algebraPresentedAlgebraModuleElement(
        element.parent,
        algebraPresentedAlgebraModuleVectorScale(
            scalar,
            element.representative
        )
    );
}

export const algebraPresentedAlgebraModuleElementEquals = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPresentedAlgebraModuleElement<P, C, I>,
    right: AlgebraPresentedAlgebraModuleElement<P, C, I>
): boolean => sameAlgebraParent(left.parent, right.parent) &&
    algebraPresentedAlgebraModuleVectorEquals(
        left.representative,
        right.representative
    );

export const algebraPresentedAlgebraModuleElementIsZero = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(element: AlgebraPresentedAlgebraModuleElement<P, C, I>): boolean =>
    algebraPresentedAlgebraModuleElementEquals(
        element,
        algebraPresentedAlgebraModuleElementZero(element.parent)
    );

export const algebraPresentedAlgebraModuleIsZero = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(module: AlgebraPresentedAlgebraModule<P, C, I>): boolean =>
    Array.from({ length: module.freeModule.rank }, (_, position) =>
        algebraPresentedAlgebraModuleElement(
            module,
            algebraPresentedAlgebraModuleBasisVector(
                module.freeModule,
                position
            )
        )
    ).every(algebraPresentedAlgebraModuleElementIsZero);

export function algebraPresentedAlgebraModuleVectorSchema<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(module: AlgebraPresentedAlgebraFreeModule<P, C, I>): AlgebraRuntimeSchema<
    AlgebraPresentedAlgebraModuleVector<P, C, I>
> {
    return defineAlgebraRuntimeSchema({
        id: `algebra.presented-module-vector/${module.identity.id}`,
        revision: module.identity.revision,
        normalize(value: unknown, path: string) {
            if (
                !record(value) ||
                value.kind !== 'algebra-presented-algebra-module-vector' ||
                !record(value.parent) ||
                !sameAlgebraParent(value.parent as unknown as AlgebraParent, module) ||
                !Array.isArray(value.components)
            ) throw new Error(`presented module vector expected at ${path}`);
            return algebraPresentedAlgebraModuleVector(
                module,
                value.components as AlgebraQuotientElement<P, C, I>[]
            );
        }
    });
}

export function algebraPresentedAlgebraModuleElementSchema<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(module: AlgebraPresentedAlgebraModule<P, C, I>): AlgebraRuntimeSchema<
    AlgebraPresentedAlgebraModuleElement<P, C, I>
> {
    const vectorSchema = algebraPresentedAlgebraModuleVectorSchema(
        module.freeModule
    );
    return defineAlgebraRuntimeSchema({
        id: `algebra.presented-module-element/${module.identity.id}`,
        revision: module.identity.revision,
        normalize(value: unknown, path: string) {
            if (
                !record(value) ||
                value.kind !== 'algebra-presented-algebra-module-element' ||
                !record(value.parent) ||
                !sameAlgebraParent(value.parent as unknown as AlgebraParent, module)
            ) throw new Error(`presented module element expected at ${path}`);
            return algebraPresentedAlgebraModuleElement(
                module,
                vectorSchema.normalize(value.representative, `${path}.representative`)
            );
        }
    });
}

export const serializeAlgebraPresentedAlgebraModule = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(module: AlgebraPresentedAlgebraModule<P, C, I>): string => `${JSON.stringify({
    revision: ALGEBRA_PRESENTED_MODULE_PROFILE.revision,
    kind: module.kind,
    identity: module.identity,
    algebra: module.freeModule.algebra.quotient.identity,
    rank: module.freeModule.rank,
    termOrder: module.freeModule.termOrder,
    relations: module.relations.map(relation =>
        relation.components.map(algebraQuotientText)
    ),
    reducedRelationBasis: module.relationBasis.basis.map(vector =>
        vector.components.map(algebraPolynomialText)
    )
})}\n`;

export const serializeAlgebraPresentedAlgebraModuleElement = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(element: AlgebraPresentedAlgebraModuleElement<P, C, I>): string =>
    `${JSON.stringify({
        revision: ALGEBRA_PRESENTED_MODULE_PROFILE.revision,
        kind: element.kind,
        module: element.parent.identity,
        representative: element.representative.components.map(algebraQuotientText)
    })}\n`;
