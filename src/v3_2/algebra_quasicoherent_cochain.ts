/** Heterogeneous additive cochains over a varying-ring affine Cech diagram. */

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
import { algebraQuotientText } from './algebra_quotient';
import {
    AlgebraPresentedAlgebraModuleElement,
    algebraPresentedAlgebraModuleElementAdd,
    algebraPresentedAlgebraModuleElementEquals,
    algebraPresentedAlgebraModuleElementIsZero,
    algebraPresentedAlgebraModuleElementNegate,
    algebraPresentedAlgebraModuleElementSchema,
    algebraPresentedAlgebraModuleElementZero
} from './algebra_presented_module';
import { algebraPresentedModuleBaseChangeElement } from
    './algebra_presented_module_base_change';
import {
    AlgebraAffineQuasiCoherentCechDegree,
    AlgebraAffineQuasiCoherentCechDiagram
} from './algebra_quasicoherent_cech';

export const ALGEBRA_QUASICOHERENT_COCHAIN_PROFILE = Object.freeze({
    revision: 'emdash-quasicoherent-cochain-v1' as const,
    representation: 'ordered-heterogeneous-module-element-tuple' as const,
    commonScalarParent: false as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraQuasiCoherentCochainErrorCode =
    | 'INVALID_DEGREE'
    | 'INVALID_COMPONENT_ARITY'
    | 'FOREIGN_COMPONENT'
    | 'FOREIGN_COCHAIN'
    | 'INVALID_COMPONENT_POSITION'
    | 'UNKNOWN_SIMPLEX'
    | 'FOREIGN_GLOBAL_ELEMENT';

export class AlgebraQuasiCoherentCochainError extends Error {
    constructor(
        public readonly code: AlgebraQuasiCoherentCochainErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraQuasiCoherentCochainError';
    }
}

const fail = (
    code: AlgebraQuasiCoherentCochainErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraQuasiCoherentCochainError(code, path, message);
};

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

const hexText = (value: string): string => Array.from(new TextEncoder().encode(value))
    .map(byte => byte.toString(16).padStart(2, '0'))
    .join('');

const key = (indices: readonly number[]): string => indices.join(',');

export interface AlgebraAffineQuasiCoherentCochainDegree<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> extends AlgebraParent<'quasicoherent-cech-cochain-degree'> {
    readonly diagram: AlgebraAffineQuasiCoherentCechDiagram<P, C, I>;
    readonly degree: number;
    readonly data: AlgebraAffineQuasiCoherentCechDegree<P, C, I>;
}

export function algebraAffineQuasiCoherentCochainDegree<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    diagram: AlgebraAffineQuasiCoherentCechDiagram<P, C, I>,
    degree: number
): AlgebraAffineQuasiCoherentCochainDegree<P, C, I> {
    if (!Number.isSafeInteger(degree) || degree < 0) {
        return fail(
            'INVALID_DEGREE',
            'quasicoherentCochainDegree.degree',
            'Cochain degree must be a retained nonnegative safe integer'
        );
    }
    const data = diagram.degrees.find(candidate => candidate.degree === degree);
    if (data === undefined) {
        return fail(
            'INVALID_DEGREE',
            'quasicoherentCochainDegree.degree',
            `Cech diagram has no retained degree ${degree}`
        );
    }
    const fingerprint = data.simplices.map(simplex =>
        `${key(simplex.simplex.indices)}:${simplex.value.module.identity.id}`
    ).join('|') || 'empty';
    const parent = defineAlgebraParent(
        'quasicoherent-cech-cochain-degree',
        `algebra.quasicoherent-cochain/` +
            `${diagram.presentation.module.identity.id}/` +
            `${diagram.cover.elements.length}/${diagram.cover.maximumDegree}/` +
            `${degree}/${hexText(fingerprint)}`,
        `v1.${diagram.presentation.module.identity.revision}`
    );
    return Object.freeze({
        ...parent,
        diagram,
        degree,
        data
    });
}

export interface AlgebraAffineQuasiCoherentCochain<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> extends AlgebraElement<AlgebraAffineQuasiCoherentCochainDegree<P, C, I>> {
    readonly kind: 'algebra-affine-quasicoherent-cochain';
    readonly components:
        readonly AlgebraPresentedAlgebraModuleElement<P, C, I>[];
}

export function algebraAffineQuasiCoherentCochain<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    parent: AlgebraAffineQuasiCoherentCochainDegree<P, C, I>,
    componentInput:
        readonly AlgebraPresentedAlgebraModuleElement<P, C, I>[]
): AlgebraAffineQuasiCoherentCochain<P, C, I> {
    if (!Array.isArray(componentInput) ||
        componentInput.length !== parent.data.simplices.length) {
        return fail(
            'INVALID_COMPONENT_ARITY',
            'quasicoherentCochain.components',
            `Expected ${parent.data.simplices.length} cochain components`
        );
    }
    const components = Object.freeze(componentInput.map((component, index) => {
        const module = parent.data.simplices[index].value.module;
        if (!sameAlgebraParent(component.parent, module)) {
            return fail(
                'FOREIGN_COMPONENT',
                `quasicoherentCochain.components[${index}]`,
                'Cochain component belongs to the wrong simplex module'
            );
        }
        return algebraPresentedAlgebraModuleElementSchema(module).normalize(
            component,
            `quasicoherentCochain.components[${index}]`
        );
    }));
    return Object.freeze({
        kind: 'algebra-affine-quasicoherent-cochain',
        parent,
        components
    });
}

export const algebraAffineQuasiCoherentCochainZero = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(parent: AlgebraAffineQuasiCoherentCochainDegree<P, C, I>):
    AlgebraAffineQuasiCoherentCochain<P, C, I> =>
    algebraAffineQuasiCoherentCochain(
        parent,
        parent.data.simplices.map(simplex =>
            algebraPresentedAlgebraModuleElementZero(simplex.value.module)
        )
    );

const sameCochainParent = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraAffineQuasiCoherentCochain<P, C, I>,
    right: AlgebraAffineQuasiCoherentCochain<P, C, I>,
    path: string
): AlgebraAffineQuasiCoherentCochainDegree<P, C, I> => {
    if (!sameAlgebraParent(left.parent, right.parent)) {
        return fail(
            'FOREIGN_COCHAIN',
            path,
            'Cochains belong to different diagram degrees'
        );
    }
    return left.parent;
};

export const algebraAffineQuasiCoherentCochainAdd = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraAffineQuasiCoherentCochain<P, C, I>,
    right: AlgebraAffineQuasiCoherentCochain<P, C, I>
): AlgebraAffineQuasiCoherentCochain<P, C, I> => {
    const parent = sameCochainParent(left, right, 'quasicoherentCochainAdd');
    return algebraAffineQuasiCoherentCochain(
        parent,
        left.components.map((component, index) =>
            algebraPresentedAlgebraModuleElementAdd(
                component,
                right.components[index]
            )
        )
    );
};

export const algebraAffineQuasiCoherentCochainNegate = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(cochain: AlgebraAffineQuasiCoherentCochain<P, C, I>):
    AlgebraAffineQuasiCoherentCochain<P, C, I> =>
    algebraAffineQuasiCoherentCochain(
        cochain.parent,
        cochain.components.map(algebraPresentedAlgebraModuleElementNegate)
    );

export const algebraAffineQuasiCoherentCochainSubtract = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraAffineQuasiCoherentCochain<P, C, I>,
    right: AlgebraAffineQuasiCoherentCochain<P, C, I>
): AlgebraAffineQuasiCoherentCochain<P, C, I> =>
    algebraAffineQuasiCoherentCochainAdd(
        left,
        algebraAffineQuasiCoherentCochainNegate(right)
    );

export const algebraAffineQuasiCoherentCochainEquals = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraAffineQuasiCoherentCochain<P, C, I>,
    right: AlgebraAffineQuasiCoherentCochain<P, C, I>
): boolean => sameAlgebraParent(left.parent, right.parent) &&
    left.components.every((component, index) =>
        algebraPresentedAlgebraModuleElementEquals(
            component,
            right.components[index]
        )
    );

export const algebraAffineQuasiCoherentCochainIsZero = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(cochain: AlgebraAffineQuasiCoherentCochain<P, C, I>): boolean =>
    cochain.components.every(algebraPresentedAlgebraModuleElementIsZero);

export function algebraAffineQuasiCoherentCochainComponentAt<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    cochain: AlgebraAffineQuasiCoherentCochain<P, C, I>,
    position: number
): AlgebraPresentedAlgebraModuleElement<P, C, I> {
    if (!Number.isSafeInteger(position) ||
        position < 0 || position >= cochain.components.length) {
        return fail(
            'INVALID_COMPONENT_POSITION',
            'quasicoherentCochainComponent.position',
            'Cochain component position is out of bounds'
        );
    }
    return cochain.components[position];
}

export function algebraAffineQuasiCoherentCochainComponentAtIndices<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    cochain: AlgebraAffineQuasiCoherentCochain<P, C, I>,
    indices: readonly number[]
): AlgebraPresentedAlgebraModuleElement<P, C, I> {
    const position = cochain.parent.data.simplices.findIndex(simplex =>
        key(simplex.simplex.indices) === key(indices)
    );
    if (position < 0) {
        return fail(
            'UNKNOWN_SIMPLEX',
            'quasicoherentCochainComponent.indices',
            `Degree ${cochain.parent.degree} has no simplex [${indices.join(',')}]`
        );
    }
    return cochain.components[position];
}

export function algebraAffineQuasiCoherentCochainFromGlobalElement<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    parent: AlgebraAffineQuasiCoherentCochainDegree<P, C, I>,
    element: AlgebraPresentedAlgebraModuleElement<P, C, I>
): AlgebraAffineQuasiCoherentCochain<P, C, I> {
    if (!sameAlgebraParent(
        element.parent,
        parent.diagram.presentation.module
    )) {
        return fail(
            'FOREIGN_GLOBAL_ELEMENT',
            'quasicoherentCochain.globalElement',
            'Global element belongs to a foreign ambient module'
        );
    }
    return algebraAffineQuasiCoherentCochain(
        parent,
        parent.data.simplices.map(simplex =>
            algebraPresentedModuleBaseChangeElement(
                simplex.value.baseChange,
                element
            )
        )
    );
}

export function algebraAffineQuasiCoherentCochainSchema<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(parent: AlgebraAffineQuasiCoherentCochainDegree<P, C, I>):
    AlgebraRuntimeSchema<AlgebraAffineQuasiCoherentCochain<P, C, I>> {
    return defineAlgebraRuntimeSchema({
        id: `algebra.quasicoherent-cochain/${parent.identity.id}`,
        revision: ALGEBRA_QUASICOHERENT_COCHAIN_PROFILE.revision,
        normalize(value: unknown, path: string) {
            if (
                !record(value) ||
                value.kind !== 'algebra-affine-quasicoherent-cochain' ||
                !record(value.parent) ||
                !sameAlgebraParent(value.parent as unknown as AlgebraParent, parent) ||
                !Array.isArray(value.components)
            ) throw new Error(`quasi-coherent cochain expected at ${path}`);
            return algebraAffineQuasiCoherentCochain(
                parent,
                value.components as AlgebraPresentedAlgebraModuleElement<P, C, I>[]
            );
        }
    });
}

export const serializeAlgebraAffineQuasiCoherentCochain = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(cochain: AlgebraAffineQuasiCoherentCochain<P, C, I>): string =>
    `${JSON.stringify({
        revision: ALGEBRA_QUASICOHERENT_COCHAIN_PROFILE.revision,
        kind: cochain.kind,
        parent: cochain.parent.identity,
        degree: cochain.parent.degree,
        components: cochain.components.map((component, index) => ({
            indices: cochain.parent.data.simplices[index].simplex.indices,
            module: component.parent.identity,
            representative: component.representative.components.map(
                algebraQuotientText
            )
        }))
    })}\n`;
