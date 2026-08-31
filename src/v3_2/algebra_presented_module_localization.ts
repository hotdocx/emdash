/** Principal localization of modules as presented-algebra base change. */

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
    AlgebraGroebnerOptions
} from './algebra_ideal';
import {
    AlgebraQuotientElement,
    algebraQuotientText
} from './algebra_quotient';
import {
    AlgebraPrincipalLocalization,
    algebraPrincipalLocalization
} from './algebra_localization';
import {
    AlgebraPresentedAlgebraModule,
    AlgebraPresentedAlgebraModuleOptions,
    algebraPresentedAlgebraModuleIsZero
} from './algebra_presented_module';
import {
    AlgebraPresentedAlgebraModuleSemilinearMap
} from './algebra_presented_module_map';
import {
    AlgebraPresentedModuleBaseChange,
    AlgebraPresentedModuleMapBaseChange,
    algebraPresentedModuleBaseChange,
    algebraPresentedModuleBaseChangeMap
} from './algebra_presented_module_base_change';

export const ALGEBRA_PRESENTED_MODULE_LOCALIZATION_PROFILE = Object.freeze({
    revision: 'emdash-presented-module-localization-v1' as const,
    construction: 'base-change-along-principal-localization' as const,
    fractionSyntax: false as const,
    specialZeroBranch: false as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraPresentedModuleLocalizationErrorCode =
    | 'FOREIGN_LOCALIZED_ELEMENT';

export class AlgebraPresentedModuleLocalizationError extends Error {
    constructor(
        public readonly code: AlgebraPresentedModuleLocalizationErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraPresentedModuleLocalizationError';
    }
}

const fail = (
    code: AlgebraPresentedModuleLocalizationErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraPresentedModuleLocalizationError(code, path, message);
};

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

const hexText = (value: string): string => Array.from(new TextEncoder().encode(value))
    .map(byte => byte.toString(16).padStart(2, '0'))
    .join('');

export interface AlgebraPresentedModuleLocalizationOptions {
    readonly localization?: AlgebraGroebnerOptions;
    readonly module?: AlgebraPresentedAlgebraModuleOptions;
}

export interface AlgebraPresentedModuleLocalization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-presented-module-localization';
    readonly source: AlgebraPresentedAlgebraModule<P, C, I>;
    readonly element: AlgebraQuotientElement<P, C, I>;
    readonly localization: AlgebraPrincipalLocalization<P, C, I>;
    readonly baseChange: AlgebraPresentedModuleBaseChange<P, C, I>;
    readonly module: AlgebraPresentedAlgebraModule<P, C, I>;
    readonly unit: AlgebraPresentedAlgebraModuleSemilinearMap<P, C, I>;
    readonly isZero: boolean;
}

export function algebraPresentedModuleLocalization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    source: AlgebraPresentedAlgebraModule<P, C, I>,
    element: AlgebraQuotientElement<P, C, I>,
    options: AlgebraPresentedModuleLocalizationOptions = {}
): AlgebraPresentedModuleLocalization<P, C, I> {
    if (!sameAlgebraParent(
        element.parent,
        source.freeModule.algebra.quotient
    )) {
        return fail(
            'FOREIGN_LOCALIZED_ELEMENT',
            'moduleLocalization.element',
            'Localized element belongs to a foreign module scalar algebra'
        );
    }
    const localization = algebraPrincipalLocalization(
        source.freeModule.algebra,
        element,
        options.localization
    );
    const baseChange = algebraPresentedModuleBaseChange(
        localization.canonicalMap,
        source,
        options.module
    );
    return Object.freeze({
        kind: 'algebra-presented-module-localization',
        source,
        element,
        localization,
        baseChange,
        module: baseChange.target,
        unit: baseChange.unit,
        isZero: algebraPresentedAlgebraModuleIsZero(baseChange.target)
    });
}

export interface AlgebraPresentedModuleMapLocalization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-presented-module-map-localization';
    readonly element: AlgebraQuotientElement<P, C, I>;
    readonly localization: AlgebraPrincipalLocalization<P, C, I>;
    readonly baseChange: AlgebraPresentedModuleMapBaseChange<P, C, I>;
}

export function algebraPresentedModuleMapLocalization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    map: AlgebraPresentedAlgebraModuleSemilinearMap<P, C, I>,
    element: AlgebraQuotientElement<P, C, I>,
    options: AlgebraPresentedModuleLocalizationOptions = {}
): AlgebraPresentedModuleMapLocalization<P, C, I> {
    if (!sameAlgebraParent(
        element.parent,
        map.source.freeModule.algebra.quotient
    )) {
        return fail(
            'FOREIGN_LOCALIZED_ELEMENT',
            'moduleMapLocalization.element',
            'Localized element belongs to a foreign module scalar algebra'
        );
    }
    const localization = algebraPrincipalLocalization(
        map.source.freeModule.algebra,
        element,
        options.localization
    );
    return Object.freeze({
        kind: 'algebra-presented-module-map-localization',
        element,
        localization,
        baseChange: algebraPresentedModuleBaseChangeMap(
            localization.canonicalMap,
            map,
            options.module
        )
    });
}

export function algebraPresentedModuleLocalizationSchema<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    source: AlgebraPresentedAlgebraModule<P, C, I>,
    element: AlgebraQuotientElement<P, C, I>
): AlgebraRuntimeSchema<AlgebraPresentedModuleLocalization<P, C, I>> {
    return defineAlgebraRuntimeSchema({
        id: `algebra.presented-module-localization/${source.identity.id}/` +
            hexText(algebraQuotientText(element)),
        revision: ALGEBRA_PRESENTED_MODULE_LOCALIZATION_PROFILE.revision,
        normalize(value: unknown, path: string) {
            if (
                !record(value) ||
                value.kind !== 'algebra-presented-module-localization' ||
                !record(value.source) ||
                !sameAlgebraParent(value.source as unknown as AlgebraParent, source)
            ) throw new Error(`presented module localization expected at ${path}`);
            return algebraPresentedModuleLocalization(source, element);
        }
    });
}

export const serializeAlgebraPresentedModuleLocalization = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(localization: AlgebraPresentedModuleLocalization<P, C, I>): string =>
    `${JSON.stringify({
        revision: ALGEBRA_PRESENTED_MODULE_LOCALIZATION_PROFILE.revision,
        kind: localization.kind,
        source: localization.source.identity,
        element: algebraQuotientText(localization.element),
        scalarLocalization: {
            target: localization.localization.algebra.quotient.identity,
            inverseVariable: localization.localization.inverseVariable,
            inverseEquation: localization.localization.inverseEquation
        },
        module: localization.module.identity,
        isZero: localization.isZero
    })}\n`;
