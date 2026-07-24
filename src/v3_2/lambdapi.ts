/**
 * Deterministic Lambdapi v3.2 conformance backend for explicit emdash Core.
 *
 * Active symbol spellings and source provenance live here, not in Core or the
 * surface grammar. The TypeScript product path can therefore replace this
 * backend without changing elaboration results.
 */

import {
    KernelBinder,
    KernelExpression
} from './kernel';
import {
    CoreOwnerId
} from './schema';

export const LAMBDAPI_V32_MODULE = 'emdash.emdash3_2' as const;

export interface LambdapiOwnerBinding {
    module: typeof LAMBDAPI_V32_MODULE;
    serializedName: string;
    provenance: {
        authorityPath: 'emdash2/emdash3_2.lp';
        section: string;
        declaration: string;
        auditedOn: '2026-07-23';
    };
}

const binding = (
    serializedName: string,
    section: string,
    declaration: string
): LambdapiOwnerBinding => ({
    module: LAMBDAPI_V32_MODULE,
    serializedName,
    provenance: {
        authorityPath: 'emdash2/emdash3_2.lp',
        section,
        declaration,
        auditedOn: '2026-07-23'
    }
});

/**
 * Lambdapi names for every owner in the ELAB-1B Core catalog.
 *
 * Sections are stable source anchors; callers must relocate declarations by
 * name instead of treating a remembered line number as authority.
 */
export const LAMBDAPI_V32_OWNER_BINDINGS = {
    'category-universe': binding(
        'Cat',
        '2. Core categories',
        'constant symbol Cat'
    ),
    decode: binding(
        'τ',
        '0. Groupoid universe and equality',
        'injective symbol τ'
    ),
    'object-classifier': binding(
        'Obj',
        '2. Core categories',
        'symbol Obj'
    ),
    'functor-classifier': binding(
        'Functor',
        '3a. Ordinary functor classifier and action',
        'injective symbol Functor'
    ),
    'hom-classifier': binding(
        'Hom',
        '2. Core categories',
        'injective symbol Hom'
    ),
    'transfor-classifier': binding(
        'Transf',
        '6a. Transformation classifier, components, and generic projection calculus',
        'injective symbol Transf'
    ),
    'hom-category': binding(
        'Hom_cat',
        '2. Core categories',
        'injective symbol Hom_cat'
    ),
    'transfor-category': binding(
        'Transf_cat',
        '6a. Transformation classifier, components, and generic projection calculus',
        'injective symbol Transf_cat'
    ),
    'functor-object': binding(
        'fapp0',
        '3a. Ordinary functor classifier and action',
        'symbol fapp0'
    ),
    'functor-hom-full': binding(
        'fapp1_func',
        '3a. Ordinary functor classifier and action',
        'symbol fapp1_func'
    ),
    'functor-hom-capped': binding(
        'fapp1_fapp0',
        '3a. Ordinary functor classifier and action',
        'symbol fapp1_fapp0'
    ),
    'transfor-component-full': binding(
        'tapp0_func',
        '6a. Transformation classifier, components, and generic projection calculus',
        'symbol tapp0_func'
    ),
    'transfor-component-capped': binding(
        'tapp0_fapp0',
        '6a. Transformation classifier, components, and generic projection calculus',
        'symbol tapp0_fapp0'
    ),
    'transfor-hom-full': binding(
        'tapp1_func',
        '6a. Transformation classifier, components, and generic projection calculus',
        'symbol tapp1_func'
    ),
    'transfor-hom-capped': binding(
        'tapp1_fapp0',
        '6a. Transformation classifier, components, and generic projection calculus',
        'symbol tapp1_fapp0'
    )
} as const satisfies Record<CoreOwnerId, LambdapiOwnerBinding>;

const parenthesize = (expression: KernelExpression): string =>
    expression.tag === 'reference'
        ? serializeKernelExpression(expression)
        : `(${serializeKernelExpression(expression)})`;

const serializeBinder = (binder: KernelBinder): string => {
    const typed = `${binder.name} : ${serializeKernelExpression(binder.type)}`;
    return binder.mode.plicity === 'implicit' ? `[${typed}]` : `(${typed})`;
};

export function serializeKernelExpression(
    expression: KernelExpression
): string {
    switch (expression.tag) {
        case 'reference':
            return expression.name;
        case 'application': {
            const backend = LAMBDAPI_V32_OWNER_BINDINGS[expression.owner];
            const hasImplicitArguments = expression.arguments.some(
                argument => argument.plicity === 'implicit'
            );
            const head = hasImplicitArguments
                ? `@${backend.serializedName}`
                : backend.serializedName;
            return [
                head,
                ...expression.arguments.map(argument =>
                    parenthesize(argument.value)
                )
            ].join(' ');
        }
        case 'pi':
            return `Π ${serializeBinder(expression.binder)}, ` +
                serializeKernelExpression(expression.body);
        case 'lambda':
            return `λ ${serializeBinder(expression.binder)}, ` +
                serializeKernelExpression(expression.body);
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
}
