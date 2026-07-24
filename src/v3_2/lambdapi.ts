/**
 * Deterministic Lambdapi v3.2 conformance backend for explicit emdash Core.
 *
 * Active symbol spellings and source provenance live here, not in Core or the
 * surface grammar. The TypeScript product path can therefore replace this
 * backend without changing elaboration results.
 */

import {
    KernelExpression,
    KernelMetaVariable,
    kernelAssertScoped
} from './kernel';
import {
    CoreOwnerId
} from './schema';

export const LAMBDAPI_V32_MODULE = 'emdash.emdash3_2' as const;

export class UnsolvedKernelMetaError extends Error {
    constructor(public readonly meta: KernelMetaVariable) {
        super(
            `Cannot serialize unsolved Core metavariable ` +
            `?m${meta.identity.index}; zonk it through its owning session first`
        );
        this.name = 'UnsolvedKernelMetaError';
    }
}

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
 * Lambdapi names for every owner in the current Core catalog.
 *
 * Sections are stable source anchors; callers must relocate declarations by
 * name instead of treating a remembered line number as authority.
 */
export const LAMBDAPI_V32_OWNER_BINDINGS = {
    'groupoid-universe': binding(
        'Grpd',
        '0. Groupoid universe and equality',
        'constant symbol Grpd'
    ),
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
    'category-of-categories': binding(
        'Cat_cat',
        '3c. Universe categories',
        'constant symbol Cat_cat'
    ),
    'opposite-category': binding(
        'Op_cat',
        '2. Core categories',
        'injective symbol Op_cat'
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
    'displayed-category-category': binding(
        'Catd_cat',
        '3d. Directed-family and displayed-arrow classifiers',
        'injective symbol Catd_cat'
    ),
    'internal-hom-source': binding(
        'hom_int',
        '4d. Internalized source/target endpoints and variance comparison',
        'injective symbol hom_int'
    ),
    'internal-hom-target': binding(
        'hom_con_int',
        '4d. Internalized source/target endpoints and variance comparison',
        'injective symbol hom_con_int'
    ),
    'displayed-pullback': binding(
        'Pullback_catd',
        '8a. Fibre notation, pullback, and base-arrow transport',
        'injective symbol Pullback_catd'
    ),
    'constant-displayed-family': binding(
        'Const_catd',
        '8b. Constant, terminal, opposite, and displayed composition',
        'injective symbol Const_catd'
    ),
    'section-category': binding(
        'Pi_cat',
        '8c. Section categories and Pi action',
        'injective symbol Pi_cat'
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

/**
 * Backend-only proof constructors used by conformance probes.
 *
 * They are intentionally not Core owners: ELAB-2B needs oracle evidence for
 * a proof-time comparison, not equality syntax in the product fragment.
 */
export const LAMBDAPI_V32_PROOF_PROBE_BINDINGS = {
    equality: binding(
        '=',
        '0. Groupoid universe and equality',
        'injective symbol ='
    ),
    reflexivity: binding(
        'eq_refl',
        '0. Groupoid universe and equality',
        'injective symbol eq_refl'
    )
} as const;

interface SerializationState {
    nextBoundName: number;
    reservedNames: Set<string>;
}

function collectFreeReferenceNames(
    expression: KernelExpression,
    names: Set<string>
): void {
    switch (expression.tag) {
        case 'universe':
            return;
        case 'reference':
            names.add(expression.name);
            return;
        case 'bound':
            return;
        case 'meta':
            expression.spine.forEach(item =>
                collectFreeReferenceNames(item, names)
            );
            return;
        case 'application':
            expression.arguments.forEach(argument =>
                collectFreeReferenceNames(argument.value, names)
            );
            return;
        case 'call':
            collectFreeReferenceNames(expression.callee, names);
            expression.arguments.forEach(argument =>
                collectFreeReferenceNames(argument.value, names)
            );
            return;
        case 'pi':
        case 'lambda':
            collectFreeReferenceNames(expression.binder.type, names);
            collectFreeReferenceNames(expression.body, names);
            return;
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
}

function freshBoundName(state: SerializationState): string {
    while (true) {
        const candidate = `v${state.nextBoundName++}`;
        if (state.reservedNames.has(candidate)) continue;
        state.reservedNames.add(candidate);
        return candidate;
    }
}

function serializeExpression(
    expression: KernelExpression,
    state: SerializationState,
    boundNames: readonly string[]
): string {
    const parenthesize = (child: KernelExpression): string =>
        child.tag === 'universe' ||
            child.tag === 'reference' ||
            child.tag === 'bound'
            ? serializeExpression(child, state, boundNames)
            : `(${serializeExpression(child, state, boundNames)})`;

    switch (expression.tag) {
        case 'universe':
            return 'TYPE';
        case 'reference':
            return expression.name;
        case 'bound': {
            const name = boundNames[expression.index];
            if (name === undefined) {
                throw new Error(
                    `Internal serializer scope mismatch for bound index ` +
                    expression.index
                );
            }
            return name;
        }
        case 'meta':
            throw new UnsolvedKernelMetaError(expression);
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
        case 'call': {
            let callee = expression.callee;
            const callArguments = [...expression.arguments];
            while (callee.tag === 'call') {
                callArguments.unshift(...callee.arguments);
                callee = callee.callee;
            }
            const serializedCallee = serializeExpression(
                callee,
                state,
                boundNames
            );
            const head =
                callee.tag === 'reference' || callee.tag === 'bound'
                    ? serializedCallee
                    : `(${serializedCallee})`;
            const revealImplicits = callArguments.some(
                argument => argument.plicity === 'implicit'
            );
            return [
                `${revealImplicits ? '@' : ''}${head}`,
                ...callArguments.map(argument =>
                    parenthesize(argument.value)
                )
            ].join(' ');
        }
        case 'pi':
        case 'lambda': {
            const boundName = freshBoundName(state);
            const typed =
                `${boundName} : ` +
                serializeExpression(
                    expression.binder.type,
                    state,
                    boundNames
                );
            const binder = expression.binder.mode.plicity === 'implicit'
                ? `[${typed}]`
                : `(${typed})`;
            const body = serializeExpression(
                expression.body,
                state,
                [boundName, ...boundNames]
            );
            const head = expression.tag === 'pi' ? 'Π' : 'λ';
            return `${head} ${binder}, ${body}`;
        }
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
}

export function serializeKernelExpression(
    expression: KernelExpression
): string {
    kernelAssertScoped(expression);
    const reservedNames = new Set(
        Object.values(LAMBDAPI_V32_OWNER_BINDINGS).map(
            owner => owner.serializedName
        )
    );
    collectFreeReferenceNames(expression, reservedNames);
    return serializeExpression(
        expression,
        { nextBoundName: 0, reservedNames },
        []
    );
}
