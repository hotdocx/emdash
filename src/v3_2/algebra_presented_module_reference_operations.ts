/** Native whole operations for presented modules and affine module descent. */

import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    AlgebraOperation,
    AlgebraRuntimeSchema,
    algebraAlgorithmIdentity,
    defineAlgebraOperation,
    defineAlgebraRuntimeSchema
} from './algebra_engine';
import {
    AlgebraPresentedAlgebraMap
} from './algebra_presented_algebra';
import {
    AlgebraQuotientElement
} from './algebra_quotient';
import {
    AlgebraPresentedAlgebraModule,
    AlgebraPresentedAlgebraModuleElement
} from './algebra_presented_module';
import {
    AlgebraPresentedAlgebraModuleSemilinearMap,
    algebraPresentedAlgebraModuleSemilinearMapApply
} from './algebra_presented_module_map';
import {
    AlgebraPresentedModuleBaseChange,
    algebraPresentedModuleBaseChange
} from './algebra_presented_module_base_change';
import {
    AlgebraPresentedModuleLocalization,
    algebraPresentedModuleLocalization
} from './algebra_presented_module_localization';
import {
    AlgebraAffineCover
} from './algebra_cech';
import {
    AlgebraAffineQuasiCoherentPresentation
} from './algebra_quasicoherent';
import {
    AlgebraAffineQuasiCoherentCechDiagram,
    algebraAffineQuasiCoherentCechDiagram
} from './algebra_quasicoherent_cech';
import {
    AlgebraReferenceImplementation,
    defineAlgebraReferenceImplementation
} from './algebra_reference_engine';

export const ALGEBRA_PRESENTED_MODULE_REFERENCE_PROFILE = Object.freeze({
    revision: 'emdash-presented-module-reference-v1' as const,
    algorithmRevision: 'typescript-presented-module-affine-v1' as const,
    wholeResults: true as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export interface AlgebraPresentedModuleMapApplyInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly map: AlgebraPresentedAlgebraModuleSemilinearMap<P, C, I>;
    readonly element: AlgebraPresentedAlgebraModuleElement<P, C, I>;
}

export interface AlgebraPresentedModuleBaseChangeInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly scalarMap: AlgebraPresentedAlgebraMap<P, C, I>;
    readonly module: AlgebraPresentedAlgebraModule<P, C, I>;
}

export interface AlgebraPresentedModuleLocalizationInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly module: AlgebraPresentedAlgebraModule<P, C, I>;
    readonly element: AlgebraQuotientElement<P, C, I>;
}

export interface AlgebraQuasiCoherentCechInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly presentation: AlgebraAffineQuasiCoherentPresentation<P, C, I>;
    readonly cover: AlgebraAffineCover<P, C, I>;
}

export interface AlgebraPresentedModuleReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly mapApplyInputSchema:
        AlgebraRuntimeSchema<AlgebraPresentedModuleMapApplyInput<P, C, I>>;
    readonly baseChangeInputSchema:
        AlgebraRuntimeSchema<AlgebraPresentedModuleBaseChangeInput<P, C, I>>;
    readonly localizationInputSchema:
        AlgebraRuntimeSchema<AlgebraPresentedModuleLocalizationInput<P, C, I>>;
    readonly cechInputSchema:
        AlgebraRuntimeSchema<AlgebraQuasiCoherentCechInput<P, C, I>>;
    readonly mapApply: AlgebraOperation<
        AlgebraPresentedModuleMapApplyInput<P, C, I>,
        AlgebraPresentedAlgebraModuleElement<P, C, I>
    >;
    readonly baseChange: AlgebraOperation<
        AlgebraPresentedModuleBaseChangeInput<P, C, I>,
        AlgebraPresentedModuleBaseChange<P, C, I>
    >;
    readonly localization: AlgebraOperation<
        AlgebraPresentedModuleLocalizationInput<P, C, I>,
        AlgebraPresentedModuleLocalization<P, C, I>
    >;
    readonly cech: AlgebraOperation<
        AlgebraQuasiCoherentCechInput<P, C, I>,
        AlgebraAffineQuasiCoherentCechDiagram<P, C, I>
    >;
    readonly implementations: readonly AlgebraReferenceImplementation[];
}

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

const inputSchema = <T>(
    id: string,
    normalize: (value: Record<string, unknown>, path: string) => T
): AlgebraRuntimeSchema<T> => defineAlgebraRuntimeSchema({
    id,
    revision: ALGEBRA_PRESENTED_MODULE_REFERENCE_PROFILE.revision,
    normalize(value: unknown, path: string) {
        if (!record(value)) throw new Error(`record expected at ${path}`);
        return normalize(value, path);
    }
});

const wholeSchema = <T extends { readonly kind: string }>(
    id: string,
    kind: T['kind']
): AlgebraRuntimeSchema<T> => defineAlgebraRuntimeSchema({
    id,
    revision: ALGEBRA_PRESENTED_MODULE_REFERENCE_PROFILE.revision,
    normalize(value: unknown, path: string) {
        if (!record(value) || value.kind !== kind) {
            throw new Error(`${kind} expected at ${path}`);
        }
        return value as unknown as T;
    }
});

const algorithm = (id: string) => algebraAlgorithmIdentity(
    `algebra.typescript-reference/${id}`,
    ALGEBRA_PRESENTED_MODULE_REFERENCE_PROFILE.algorithmRevision
);

export function algebraPresentedModuleReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(): AlgebraPresentedModuleReferenceOperations<P, C, I> {
    const mapApplyInputSchema = inputSchema<
        AlgebraPresentedModuleMapApplyInput<P, C, I>
    >('algebra.presented-module.map-apply-input', value => Object.freeze({
        map: value.map as AlgebraPresentedAlgebraModuleSemilinearMap<P, C, I>,
        element: value.element as AlgebraPresentedAlgebraModuleElement<P, C, I>
    }));
    const baseChangeInputSchema = inputSchema<
        AlgebraPresentedModuleBaseChangeInput<P, C, I>
    >('algebra.presented-module.base-change-input', value => Object.freeze({
        scalarMap: value.scalarMap as AlgebraPresentedAlgebraMap<P, C, I>,
        module: value.module as AlgebraPresentedAlgebraModule<P, C, I>
    }));
    const localizationInputSchema = inputSchema<
        AlgebraPresentedModuleLocalizationInput<P, C, I>
    >('algebra.presented-module.localization-input', value => Object.freeze({
        module: value.module as AlgebraPresentedAlgebraModule<P, C, I>,
        element: value.element as AlgebraQuotientElement<P, C, I>
    }));
    const cechInputSchema = inputSchema<AlgebraQuasiCoherentCechInput<P, C, I>>(
        'algebra.presented-module.cech-input',
        value => Object.freeze({
            presentation: value.presentation as
                AlgebraAffineQuasiCoherentPresentation<P, C, I>,
            cover: value.cover as AlgebraAffineCover<P, C, I>
        })
    );
    const mapApply = defineAlgebraOperation({
        id: 'algebra.presented-module.map-apply',
        revision: ALGEBRA_PRESENTED_MODULE_REFERENCE_PROFILE.revision,
        input: mapApplyInputSchema,
        output: wholeSchema<AlgebraPresentedAlgebraModuleElement<P, C, I>>(
            'algebra.presented-module.element-result',
            'algebra-presented-algebra-module-element'
        )
    });
    const baseChange = defineAlgebraOperation({
        id: 'algebra.presented-module.base-change',
        revision: ALGEBRA_PRESENTED_MODULE_REFERENCE_PROFILE.revision,
        input: baseChangeInputSchema,
        output: wholeSchema<AlgebraPresentedModuleBaseChange<P, C, I>>(
            'algebra.presented-module.base-change-result',
            'algebra-presented-module-base-change'
        )
    });
    const localization = defineAlgebraOperation({
        id: 'algebra.presented-module.localization',
        revision: ALGEBRA_PRESENTED_MODULE_REFERENCE_PROFILE.revision,
        input: localizationInputSchema,
        output: wholeSchema<AlgebraPresentedModuleLocalization<P, C, I>>(
            'algebra.presented-module.localization-result',
            'algebra-presented-module-localization'
        )
    });
    const cech = defineAlgebraOperation({
        id: 'algebra.presented-module.quasicoherent-cech',
        revision: ALGEBRA_PRESENTED_MODULE_REFERENCE_PROFILE.revision,
        input: cechInputSchema,
        output: wholeSchema<AlgebraAffineQuasiCoherentCechDiagram<P, C, I>>(
            'algebra.presented-module.cech-result',
            'algebra-affine-quasicoherent-cech-diagram'
        )
    });
    const implementations = Object.freeze([
        defineAlgebraReferenceImplementation({
            operation: mapApply,
            algorithm: algorithm('presented-module-map-apply'),
            execute: input => algebraPresentedAlgebraModuleSemilinearMapApply(
                input.map,
                input.element
            )
        }),
        defineAlgebraReferenceImplementation({
            operation: baseChange,
            algorithm: algorithm('presented-module-base-change'),
            execute: (input, context) => algebraPresentedModuleBaseChange(
                input.scalarMap,
                input.module,
                { context }
            )
        }),
        defineAlgebraReferenceImplementation({
            operation: localization,
            algorithm: algorithm('presented-module-localization'),
            execute: (input, context) => algebraPresentedModuleLocalization(
                input.module,
                input.element,
                {
                    localization: { context },
                    module: { context }
                }
            )
        }),
        defineAlgebraReferenceImplementation({
            operation: cech,
            algorithm: algorithm('presented-module-quasicoherent-cech'),
            execute: (input, context) =>
                algebraAffineQuasiCoherentCechDiagram(
                    input.presentation,
                    input.cover,
                    { context }
                )
        })
    ]);
    return Object.freeze({
        mapApplyInputSchema,
        baseChangeInputSchema,
        localizationInputSchema,
        cechInputSchema,
        mapApply,
        baseChange,
        localization,
        cech,
        implementations
    });
}
