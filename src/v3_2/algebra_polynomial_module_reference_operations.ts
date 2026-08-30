/** Native operations for polynomial-module Gröbner and resolution pipelines. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import {
    AlgebraOperation,
    AlgebraRuntimeSchema,
    algebraAlgorithmIdentity,
    defineAlgebraOperation,
    defineAlgebraRuntimeSchema
} from './algebra_engine';
import {
    AlgebraPolynomialFreeModule,
    AlgebraPolynomialModuleGroebnerBasis,
    AlgebraPolynomialModuleSchreyerSyzygies,
    AlgebraPolynomialSubmodule,
    algebraPolynomialModuleGroebnerBasis,
    algebraPolynomialModuleSchreyerSyzygies,
    algebraPolynomialModuleVectorSchema,
    algebraPolynomialSubmodule
} from './algebra_polynomial_module';
import {
    AlgebraPolynomialSchreyerResolution,
    algebraPolynomialSchreyerResolution,
    algebraPresentedPolynomialModule
} from './algebra_polynomial_presentation';
import {
    AlgebraReferenceImplementation,
    defineAlgebraReferenceImplementation
} from './algebra_reference_engine';

export const ALGEBRA_POLYNOMIAL_MODULE_REFERENCE_PROFILE = Object.freeze({
    revision: 'emdash-algebra-polynomial-module-reference-v1' as const,
    algorithmRevision: 'typescript-module-buchberger-schreyer-v1' as const,
    wholeResults: true as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export interface AlgebraPolynomialResolutionInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly relations: AlgebraPolynomialSubmodule<P, C, I>;
    readonly maximumLength: number;
}

export interface AlgebraPolynomialModuleReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly submoduleSchema: AlgebraRuntimeSchema<AlgebraPolynomialSubmodule<P, C, I>>;
    readonly basisSchema: AlgebraRuntimeSchema<
        AlgebraPolynomialModuleGroebnerBasis<P, C, I>
    >;
    readonly groebner: AlgebraOperation<
        AlgebraPolynomialSubmodule<P, C, I>,
        AlgebraPolynomialModuleGroebnerBasis<P, C, I>
    >;
    readonly syzygies: AlgebraOperation<
        AlgebraPolynomialModuleGroebnerBasis<P, C, I>,
        AlgebraPolynomialModuleSchreyerSyzygies<P, C, I>
    >;
    readonly resolution: AlgebraOperation<
        AlgebraPolynomialResolutionInput<P, C, I>,
        AlgebraPolynomialSchreyerResolution<P, C, I>
    >;
    readonly implementations: readonly AlgebraReferenceImplementation[];
}

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

const algorithm = (id: string) => algebraAlgorithmIdentity(
    `algebra.typescript-reference/${id}`,
    ALGEBRA_POLYNOMIAL_MODULE_REFERENCE_PROFILE.algorithmRevision
);

export function algebraPolynomialModuleReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(module: AlgebraPolynomialFreeModule<P, C, I>):
    AlgebraPolynomialModuleReferenceOperations<P, C, I> {
    const suffix = module.identity.id;
    const vectorSchema = algebraPolynomialModuleVectorSchema(module);
    const submoduleSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialSubmodule<P, C, I>
    >({
        id: `algebra.polynomial-submodule/${suffix}`,
        revision: module.identity.revision,
        normalize(value: unknown, path: string) {
            if (
                !record(value) ||
                value.kind !== 'algebra-polynomial-submodule' ||
                !Array.isArray(value.generators)
            ) throw new Error(`polynomial submodule expected at ${path}`);
            return algebraPolynomialSubmodule(
                module,
                value.generators.map((generator, index) =>
                    vectorSchema.normalize(generator, `${path}.generators[${index}]`)
                )
            );
        }
    });
    const basisSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialModuleGroebnerBasis<P, C, I>
    >({
        id: `algebra.polynomial-module-groebner/${suffix}`,
        revision: module.identity.revision,
        normalize(value: unknown, path: string) {
            if (
                !record(value) ||
                value.kind !== 'algebra-polynomial-module-groebner-basis' ||
                !Array.isArray(value.basis) ||
                !Array.isArray(value.transformations)
            ) throw new Error(`module Groebner basis expected at ${path}`);
            submoduleSchema.normalize(value.submodule, `${path}.submodule`);
            value.basis.forEach((entry, index) =>
                vectorSchema.normalize(entry, `${path}.basis[${index}]`)
            );
            return value as unknown as AlgebraPolynomialModuleGroebnerBasis<P, C, I>;
        }
    });
    const syzygySchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialModuleSchreyerSyzygies<P, C, I>
    >({
        id: `algebra.polynomial-module-syzygies/${suffix}`,
        revision: module.identity.revision,
        normalize(value: unknown, path: string) {
            if (!record(value) || value.kind !==
                'algebra-polynomial-module-schreyer-syzygies') {
                throw new Error(`Schreyer syzygies expected at ${path}`);
            }
            basisSchema.normalize(value.basis, `${path}.basis`);
            return value as unknown as AlgebraPolynomialModuleSchreyerSyzygies<P, C, I>;
        }
    });
    const resolutionInputSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialResolutionInput<P, C, I>
    >({
        id: `algebra.polynomial-module-resolution-input/${suffix}`,
        revision: module.identity.revision,
        normalize(value: unknown, path: string) {
            if (!record(value) || !Number.isSafeInteger(value.maximumLength)) {
                throw new Error(`resolution input expected at ${path}`);
            }
            return Object.freeze({
                relations: submoduleSchema.normalize(
                    value.relations,
                    `${path}.relations`
                ),
                maximumLength: value.maximumLength as number
            });
        }
    });
    const resolutionSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialSchreyerResolution<P, C, I>
    >({
        id: `algebra.polynomial-module-resolution/${suffix}`,
        revision: module.identity.revision,
        normalize(value: unknown, path: string) {
            if (!record(value) || value.kind !==
                'algebra-polynomial-schreyer-resolution') {
                throw new Error(`Schreyer resolution expected at ${path}`);
            }
            return value as unknown as AlgebraPolynomialSchreyerResolution<P, C, I>;
        }
    });
    const groebner = defineAlgebraOperation({
        id: `algebra.polynomial-module.groebner/${suffix}`,
        revision: module.identity.revision,
        input: submoduleSchema,
        output: basisSchema
    });
    const syzygies = defineAlgebraOperation({
        id: `algebra.polynomial-module.syzygies/${suffix}`,
        revision: module.identity.revision,
        input: basisSchema,
        output: syzygySchema
    });
    const resolution = defineAlgebraOperation({
        id: `algebra.polynomial-module.resolution/${suffix}`,
        revision: module.identity.revision,
        input: resolutionInputSchema,
        output: resolutionSchema
    });
    const implementations = Object.freeze([
        defineAlgebraReferenceImplementation({
            operation: groebner,
            algorithm: algorithm(groebner.identity.id),
            execute: (input, context) => algebraPolynomialModuleGroebnerBasis(
                input,
                { context }
            )
        }),
        defineAlgebraReferenceImplementation({
            operation: syzygies,
            algorithm: algorithm(syzygies.identity.id),
            execute: input => algebraPolynomialModuleSchreyerSyzygies(input)
        }),
        defineAlgebraReferenceImplementation({
            operation: resolution,
            algorithm: algorithm(resolution.identity.id),
            execute: input => algebraPolynomialSchreyerResolution(
                algebraPresentedPolynomialModule(input.relations),
                input.maximumLength
            )
        })
    ]);
    return Object.freeze({
        submoduleSchema,
        basisSchema,
        groebner,
        syzygies,
        resolution,
        implementations
    });
}
