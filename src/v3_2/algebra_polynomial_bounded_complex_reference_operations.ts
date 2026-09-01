/** Native operations and serializers for polynomial bounded complexes. */

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
    AlgebraPolynomialBoundedChainMap,
    AlgebraPolynomialBoundedFreeComplex,
    algebraPolynomialBoundedChainMap,
    algebraPolynomialBoundedFreeComplex,
    algebraPolynomialBoundedFreeComplexFromSchreyer
} from './algebra_polynomial_bounded_complex';
import {
    AlgebraPolynomialFreeModule
} from './algebra_polynomial_module';
import {
    AlgebraPolynomialModuleMap,
    AlgebraPolynomialSchreyerResolution
} from './algebra_polynomial_presentation';
import {
    AlgebraReferenceImplementation,
    defineAlgebraReferenceImplementation
} from './algebra_reference_engine';
import {
    algebraPolynomialText
} from './algebra_polynomial';
import {
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';

export const ALGEBRA_POLYNOMIAL_BOUNDED_COMPLEX_REFERENCE_PROFILE =
    Object.freeze({
        revision:
            'emdash-algebra-polynomial-bounded-complex-reference-v1' as const,
        algorithmRevision: 'typescript-polynomial-bounded-complex-v1' as const,
        wholeResults: true as const,
        nodeBuiltinDependency: false as const,
        performsIo: false as const
    });

export interface AlgebraPolynomialBoundedComplexInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly terms: readonly AlgebraPolynomialFreeModule<P, C, I>[];
    readonly differentials: readonly AlgebraPolynomialModuleMap<P, C, I>[];
}

export interface AlgebraPolynomialBoundedChainMapInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly source: AlgebraPolynomialBoundedFreeComplex<P, C, I>;
    readonly target: AlgebraPolynomialBoundedFreeComplex<P, C, I>;
    readonly components: readonly AlgebraPolynomialModuleMap<P, C, I>[];
}

export interface AlgebraPolynomialBoundedComplexReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly complexInputSchema:
        AlgebraRuntimeSchema<AlgebraPolynomialBoundedComplexInput<P, C, I>>;
    readonly resolutionSchema:
        AlgebraRuntimeSchema<AlgebraPolynomialSchreyerResolution<P, C, I>>;
    readonly chainMapInputSchema:
        AlgebraRuntimeSchema<AlgebraPolynomialBoundedChainMapInput<P, C, I>>;
    readonly complex: AlgebraOperation<
        AlgebraPolynomialBoundedComplexInput<P, C, I>,
        AlgebraPolynomialBoundedFreeComplex<P, C, I>
    >;
    readonly schreyerComplex: AlgebraOperation<
        AlgebraPolynomialSchreyerResolution<P, C, I>,
        AlgebraPolynomialBoundedFreeComplex<P, C, I>
    >;
    readonly chainMap: AlgebraOperation<
        AlgebraPolynomialBoundedChainMapInput<P, C, I>,
        AlgebraPolynomialBoundedChainMap<P, C, I>
    >;
    readonly implementations: readonly AlgebraReferenceImplementation[];
}

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

const moduleValue = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    value: unknown,
    path: string
): AlgebraPolynomialFreeModule<P, C, I> => {
    if (!record(value) || value.kind !== 'polynomial-free-module') {
        throw new Error(`polynomial free module expected at ${path}`);
    }
    return value as unknown as AlgebraPolynomialFreeModule<P, C, I>;
};

const mapValue = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    value: unknown,
    path: string
): AlgebraPolynomialModuleMap<P, C, I> => {
    if (
        !record(value) ||
        value.kind !== 'algebra-polynomial-module-map' ||
        !Array.isArray(value.columns)
    ) throw new Error(`polynomial module map expected at ${path}`);
    return value as unknown as AlgebraPolynomialModuleMap<P, C, I>;
};

const complexValue = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    value: unknown,
    path: string
): AlgebraPolynomialBoundedFreeComplex<P, C, I> => {
    if (
        !record(value) ||
        value.kind !== 'algebra-polynomial-bounded-free-complex' ||
        !Array.isArray(value.terms) ||
        !Array.isArray(value.differentials)
    ) throw new Error(`polynomial bounded complex expected at ${path}`);
    return value as unknown as AlgebraPolynomialBoundedFreeComplex<P, C, I>;
};

const mapData = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    value: AlgebraPolynomialModuleMap<P, C, I>
) => Object.freeze({
    sourceRank: value.source.rank,
    targetRank: value.target.rank,
    columns: value.columns.map(column =>
        column.components.map(algebraPolynomialText)
    )
});

export const serializeAlgebraPolynomialBoundedFreeComplex = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialBoundedFreeComplex<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        kind: value.kind,
        length: value.length,
        terms: value.terms.map(term => Object.freeze({
            degree: term.degree,
            rank: term.module.rank,
            order: term.module.termOrder
        })),
        differentials: value.differentials.map(entry => Object.freeze({
            degree: entry.degree,
            map: mapData(entry.map)
        })),
        conditions: value.conditions.map(condition => Object.freeze({
            upperDegree: condition.upperDegree,
            composite: mapData(condition.composite),
            zero: condition.zero
        })),
        isComplex: value.isComplex,
        schreyer: value.schreyerSource === undefined
            ? null
            : {
                complete: value.schreyerSource.complete,
                maximumLength: value.schreyerSource.maximumLength,
                resolutionLength: value.schreyerSource.resolution.length
            }
    }, 'polynomialBoundedFreeComplex');

export const serializeAlgebraPolynomialBoundedChainMap = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialBoundedChainMap<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        kind: value.kind,
        source: serializeAlgebraPolynomialBoundedFreeComplex(value.source),
        target: serializeAlgebraPolynomialBoundedFreeComplex(value.target),
        components: value.components.map(component => Object.freeze({
            degree: component.degree,
            map: mapData(component.map)
        })),
        squares: value.squares.map((square, index) => Object.freeze({
            degree: index + 1,
            left: mapData(square.targetAfterComponent),
            right: mapData(square.componentAfterSource),
            commutes: square.commutes
        })),
        isChainMap: value.isChainMap
    }, 'polynomialBoundedChainMap');

const wholeSchema = <T extends { readonly kind: string }>(
    id: string,
    kind: T['kind']
): AlgebraRuntimeSchema<T> => defineAlgebraRuntimeSchema({
    id,
    revision: ALGEBRA_POLYNOMIAL_BOUNDED_COMPLEX_REFERENCE_PROFILE.revision,
    normalize(value: unknown, path: string) {
        if (!record(value) || value.kind !== kind) {
            throw new Error(`${kind} expected at ${path}`);
        }
        return value as unknown as T;
    }
});

const algorithm = (id: string) => algebraAlgorithmIdentity(
    `algebra.typescript-reference/${id}`,
    ALGEBRA_POLYNOMIAL_BOUNDED_COMPLEX_REFERENCE_PROFILE.algorithmRevision
);

export function algebraPolynomialBoundedComplexReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(): AlgebraPolynomialBoundedComplexReferenceOperations<P, C, I> {
    const revision = ALGEBRA_POLYNOMIAL_BOUNDED_COMPLEX_REFERENCE_PROFILE.revision;
    const complexInputSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialBoundedComplexInput<P, C, I>
    >({
        id: 'algebra.polynomial-bounded-complex-input',
        revision,
        normalize(value: unknown, path: string) {
            if (!record(value) || !Array.isArray(value.terms) ||
                !Array.isArray(value.differentials)) {
                throw new Error(`bounded complex input expected at ${path}`);
            }
            return Object.freeze({
                terms: Object.freeze(value.terms.map((term, index) =>
                    moduleValue<P, C, I>(term, `${path}.terms[${index}]`)
                )),
                differentials: Object.freeze(value.differentials.map(
                    (map, index) => mapValue<P, C, I>(
                        map,
                        `${path}.differentials[${index}]`
                    )
                ))
            });
        }
    });
    const resolutionSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialSchreyerResolution<P, C, I>
    >({
        id: 'algebra.polynomial-bounded-complex-resolution-input',
        revision,
        normalize(value: unknown, path: string) {
            if (!record(value) ||
                value.kind !== 'algebra-polynomial-schreyer-resolution') {
                throw new Error(`Schreyer resolution expected at ${path}`);
            }
            return value as unknown as AlgebraPolynomialSchreyerResolution<P, C, I>;
        }
    });
    const chainMapInputSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialBoundedChainMapInput<P, C, I>
    >({
        id: 'algebra.polynomial-bounded-chain-map-input',
        revision,
        normalize(value: unknown, path: string) {
            if (!record(value) || !Array.isArray(value.components)) {
                throw new Error(`bounded chain map input expected at ${path}`);
            }
            return Object.freeze({
                source: complexValue<P, C, I>(value.source, `${path}.source`),
                target: complexValue<P, C, I>(value.target, `${path}.target`),
                components: Object.freeze(value.components.map((map, index) =>
                    mapValue<P, C, I>(map, `${path}.components[${index}]`)
                ))
            });
        }
    });
    const complex = defineAlgebraOperation({
        id: 'algebra.polynomial-bounded-complex.construct',
        revision,
        input: complexInputSchema,
        output: wholeSchema<AlgebraPolynomialBoundedFreeComplex<P, C, I>>(
            'algebra.polynomial-bounded-complex-result',
            'algebra-polynomial-bounded-free-complex'
        )
    });
    const schreyerComplex = defineAlgebraOperation({
        id: 'algebra.polynomial-bounded-complex.from-schreyer',
        revision,
        input: resolutionSchema,
        output: complex.output
    });
    const chainMap = defineAlgebraOperation({
        id: 'algebra.polynomial-bounded-complex.chain-map',
        revision,
        input: chainMapInputSchema,
        output: wholeSchema<AlgebraPolynomialBoundedChainMap<P, C, I>>(
            'algebra.polynomial-bounded-chain-map-result',
            'algebra-polynomial-bounded-chain-map'
        )
    });
    const implementations = Object.freeze([
        defineAlgebraReferenceImplementation({
            operation: complex,
            algorithm: algorithm(complex.identity.id),
            execute: input => algebraPolynomialBoundedFreeComplex(input)
        }),
        defineAlgebraReferenceImplementation({
            operation: schreyerComplex,
            algorithm: algorithm(schreyerComplex.identity.id),
            execute: algebraPolynomialBoundedFreeComplexFromSchreyer
        }),
        defineAlgebraReferenceImplementation({
            operation: chainMap,
            algorithm: algorithm(chainMap.identity.id),
            execute: input => algebraPolynomialBoundedChainMap(input)
        })
    ]);
    return Object.freeze({
        complexInputSchema,
        resolutionSchema,
        chainMapInputSchema,
        complex,
        schreyerComplex,
        chainMap,
        implementations
    });
}
