/** Proof–CAS adapters and ordered adoption for bounded complex laws. */

import {
    AlgebraFormalAssumptionSource,
    appendAlgebraFormalAssumption,
    serializeAlgebraFormalAssumptionSource
} from './algebra_formal_assumption_source';
import {
    ALGEBRA_FORMAL_BOUNDED_COMPLEX_PROFILE,
    AlgebraFormalBoundedChainMapRealization,
    AlgebraFormalBoundedComplexRealization,
    defineAlgebraFormalBoundedChainMapRealization,
    defineAlgebraFormalBoundedComplexRealization
} from './algebra_formal_bounded_complex';
import {
    AlgebraFormalComputationAdapter,
    AlgebraFormalComputationInterpretationInput,
    AlgebraFormalDelegationError,
    defineAlgebraFormalComputationAdapter
} from './algebra_formal_delegation';
import {
    AffineFormalPolynomialReifier
} from './algebra_formal_reifier';
import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    AlgebraPolynomialBoundedChainMap,
    AlgebraPolynomialBoundedFreeComplex
} from './algebra_polynomial_bounded_complex';
import {
    AlgebraPolynomialBoundedChainMapInput,
    AlgebraPolynomialBoundedComplexInput,
    AlgebraPolynomialBoundedComplexReferenceOperations,
    algebraPolynomialBoundedComplexReferenceOperations,
    serializeAlgebraPolynomialBoundedChainMap,
    serializeAlgebraPolynomialBoundedFreeComplex
} from './algebra_polynomial_bounded_complex_reference_operations';
import {
    AlgebraReferenceImplementation,
    createAlgebraTypeScriptReferenceEngine
} from './algebra_reference_engine';
import {
    CoreProofArtifactFingerprint
} from './proof_document';
import {
    KernelExpression,
    kernelExpressionEquals,
    provenance
} from './kernel';
import {
    serializeCoreExpression
} from './core_serialization';
import {
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';
import {
    coreProofPlanHole
} from './proof_plan';
import {
    runAlgebraFormalWorkflow,
    trustAlgebraFormalWorkflow
} from './algebra_formal_workflow';

export const ALGEBRA_FORMAL_BOUNDED_COMPLEX_DELEGATION_PROFILE = Object.freeze({
    revision: 'emdash-formal-bounded-complex-delegation-v1' as const,
    order: 'complex-laws-then-chain-map-squares' as const,
    classification: 'computed-equation' as const,
    exactWholeOutput: true as const,
    addsCoreOwner: false as const,
    performsIo: false as const
});

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

const invalid = (path: string, message: string): never => {
    throw new AlgebraFormalDelegationError('INVALID_REALIZATION', path, message);
};

const goalTarget = (
    actual: KernelExpression,
    expected: KernelExpression,
    path: string
): void => {
    if (!kernelExpressionEquals(actual, expected)) {
        throw new AlgebraFormalDelegationError(
            'CLAIM_TARGET_MISMATCH',
            path,
            'Goal differs from the selected bounded-complex equation'
        );
    }
};

export interface AlgebraFormalBoundedComplexConditionBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly operations: AlgebraPolynomialBoundedComplexReferenceOperations<P, C, I>;
    readonly realization: AlgebraFormalBoundedComplexRealization<P, C, I>;
    readonly conditionIndex: number;
    readonly adapter: AlgebraFormalComputationAdapter<
        AlgebraFormalBoundedComplexRealization<P, C, I>,
        AlgebraPolynomialBoundedComplexInput<P, C, I>,
        AlgebraPolynomialBoundedFreeComplex<P, C, I>
    >;
}

export function algebraFormalBoundedComplexConditionBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialBoundedFreeComplex<P, C, I>;
    readonly conditionIndex: number;
}): AlgebraFormalBoundedComplexConditionBundle<P, C, I> {
    if (
        !Number.isSafeInteger(input.conditionIndex) ||
        input.conditionIndex < 0 ||
        input.conditionIndex >= input.selected.conditions.length
    ) return invalid('boundedComplex.conditionIndex', 'Condition index is invalid');
    const operations = algebraPolynomialBoundedComplexReferenceOperations<P, C, I>();
    const realization = defineAlgebraFormalBoundedComplexRealization(input);
    const condition = realization.conditions[input.conditionIndex];
    const adapter = defineAlgebraFormalComputationAdapter({
        id: `proof-cas.bounded-complex-condition/` +
            input.selected.ring.identity.id,
        revision: input.selected.ring.identity.revision,
        operation: operations.complex,
        normalizeRealization(value, path) {
            if (!record(value) || value.profileRevision !==
                ALGEBRA_FORMAL_BOUNDED_COMPLEX_PROFILE.complexRevision) {
                return invalid(path, 'Expected one current complex realization');
            }
            const candidate = value as unknown as typeof realization;
            const expected = defineAlgebraFormalBoundedComplexRealization({
                reifier: candidate.reifier,
                selected: candidate.selected
            });
            if (
                candidate.selectedOutputData !== expected.selectedOutputData ||
                candidate.conditions.length !== expected.conditions.length ||
                !candidate.conditions.every((entry, index) =>
                    kernelExpressionEquals(
                        entry.claimType,
                        expected.conditions[index].claimType
                    )
                )
            ) return invalid(path, 'Complex realization differs from its laws');
            return candidate;
        },
        serializeRealization: value => serializeCoreLfWorkspaceCanonicalJson({
            selected: value.selectedOutputData,
            conditionIndex: input.conditionIndex,
            claim: serializeCoreExpression(
                value.conditions[input.conditionIndex].claimType
            )
        }, 'formalBoundedComplexConditionRealization'),
        acquire: (goal, value) => {
            goalTarget(
                goal.target,
                value.conditions[input.conditionIndex].claimType,
                'boundedComplex.goal'
            );
            return Object.freeze({
                terms: value.selected.terms.map(term => term.module),
                differentials: value.selected.differentials.map(entry => entry.map)
            });
        },
        serializeInput: value => serializeCoreLfWorkspaceCanonicalJson({
            ranks: value.terms.map(term => term.rank),
            differentialCount: value.differentials.length
        }, 'formalBoundedComplexInput'),
        serializeOutput: serializeAlgebraPolynomialBoundedFreeComplex,
        interpret: ({ goal, realization: value, computed }):
            AlgebraFormalComputationInterpretationInput =>
            serializeAlgebraPolynomialBoundedFreeComplex(computed.value) ===
                value.selectedOutputData &&
            computed.value.conditions[input.conditionIndex]?.zero === true
                ? {
                    kind: 'claim',
                    summary: `selected d^2 law in degree ` +
                        value.conditions[input.conditionIndex].upperDegree,
                    claimType: goal.target
                }
                : {
                    kind: 'observation',
                    summary: 'complex has a changed or nonzero adjacent composite'
                }
    });
    return Object.freeze({
        operations,
        realization,
        conditionIndex: input.conditionIndex,
        adapter
    });
}

export interface AlgebraFormalBoundedChainMapSquareBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly operations: AlgebraPolynomialBoundedComplexReferenceOperations<P, C, I>;
    readonly realization: AlgebraFormalBoundedChainMapRealization<P, C, I>;
    readonly squareIndex: number;
    readonly adapter: AlgebraFormalComputationAdapter<
        AlgebraFormalBoundedChainMapRealization<P, C, I>,
        AlgebraPolynomialBoundedChainMapInput<P, C, I>,
        AlgebraPolynomialBoundedChainMap<P, C, I>
    >;
}

export function algebraFormalBoundedChainMapSquareBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialBoundedChainMap<P, C, I>;
    readonly squareIndex: number;
}): AlgebraFormalBoundedChainMapSquareBundle<P, C, I> {
    if (
        !Number.isSafeInteger(input.squareIndex) ||
        input.squareIndex < 0 ||
        input.squareIndex >= input.selected.squares.length
    ) return invalid('boundedChainMap.squareIndex', 'Square index is invalid');
    const operations = algebraPolynomialBoundedComplexReferenceOperations<P, C, I>();
    const realization = defineAlgebraFormalBoundedChainMapRealization(input);
    const adapter = defineAlgebraFormalComputationAdapter({
        id: `proof-cas.bounded-chain-map-square/` +
            input.selected.source.ring.identity.id,
        revision: input.selected.source.ring.identity.revision,
        operation: operations.chainMap,
        normalizeRealization(value, path) {
            if (!record(value) || value.profileRevision !==
                ALGEBRA_FORMAL_BOUNDED_COMPLEX_PROFILE.chainMapRevision) {
                return invalid(path, 'Expected one current chain-map realization');
            }
            const candidate = value as unknown as typeof realization;
            const expected = defineAlgebraFormalBoundedChainMapRealization({
                reifier: candidate.reifier,
                selected: candidate.selected
            });
            if (
                candidate.selectedOutputData !== expected.selectedOutputData ||
                candidate.squares.length !== expected.squares.length ||
                !candidate.squares.every((entry, index) =>
                    kernelExpressionEquals(
                        entry.claimType,
                        expected.squares[index].claimType
                    )
                )
            ) return invalid(path, 'Chain-map realization differs from its laws');
            return candidate;
        },
        serializeRealization: value => serializeCoreLfWorkspaceCanonicalJson({
            selected: value.selectedOutputData,
            squareIndex: input.squareIndex,
            claim: serializeCoreExpression(value.squares[input.squareIndex].claimType)
        }, 'formalBoundedChainMapSquareRealization'),
        acquire: (goal, value) => {
            goalTarget(
                goal.target,
                value.squares[input.squareIndex].claimType,
                'boundedChainMap.goal'
            );
            return Object.freeze({
                source: value.selected.source,
                target: value.selected.target,
                components: value.selected.components.map(entry => entry.map)
            });
        },
        serializeInput: value => serializeCoreLfWorkspaceCanonicalJson({
            length: value.source.length,
            componentCount: value.components.length
        }, 'formalBoundedChainMapInput'),
        serializeOutput: serializeAlgebraPolynomialBoundedChainMap,
        interpret: ({ goal, realization: value, computed }):
            AlgebraFormalComputationInterpretationInput =>
            serializeAlgebraPolynomialBoundedChainMap(computed.value) ===
                value.selectedOutputData &&
            computed.value.squares[input.squareIndex]?.commutes === true &&
            computed.value.source.isComplex && computed.value.target.isComplex
                ? {
                    kind: 'claim',
                    summary: `selected chain square in degree ${input.squareIndex + 1}`,
                    claimType: goal.target
                }
                : {
                    kind: 'observation',
                    summary: 'chain map has a changed or noncommuting square'
                }
    });
    return Object.freeze({
        operations,
        realization,
        squareIndex: input.squareIndex,
        adapter
    });
}

export interface AlgebraFormalAdoptedBoundedComplexRecipe<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly realization: AlgebraFormalBoundedComplexRealization<P, C, I>;
    readonly lawTerms: readonly KernelExpression[];
}

export interface AlgebraFormalAdoptedBoundedChainMapRecipe<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly realization: AlgebraFormalBoundedChainMapRealization<P, C, I>;
    readonly lawTerms: readonly KernelExpression[];
}

export interface AlgebraFormalBoundedComplexBatchResult<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly source: AlgebraFormalAssumptionSource;
    readonly complex: AlgebraFormalAdoptedBoundedComplexRecipe<P, C, I>;
    readonly chainMaps: readonly AlgebraFormalAdoptedBoundedChainMapRecipe<P, C, I>[];
}

export const serializeAlgebraFormalBoundedComplexBatchResult = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraFormalBoundedComplexBatchResult<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        source: serializeAlgebraFormalAssumptionSource(value.source),
        complex: {
            selected: value.complex.realization.selectedOutputData,
            laws: value.complex.lawTerms.map(term => serializeCoreExpression(term))
        },
        chainMaps: value.chainMaps.map(recipe => ({
            selected: recipe.realization.selectedOutputData,
            laws: recipe.lawTerms.map(term => serializeCoreExpression(term))
        }))
    }, 'formalBoundedComplexBatchResult');

const stem = (value: string): string => {
    const normalized = value.replace(/[^A-Za-z0-9_]/gu, '_');
    if (/^[A-Za-z][A-Za-z0-9_]*$/u.test(normalized)) return normalized;
    throw new Error('Bounded-complex artifact ID must begin with a letter');
};

export async function delegateAlgebraFormalBoundedComplexLaws<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly artifactId: string;
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly complex: AlgebraPolynomialBoundedFreeComplex<P, C, I>;
    readonly chainMaps: readonly AlgebraPolynomialBoundedChainMap<P, C, I>[];
    readonly source: AlgebraFormalAssumptionSource;
    readonly fingerprint: (goalId: string) => CoreProofArtifactFingerprint;
    readonly decisionEvidence: (goalId: string) => string;
}): Promise<AlgebraFormalBoundedComplexBatchResult<P, C, I>> {
    let source = input.source;
    const idStem = stem(input.artifactId);
    const complexRealization = defineAlgebraFormalBoundedComplexRealization({
        reifier: input.reifier,
        selected: input.complex
    });
    const complexLawTerms: KernelExpression[] = [];
    const mapRecipes: AlgebraFormalAdoptedBoundedChainMapRecipe<P, C, I>[] = [];
    const document = (goalId: string, target: KernelExpression) => Object.freeze({
        moduleId: `${input.artifactId}.assumptions`,
        declarationId: goalId,
        environment: source.environment,
        type: target,
        plan: coreProofPlanHole(goalId, {
            provenance: provenance('derived', `generated goal ${goalId}`),
            expectation: { contextDepth: 0, target }
        }),
        provenance: provenance('derived', `generated root ${goalId}`),
        fingerprint: input.fingerprint(goalId)
    });
    const adopt = async <R, Input, Output>(args: {
        readonly goalId: string;
        readonly name: string;
        readonly target: KernelExpression;
        readonly adapter: AlgebraFormalComputationAdapter<R, Input, Output>;
        readonly realization: R;
        readonly implementations: readonly AlgebraReferenceImplementation[];
    }): Promise<KernelExpression> => {
        const engine = createAlgebraTypeScriptReferenceEngine({
            id: `${input.artifactId}.reference`,
            revision: 'v1',
            implementations: args.implementations
        });
        const run = await runAlgebraFormalWorkflow({
            document: document(args.goalId, args.target),
            goalId: args.goalId,
            adapter: args.adapter,
            realization: args.realization,
            engine
        });
        const adoption = trustAlgebraFormalWorkflow({
            run,
            assumptionName: args.name,
            decision: {
                kind: 'trust-exact-algebra-computation',
                evidence: input.decisionEvidence(args.goalId)
            }
        });
        source = appendAlgebraFormalAssumption({
            source,
            adoption,
            classification: 'computed-equation'
        });
        return source.entries[source.entries.length - 1].reference;
    };
    for (let index = 0; index < input.complex.conditions.length; index++) {
        const bundle = algebraFormalBoundedComplexConditionBundle({
            reifier: input.reifier,
            selected: input.complex,
            conditionIndex: index
        });
        complexLawTerms.push(await adopt({
            goalId: `${input.artifactId}-complex-${index}`,
            name: `${idStem}_complex_${index}`,
            target: bundle.realization.conditions[index].claimType,
            adapter: bundle.adapter,
            realization: bundle.realization,
            implementations: bundle.operations.implementations
        }));
    }
    for (let mapIndex = 0; mapIndex < input.chainMaps.length; mapIndex++) {
        const map = input.chainMaps[mapIndex];
        const realization = defineAlgebraFormalBoundedChainMapRealization({
            reifier: input.reifier,
            selected: map
        });
        const laws: KernelExpression[] = [];
        for (let squareIndex = 0; squareIndex < map.squares.length; squareIndex++) {
            const bundle = algebraFormalBoundedChainMapSquareBundle({
                reifier: input.reifier,
                selected: map,
                squareIndex
            });
            laws.push(await adopt({
                goalId: `${input.artifactId}-map-${mapIndex}-${squareIndex}`,
                name: `${idStem}_map_${mapIndex}_${squareIndex}`,
                target: bundle.realization.squares[squareIndex].claimType,
                adapter: bundle.adapter,
                realization: bundle.realization,
                implementations: bundle.operations.implementations
            }));
        }
        mapRecipes.push(Object.freeze({ realization, lawTerms: Object.freeze(laws) }));
    }
    return Object.freeze({
        source,
        complex: Object.freeze({
            realization: complexRealization,
            lawTerms: Object.freeze(complexLawTerms)
        }),
        chainMaps: Object.freeze(mapRecipes)
    });
}
