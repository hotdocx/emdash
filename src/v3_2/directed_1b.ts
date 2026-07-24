/**
 * Reviewed DIRECTED-1B integration.
 *
 * The exact approved proposal is compiled into five LF declarations and one
 * catalog-local runtime component. Four owners are opaque active imports;
 * `Sigma_catd_transport_func` is retained as a checked transparent mirror.
 * The component executes the three approved Foundation 1 facade
 * prerequisites and the one approved Foundation 2 decoded Cat-hom rule
 * before the three DIRECTED-1B-owned rules. Neither the default LF checker
 * nor the frozen MVP runtime imports this module or acquires any of them.
 */

import {
    CORE_DIRECTED_1B_PROPOSAL,
    CoreDirected1bCandidateOwnerId,
    CoreDirected1bExpression,
    CoreDirected1bExpressionOwnerId,
    CoreDirected1bOwnerProposal,
    CoreDirected1bRuntimeRuleId,
    CoreDirected1bRuntimeRuleProposal,
    LAMBDAPI_V32_DIRECTED_1B_OWNER_BINDINGS
} from './directed_1b_proposal';
import {
    CORE_DIRECTED_1B_REVIEW,
    validateCoreDirected1bReview
} from './directed_1b_review';
import {
    CORE_DIRECTED_1A_PRIMITIVE_NAMES,
    CoreDirected1aCatalog
} from './directed_1a';
import {
    CORE_DIRECTED_1A_PROPOSAL,
    CoreDirected1aCandidateOwnerId
} from './directed_1a_proposal';
import {
    CoreChecker,
    CoreCheckerConversionResult
} from './checker';
import {
    CoreDeclarationEnvironment
} from './context';
import {
    CoreDirectedFoundationRuntimeProgram
} from './directed_foundation';
import {
    CoreDirectedFoundationRuleId
} from './directed_foundation_proposal';
import {
    CoreDirectedFoundation2RuntimeProgram
} from './directed_foundation_2';
import {
    CoreDirectedFoundation2RuleId
} from './directed_foundation_2_proposal';
import {
    CoreRuntimeHeadRewriteResult,
    CoreRuntimeMatch
} from './evaluator';
import {
    CoreLfBuilderTerm,
    CoreLfScopedBuilder
} from './lf_builder';
import {
    CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT,
    CoreLfChecker,
    createCoreLfChecker
} from './lf_checker';
import {
    CoreLfCatalogRuntime,
    CoreLfCombinedNextStep,
    coreLfDefinitionalCompare
} from './lf_conversion';
import {
    CoreLfDeclarationCheckerFactory,
    CoreLfDeclarationEnvironment
} from './lf_declarations';
import {
    BinderMode,
    KernelExpression,
    Provenance,
    binderMode,
    kernelApplication,
    kernelBinder,
    kernelBound,
    kernelCall,
    kernelExpressionEquals,
    kernelFree,
    kernelLambda,
    kernelPi,
    kernelShift,
    kernelUniverse,
    provenance
} from './kernel';
import {
    CORE_OWNER_SCHEMAS,
    CoreOwnerId,
    Plicity
} from './schema';
import {
    CoreElaborationSession
} from './session';

export const CORE_DIRECTED_1B_PRIMITIVE_NAMES = Object.freeze({
    'decoded-dependent-pair': 'dttlf_decoded_sigma',
    'dependent-pair': 'dttlf_Struct_sigma',
    'sigma-first-projection': 'dttlf_Sigma_proj1_func',
    'sigma-transport-arrow': 'dttlf_sigma_transport_arrow',
    'sigma-telescope-transport': 'dttlf_Sigma_catd_transport_func'
} as const satisfies Record<
    CoreDirected1bCandidateOwnerId,
    string
>);

export interface CoreDirected1bPrimitive {
    readonly order: number;
    readonly owner: CoreDirected1bCandidateOwnerId;
    readonly coreName: string;
    readonly signature: KernelExpression;
    readonly body?: KernelExpression;
    readonly disposition:
        | 'opaque-import'
        | 'transparent-checked-definition';
    readonly backendName: string;
    readonly provenance: Provenance;
}

export interface CoreDirected1bRuntimeRule {
    readonly order: number;
    readonly id: CoreDirected1bRuntimeRuleId;
}

export type CoreDirected1bCatalogRuntimeRuleId =
    | CoreDirectedFoundationRuleId
    | CoreDirectedFoundation2RuleId
    | CoreDirected1bRuntimeRuleId;

export type CoreDirected1bCatalogErrorCode =
    | 'UNKNOWN_CANDIDATE_OWNER'
    | 'INVALID_CANDIDATE_ARITY'
    | 'MISSING_CANDIDATE_DEPENDENCY'
    | 'FOREIGN_CANDIDATE_ENVIRONMENT'
    | 'INCOMPLETE_RUNTIME_MATCH';

export class CoreDirected1bCatalogError extends Error {
    constructor(
        public readonly code: CoreDirected1bCatalogErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreDirected1bCatalogError';
    }
}

const explicitFunctorial: BinderMode =
    binderMode('explicit', 'functorial');

const isBaseOwner = (
    owner: string
): owner is CoreOwnerId =>
    Object.prototype.hasOwnProperty.call(CORE_OWNER_SCHEMAS, owner);

const isDirected1aOwner = (
    owner: string
): owner is CoreDirected1aCandidateOwnerId =>
    Object.prototype.hasOwnProperty.call(
        CORE_DIRECTED_1A_PRIMITIVE_NAMES,
        owner
    );

const isDirected1bOwner = (
    owner: string
): owner is CoreDirected1bCandidateOwnerId =>
    Object.prototype.hasOwnProperty.call(
        CORE_DIRECTED_1B_PRIMITIVE_NAMES,
        owner
    );

const directed1aOwnerProposal = (
    owner: CoreDirected1aCandidateOwnerId
) => {
    const proposal = CORE_DIRECTED_1A_PROPOSAL.owners.find(
        entry => entry.owner === owner
    );
    if (!proposal) {
        throw new CoreDirected1bCatalogError(
            'MISSING_CANDIDATE_DEPENDENCY',
            `DIRECTED-1B cannot locate reviewed DIRECTED-1A owner '${owner}'`
        );
    }
    return proposal;
};

const directed1bOwnerProposal = (
    owner: CoreDirected1bCandidateOwnerId
): CoreDirected1bOwnerProposal => {
    const proposal = CORE_DIRECTED_1B_PROPOSAL.owners.find(
        entry => entry.owner === owner
    );
    if (!proposal) {
        throw new CoreDirected1bCatalogError(
            'UNKNOWN_CANDIDATE_OWNER',
            `DIRECTED-1B has no reviewed owner '${owner}'`
        );
    }
    return proposal;
};

const candidateOwnerMetadata = (
    owner: CoreDirected1bExpressionOwnerId
): {
    readonly coreName: string;
    readonly plicities: readonly Plicity[];
} => {
    if (isDirected1aOwner(owner)) {
        return {
            coreName: CORE_DIRECTED_1A_PRIMITIVE_NAMES[owner],
            plicities: directed1aOwnerProposal(owner).slots.map(
                slot => slot.plicity
            )
        };
    }
    if (isDirected1bOwner(owner)) {
        return {
            coreName: CORE_DIRECTED_1B_PRIMITIVE_NAMES[owner],
            plicities: directed1bOwnerProposal(owner).slots.map(
                slot => slot.plicity
            )
        };
    }
    throw new CoreDirected1bCatalogError(
        'MISSING_CANDIDATE_DEPENDENCY',
        `DIRECTED-1B expression owner '${owner}' is not a candidate owner`
    );
};

const derived = (
    detail: string,
    source: Provenance
): Provenance => provenance('derived', detail, source.span);

const formatCatalogNextStep = (
    next: CoreLfCombinedNextStep
): string => {
    switch (next.kind) {
        case 'zonk':
            return 'catalog zonk step';
        case 'beta':
            return `catalog beta step (${next.argumentPlicity})`;
        case 'delta':
            return `catalog delta step '${next.declarationName}'`;
        case 'runtime':
            return `catalog runtime rule '${next.ruleId}'`;
        default: {
            const exhaustive: never = next;
            return exhaustive;
        }
    }
};

/**
 * Declaration validation needs the approved facade reductions before the
 * complete LF declaration wrapper exists. This checker therefore combines
 * generic beta, the closed directed runtime, and the frozen MVP component,
 * but deliberately has no delta declarations or rule-registration surface.
 */
class CoreDirectedCatalogDeclarationChecker extends CoreChecker {
    constructor(
        environment: CoreDeclarationEnvironment,
        private readonly runtimeProgram: CoreLfCatalogRuntime
    ) {
        super(new CoreElaborationSession(environment));
    }

    protected permitsAnnotatedLambdaInference(): boolean {
        return true;
    }

    protected conversionDiagnosticName(): string {
        return 'Reviewed directed catalog conversion';
    }

    protected compareDefinitions(
        left: KernelExpression,
        right: KernelExpression,
        stepLimit: number
    ): CoreCheckerConversionResult {
        const result = coreLfDefinitionalCompare(
            CoreLfDeclarationEnvironment.empty(),
            left,
            right,
            stepLimit,
            undefined,
            this.runtimeProgram
        );
        if (result.status === 'step-limit-exceeded') {
            return {
                status: 'step-limit-exceeded',
                path: result.path,
                nextStep: formatCatalogNextStep(result.next)
            };
        }
        return { status: result.status };
    }
}

const directedCatalogCheckerFactory = (
    runtimeProgram: CoreLfCatalogRuntime
): CoreLfDeclarationCheckerFactory =>
    environment => new CoreDirectedCatalogDeclarationChecker(
        environment,
        runtimeProgram
    );

const boundVariable = (
    name: string,
    scope: readonly string[],
    source: Provenance,
    detail: string
): KernelExpression => {
    const position = scope.lastIndexOf(name);
    if (position < 0) {
        throw new CoreDirected1bCatalogError(
            'MISSING_CANDIDATE_DEPENDENCY',
            `${detail} refers to unavailable variable '${name}'`
        );
    }
    return kernelBound(
        scope.length - position - 1,
        derived(`${detail} variable ${name}`, source)
    );
};

const candidateCall = (
    owner: Exclude<CoreDirected1bExpressionOwnerId, CoreOwnerId>,
    arguments_: readonly KernelExpression[],
    source: Provenance,
    detail: string
): KernelExpression => {
    const metadata = candidateOwnerMetadata(owner);
    if (arguments_.length !== metadata.plicities.length) {
        throw new CoreDirected1bCatalogError(
            'INVALID_CANDIDATE_ARITY',
            `${detail} applies '${owner}' to ${arguments_.length} ` +
            `arguments, expected ${metadata.plicities.length}`
        );
    }
    const nodeProvenance = derived(`${detail} owner ${owner}`, source);
    return kernelCall(
        kernelFree(metadata.coreName, nodeProvenance),
        arguments_.map((value, index) => ({
            plicity: metadata.plicities[index],
            value
        })),
        nodeProvenance
    );
};

const materializeExpression = (
    expression: CoreDirected1bExpression,
    scope: readonly string[],
    source: Provenance,
    detail: string
): KernelExpression => {
    switch (expression.tag) {
        case 'variable':
            return boundVariable(
                expression.name,
                scope,
                source,
                detail
            );
        case 'type':
            return kernelUniverse(
                derived(`${detail} universe`, source)
            );
        case 'owner-application': {
            const arguments_ = expression.arguments.map(
                (argument, index) => materializeExpression(
                    argument,
                    scope,
                    source,
                    `${detail}, ${expression.owner} argument ${index}`
                )
            );
            const nodeProvenance = derived(
                `${detail} owner ${expression.owner}`,
                source
            );
            if (isBaseOwner(expression.owner)) {
                return kernelApplication(
                    expression.owner,
                    arguments_.map(value => ({ value })),
                    nodeProvenance
                );
            }
            return candidateCall(
                expression.owner,
                arguments_,
                source,
                detail
            );
        }
        case 'call':
            return kernelCall(
                materializeExpression(
                    expression.callee,
                    scope,
                    source,
                    `${detail}, call callee`
                ),
                expression.arguments.map((argument, index) => ({
                    plicity: argument.plicity,
                    value: materializeExpression(
                        argument.value,
                        scope,
                        source,
                        `${detail}, call argument ${index}`
                    )
                })),
                derived(`${detail} generic call`, source)
            );
        case 'pi':
        case 'lambda': {
            const binderType = materializeExpression(
                expression.binder.type,
                scope,
                source,
                `${detail}, ${expression.tag} binder type`
            );
            const nodeProvenance = derived(
                `${detail} ${expression.tag} ${expression.binder.name}`,
                source
            );
            const binder = kernelBinder(
                expression.binder.name,
                binderType,
                binderMode(
                    expression.binder.plicity,
                    expression.binder.variation
                ),
                nodeProvenance
            );
            const body = materializeExpression(
                expression.body,
                [...scope, expression.binder.name],
                source,
                `${detail}, ${expression.tag} body`
            );
            return expression.tag === 'pi'
                ? kernelPi(binder, body, nodeProvenance)
                : kernelLambda(binder, body, nodeProvenance);
        }
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

const materializeSignature = (
    owner: CoreDirected1bOwnerProposal,
    source: Provenance
): KernelExpression => {
    const build = (
        slotIndex: number,
        scope: readonly string[]
    ): KernelExpression => {
        if (slotIndex === owner.slots.length) {
            return materializeExpression(
                owner.result,
                scope,
                source,
                `${owner.owner} result`
            );
        }
        const slot = owner.slots[slotIndex];
        const nodeProvenance = derived(
            `${owner.owner} signature binder ${slot.name}`,
            source
        );
        return kernelPi(
            kernelBinder(
                slot.name,
                materializeExpression(
                    slot.type,
                    scope,
                    source,
                    `${owner.owner} slot ${slot.name} type`
                ),
                binderMode(slot.plicity, 'functorial'),
                nodeProvenance
            ),
            build(slotIndex + 1, [...scope, slot.name]),
            nodeProvenance
        );
    };
    return build(0, []);
};

const materializeBody = (
    owner: CoreDirected1bOwnerProposal,
    source: Provenance
): KernelExpression | undefined => {
    if (owner.body === undefined) return undefined;

    const build = (
        slotIndex: number,
        scope: readonly string[]
    ): KernelExpression => {
        if (slotIndex === owner.slots.length) {
            return materializeExpression(
                owner.body as CoreDirected1bExpression,
                scope,
                source,
                `${owner.owner} definition body`
            );
        }
        const slot = owner.slots[slotIndex];
        const nodeProvenance = derived(
            `${owner.owner} definition binder ${slot.name}`,
            source
        );
        return kernelLambda(
            kernelBinder(
                slot.name,
                materializeExpression(
                    slot.type,
                    scope,
                    source,
                    `${owner.owner} body slot ${slot.name} type`
                ),
                binderMode(slot.plicity, 'functorial'),
                nodeProvenance
            ),
            build(slotIndex + 1, [...scope, slot.name]),
            nodeProvenance
        );
    };
    return build(0, []);
};

const matchCandidateOwner = (
    owner: Exclude<CoreDirected1bExpressionOwnerId, CoreOwnerId>,
    arguments_: readonly CoreDirected1bExpression[],
    expression: KernelExpression,
    bindings: Map<string, KernelExpression>
): boolean => {
    const metadata = candidateOwnerMetadata(owner);
    if (
        expression.tag !== 'call' ||
        expression.callee.tag !== 'reference' ||
        expression.callee.name !== metadata.coreName ||
        expression.arguments.length !== arguments_.length ||
        expression.arguments.length !== metadata.plicities.length
    ) {
        return false;
    }
    return arguments_.every((argument, index) =>
        expression.arguments[index].plicity ===
            metadata.plicities[index] &&
        matchRuntimePattern(
            argument,
            expression.arguments[index].value,
            bindings
        )
    );
};

const matchRuntimePattern = (
    pattern: CoreDirected1bExpression,
    expression: KernelExpression,
    bindings: Map<string, KernelExpression>
): boolean => {
    switch (pattern.tag) {
        case 'variable': {
            const existing = bindings.get(pattern.name);
            if (existing === undefined) {
                bindings.set(pattern.name, expression);
                return true;
            }
            return kernelExpressionEquals(existing, expression);
        }
        case 'type':
            return expression.tag === 'universe';
        case 'owner-application':
            if (isBaseOwner(pattern.owner)) {
                return expression.tag === 'application' &&
                    expression.owner === pattern.owner &&
                    expression.arguments.length ===
                        pattern.arguments.length &&
                    pattern.arguments.every((argument, index) =>
                        expression.arguments[index].plicity ===
                            CORE_OWNER_SCHEMAS[
                                pattern.owner as CoreOwnerId
                            ].slots[index].plicity &&
                        matchRuntimePattern(
                            argument,
                            expression.arguments[index].value,
                            bindings
                        )
                    );
            }
            return matchCandidateOwner(
                pattern.owner,
                pattern.arguments,
                expression,
                bindings
            );
        case 'call':
            return expression.tag === 'call' &&
                expression.arguments.length === pattern.arguments.length &&
                matchRuntimePattern(
                    pattern.callee,
                    expression.callee,
                    bindings
                ) &&
                pattern.arguments.every((argument, index) =>
                    expression.arguments[index].plicity ===
                        argument.plicity &&
                    matchRuntimePattern(
                        argument.value,
                        expression.arguments[index].value,
                        bindings
                    )
                );
        case 'pi':
        case 'lambda':
            return expression.tag === pattern.tag &&
                expression.binder.mode.plicity ===
                    pattern.binder.plicity &&
                expression.binder.mode.variation ===
                    pattern.binder.variation &&
                matchRuntimePattern(
                    pattern.binder.type,
                    expression.binder.type,
                    bindings
                ) &&
                matchRuntimePattern(
                    pattern.body,
                    expression.body,
                    bindings
                );
        default: {
            const exhaustive: never = pattern;
            return exhaustive;
        }
    }
};

const instantiateRuntimeExpression = (
    expression: CoreDirected1bExpression,
    bindings: ReadonlyMap<string, KernelExpression>,
    binderScope: readonly string[],
    redex: KernelExpression,
    rule: CoreDirected1bRuntimeRuleProposal
): KernelExpression => {
    const source = redex.provenance;
    const detail = `DIRECTED-1B runtime rewrite ${rule.id}`;
    switch (expression.tag) {
        case 'variable': {
            const binderPosition = binderScope.lastIndexOf(expression.name);
            if (binderPosition >= 0) {
                return kernelBound(
                    binderScope.length - binderPosition - 1,
                    derived(`${detail} binder ${expression.name}`, source)
                );
            }
            const binding = bindings.get(expression.name);
            if (binding === undefined) {
                throw new CoreDirected1bCatalogError(
                    'INCOMPLETE_RUNTIME_MATCH',
                    `Runtime rule '${rule.id}' has no binding for ` +
                    `'${expression.name}'`
                );
            }
            return binderScope.length === 0
                ? binding
                : kernelShift(binding, binderScope.length);
        }
        case 'type':
            return kernelUniverse(derived(`${detail} universe`, source));
        case 'owner-application': {
            const arguments_ = expression.arguments.map(argument =>
                instantiateRuntimeExpression(
                    argument,
                    bindings,
                    binderScope,
                    redex,
                    rule
                )
            );
            const nodeProvenance = derived(
                `${detail} owner ${expression.owner}`,
                source
            );
            if (isBaseOwner(expression.owner)) {
                return kernelApplication(
                    expression.owner,
                    arguments_.map(value => ({ value })),
                    nodeProvenance
                );
            }
            return candidateCall(
                expression.owner,
                arguments_,
                source,
                detail
            );
        }
        case 'call':
            return kernelCall(
                instantiateRuntimeExpression(
                    expression.callee,
                    bindings,
                    binderScope,
                    redex,
                    rule
                ),
                expression.arguments.map(argument => ({
                    plicity: argument.plicity,
                    value: instantiateRuntimeExpression(
                        argument.value,
                        bindings,
                        binderScope,
                        redex,
                        rule
                    )
                })),
                derived(`${detail} generic call`, source)
            );
        case 'pi':
        case 'lambda': {
            const nodeProvenance = derived(
                `${detail} ${expression.tag} ${expression.binder.name}`,
                source
            );
            const binder = kernelBinder(
                expression.binder.name,
                instantiateRuntimeExpression(
                    expression.binder.type,
                    bindings,
                    binderScope,
                    redex,
                    rule
                ),
                binderMode(
                    expression.binder.plicity,
                    expression.binder.variation
                ),
                nodeProvenance
            );
            const body = instantiateRuntimeExpression(
                expression.body,
                bindings,
                [...binderScope, expression.binder.name],
                redex,
                rule
            );
            return expression.tag === 'pi'
                ? kernelPi(binder, body, nodeProvenance)
                : kernelLambda(binder, body, nodeProvenance);
        }
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

/**
 * The closed, exact seven-rule runtime component approved for the directed
 * catalog: three Foundation 1 prerequisites, one Foundation 2 prerequisite,
 * then the three DIRECTED-1B-owned rules.
 */
export class CoreDirected1bRuntimeProgram
implements CoreLfCatalogRuntime {
    readonly revision =
        'DIRECTED-FOUNDATION-1+DIRECTED-FOUNDATION-2+' +
        'DIRECTED-1B-REVIEWED';
    readonly ruleIds: readonly CoreDirected1bCatalogRuntimeRuleId[];
    readonly rules: readonly CoreDirected1bRuntimeRule[];

    private constructor(
        public readonly foundation1:
            CoreDirectedFoundationRuntimeProgram,
        public readonly foundation2:
            CoreDirectedFoundation2RuntimeProgram
    ) {
        this.rules = Object.freeze(
            CORE_DIRECTED_1B_PROPOSAL.runtimeRules.map(rule =>
                Object.freeze({
                    order: rule.order,
                    id: rule.id
                })
            )
        );
        this.ruleIds = Object.freeze([
            ...this.foundation1.ruleIds,
            ...this.foundation2.ruleIds,
            ...this.rules.map(rule => rule.id)
        ]);
        Object.freeze(this);
    }

    static create(): CoreDirected1bRuntimeProgram {
        validateCoreDirected1bReview(CORE_DIRECTED_1B_REVIEW);
        return new CoreDirected1bRuntimeProgram(
            CoreDirectedFoundationRuntimeProgram.create(),
            CoreDirectedFoundation2RuntimeProgram.create()
        );
    }

    rewriteHead(
        expression: KernelExpression
    ): CoreRuntimeHeadRewriteResult {
        const foundation1 =
            this.foundation1.rewriteHead(expression);
        if (foundation1.status === 'rewritten') {
            return foundation1;
        }

        const foundation2 =
            this.foundation2.rewriteHead(expression);
        if (foundation2.status === 'rewritten') {
            return Object.freeze({
                ...foundation2,
                ruleIndex:
                    this.foundation1.ruleIds.length +
                    foundation2.ruleIndex
            });
        }

        for (
            let localRuleIndex = 0;
            localRuleIndex <
                CORE_DIRECTED_1B_PROPOSAL.runtimeRules.length;
            localRuleIndex++
        ) {
            const rule =
                CORE_DIRECTED_1B_PROPOSAL.runtimeRules[
                    localRuleIndex
                ];
            const bindings = new Map<string, KernelExpression>();
            if (!matchRuntimePattern(rule.left, expression, bindings)) {
                continue;
            }
            const orderedBindings = rule.variables.map(variable => {
                const binding = bindings.get(variable.name);
                if (binding === undefined) {
                    throw new CoreDirected1bCatalogError(
                        'INCOMPLETE_RUNTIME_MATCH',
                        `Runtime rule '${rule.id}' did not bind ` +
                        `'${variable.name}'`
                    );
                }
                return binding;
            });
            const match: CoreRuntimeMatch = Object.freeze({
                ruleId: rule.id,
                bindings: Object.freeze(orderedBindings)
            });
            return Object.freeze({
                status: 'rewritten',
                ruleId: rule.id,
                ruleIndex:
                    this.foundation1.ruleIds.length +
                    this.foundation2.ruleIds.length +
                    localRuleIndex,
                before: expression,
                after: instantiateRuntimeExpression(
                    rule.right,
                    bindings,
                    [],
                    expression,
                    rule
                ),
                match
            });
        }
        return Object.freeze({
            status: 'irreducible',
            expression
        });
    }
}

const freezePrimitive = (
    primitive: CoreDirected1bPrimitive
): CoreDirected1bPrimitive => Object.freeze({ ...primitive });

/**
 * Session-local catalog for the exact reviewed DIRECTED-1A + DIRECTED-1B
 * candidate boundary.
 */
export class CoreDirected1bCatalog {
    private readonly primitiveMap: ReadonlyMap<
        CoreDirected1bCandidateOwnerId,
        CoreDirected1bPrimitive
    >;

    private constructor(
        public readonly directed1a: CoreDirected1aCatalog,
        public readonly environment: CoreLfDeclarationEnvironment,
        public readonly primitives: readonly CoreDirected1bPrimitive[],
        public readonly runtimeProgram: CoreDirected1bRuntimeProgram,
        public readonly externalFreeReferences: Readonly<
            Record<string, string>
        >,
        public readonly externalTransparentDefinitions: Readonly<
            Record<string, string>
        >
    ) {
        this.primitives = Object.freeze(
            primitives.map(freezePrimitive)
        );
        this.primitiveMap = new Map(
            this.primitives.map(primitive => [
                primitive.owner,
                primitive
            ])
        );
        this.externalFreeReferences = Object.freeze({
            ...externalFreeReferences
        });
        this.externalTransparentDefinitions = Object.freeze({
            ...externalTransparentDefinitions
        });
        Object.freeze(this);
    }

    static create(
        source: Provenance = provenance(
            'derived',
            'reviewed DIRECTED-1B primitive catalog'
        )
    ): CoreDirected1bCatalog {
        validateCoreDirected1bReview(CORE_DIRECTED_1B_REVIEW);

        const directed1a = CoreDirected1aCatalog.create(source);
        const runtimeProgram =
            CoreDirected1bRuntimeProgram.create();
        const checkerFactory =
            directedCatalogCheckerFactory(runtimeProgram);
        let environment = directed1a.environment;
        const primitives: CoreDirected1bPrimitive[] = [];
        const externalFreeReferences: Record<string, string> = {
            ...directed1a.externalFreeReferences
        };
        const externalTransparentDefinitions: Record<string, string> = {};

        for (const owner of CORE_DIRECTED_1B_PROPOSAL.owners) {
            const binding =
                LAMBDAPI_V32_DIRECTED_1B_OWNER_BINDINGS[owner.order];
            if (!binding || binding.owner !== owner.owner) {
                throw new CoreDirected1bCatalogError(
                    'MISSING_CANDIDATE_DEPENDENCY',
                    `DIRECTED-1B binding ${owner.order} does not match ` +
                    owner.owner
                );
            }
            const coreName =
                CORE_DIRECTED_1B_PRIMITIVE_NAMES[owner.owner];
            const ownerProvenance = derived(
                `reviewed DIRECTED-1B primitive ${owner.owner}`,
                source
            );
            const signature = materializeSignature(
                owner,
                ownerProvenance
            );
            const body = materializeBody(owner, ownerProvenance);
            environment = environment.extend({
                name: coreName,
                type: signature,
                mode: explicitFunctorial,
                provenance: ownerProvenance,
                body,
                transparency:
                    owner.candidateDisposition ===
                        'transparent-checked-definition'
                        ? 'transparent'
                        : 'opaque'
            }, checkerFactory);
            const primitive = freezePrimitive({
                order: owner.order,
                owner: owner.owner,
                coreName,
                signature,
                body,
                disposition: owner.candidateDisposition,
                backendName: binding.serializedName,
                provenance: ownerProvenance
            });
            primitives.push(primitive);
            if (
                owner.candidateDisposition ===
                'transparent-checked-definition'
            ) {
                externalTransparentDefinitions[coreName] =
                    binding.serializedName;
            } else {
                externalFreeReferences[coreName] =
                    binding.serializedName;
            }
        }

        return new CoreDirected1bCatalog(
            directed1a,
            environment,
            primitives,
            runtimeProgram,
            externalFreeReferences,
            externalTransparentDefinitions
        );
    }

    primitive(
        owner: CoreDirected1bCandidateOwnerId
    ): CoreDirected1bPrimitive {
        const primitive = this.primitiveMap.get(owner);
        if (!primitive) {
            throw new CoreDirected1bCatalogError(
                'UNKNOWN_CANDIDATE_OWNER',
                `DIRECTED-1B catalog has no owner '${owner}'`
            );
        }
        return primitive;
    }

    application(
        owner: CoreDirected1bCandidateOwnerId,
        arguments_: readonly KernelExpression[],
        nodeProvenance: Provenance
    ): KernelExpression {
        const primitive = this.primitive(owner);
        const proposal = directed1bOwnerProposal(owner);
        if (arguments_.length !== proposal.slots.length) {
            throw new CoreDirected1bCatalogError(
                'INVALID_CANDIDATE_ARITY',
                `DIRECTED-1B owner ${owner} expects ` +
                `${proposal.slots.length} arguments, received ` +
                arguments_.length
            );
        }
        return kernelCall(
            kernelFree(primitive.coreName, nodeProvenance),
            arguments_.map((value, index) => ({
                plicity: proposal.slots[index].plicity,
                value
            })),
            nodeProvenance
        );
    }

    builderApplication(
        builder: CoreLfScopedBuilder,
        owner: CoreDirected1bCandidateOwnerId,
        arguments_: readonly CoreLfBuilderTerm[],
        nodeProvenance?: Provenance
    ): CoreLfBuilderTerm {
        const primitive = this.primitive(owner);
        const proposal = directed1bOwnerProposal(owner);
        if (arguments_.length !== proposal.slots.length) {
            throw new CoreDirected1bCatalogError(
                'INVALID_CANDIDATE_ARITY',
                `DIRECTED-1B owner ${owner} expects ` +
                `${proposal.slots.length} arguments, received ` +
                arguments_.length
            );
        }
        return builder.call(
            builder.free(primitive.coreName, nodeProvenance),
            arguments_.map((value, index) => ({
                plicity: proposal.slots[index].plicity,
                value,
                provenance: nodeProvenance
            })),
            nodeProvenance
        );
    }

    decodedDependentPair(
        classifier: KernelExpression,
        family: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        return this.application(
            'decoded-dependent-pair',
            [classifier, family],
            nodeProvenance
        );
    }

    dependentPair(
        classifier: KernelExpression,
        family: KernelExpression,
        first: KernelExpression,
        second: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        return this.application(
            'dependent-pair',
            [classifier, family, first, second],
            nodeProvenance
        );
    }

    sigmaFirstProjection(
        base: KernelExpression,
        family: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        return this.application(
            'sigma-first-projection',
            [base, family],
            nodeProvenance
        );
    }

    sigmaTransportArrow(
        base: KernelExpression,
        family: KernelExpression,
        source: KernelExpression,
        target: KernelExpression,
        arrow: KernelExpression,
        value: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        return this.application(
            'sigma-transport-arrow',
            [base, family, source, target, arrow, value],
            nodeProvenance
        );
    }

    sigmaTelescopeTransport(
        base: KernelExpression,
        family: KernelExpression,
        telescope: KernelExpression,
        source: KernelExpression,
        target: KernelExpression,
        arrow: KernelExpression,
        value: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        return this.application(
            'sigma-telescope-transport',
            [
                base,
                family,
                telescope,
                source,
                target,
                arrow,
                value
            ],
            nodeProvenance
        );
    }

    assertEnvironment(
        environment: CoreLfDeclarationEnvironment
    ): void {
        this.directed1a.assertEnvironment(environment);
        for (const primitive of this.primitives) {
            const declaration = environment.lookup(primitive.coreName);
            const expectedTransparency =
                primitive.disposition ===
                    'transparent-checked-definition'
                    ? 'transparent'
                    : 'opaque';
            if (
                !declaration ||
                declaration.transparency !== expectedTransparency ||
                !kernelExpressionEquals(
                    declaration.type,
                    primitive.signature
                ) ||
                (
                    primitive.body === undefined
                        ? declaration.body !== undefined
                        : declaration.body === undefined ||
                            !kernelExpressionEquals(
                                declaration.body,
                                primitive.body
                            )
                )
            ) {
                throw new CoreDirected1bCatalogError(
                    'FOREIGN_CANDIDATE_ENVIRONMENT',
                    `Environment does not preserve reviewed DIRECTED-1B ` +
                    `primitive '${primitive.owner}'`
                );
            }
        }
    }

    createChecker(
        environment: CoreLfDeclarationEnvironment = this.environment,
        comparisonStepLimit =
            CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT
    ): CoreLfChecker {
        this.assertEnvironment(environment);
        return createCoreLfChecker(
            environment,
            comparisonStepLimit,
            this.runtimeProgram
        );
    }
}
