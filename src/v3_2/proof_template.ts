/**
 * Management-only expression templates for compact proof-plan refinement.
 *
 * A template never becomes Core or canonical proof source. Its explicitly
 * ordered, root-scoped term placeholders lower immediately to existing
 * contextual `have` nodes followed by one `exact` node. Binder annotations
 * remain ordinary meta-free Core.
 */

import {
    CORE_OWNER_SCHEMAS,
    CoreOwnerId,
    Plicity
} from './schema';
import {
    KernelBinder,
    KernelExpression,
    Provenance,
    kernelApplication,
    kernelBinder,
    kernelBound,
    kernelCall,
    kernelLambda,
    kernelPi,
    kernelShift
} from './kernel';
import {
    CoreProofPlan,
    CoreProofPlanNodeOptions,
    coreProofPlanExact,
    coreProofPlanHave,
    validateCoreProofPlan
} from './proof_plan';

export const CORE_PROOF_REFINE_TEMPLATE_PROFILE = Object.freeze({
    revision: 'emdash-proof-refine-template-v1' as const,
    templateTags: Object.freeze([
        'core',
        'placeholder',
        'application',
        'call',
        'pi',
        'lambda'
    ] as const),
    placeholderScope: 'selected-goal-context' as const,
    placeholderOrder: 'explicit-binding-order' as const,
    templateBinderTypes: 'meta-free-core' as const,
    allowsTypePlaceholders: false as const,
    repeatedOccurrencesShareOneFact: true as const,
    lowering: 'nested-have-then-exact' as const,
    outputPlanTags: Object.freeze(['have', 'exact'] as const),
    addsCoreExpressionTags: false as const,
    addsProofPlanTags: false as const,
    retainsTemplate: false as const,
    retainsCallbacks: false as const,
    retainsMetavariables: false as const,
    performsSemanticChecks: false as const,
    nodeBuiltinDependency: false as const,
    productionLambdapiDependency: false as const
});

interface CoreProofTemplateNodeBase {
    readonly provenance: Provenance;
}

export interface CoreProofTemplateCore extends CoreProofTemplateNodeBase {
    readonly tag: 'core';
    readonly expression: KernelExpression;
}

export interface CoreProofTemplatePlaceholder
    extends CoreProofTemplateNodeBase {
    readonly tag: 'placeholder';
    readonly name: string;
}

export interface CoreProofTemplateOwnerArgument {
    readonly value: CoreProofTemplateExpression;
    readonly provenance: Provenance;
}

export interface CoreProofTemplateCallArgument
    extends CoreProofTemplateOwnerArgument {
    readonly plicity: Plicity;
}

export interface CoreProofTemplateApplication
    extends CoreProofTemplateNodeBase {
    readonly tag: 'application';
    readonly owner: CoreOwnerId;
    readonly arguments: readonly CoreProofTemplateOwnerArgument[];
}

export interface CoreProofTemplateCall extends CoreProofTemplateNodeBase {
    readonly tag: 'call';
    readonly callee: CoreProofTemplateExpression;
    readonly arguments: readonly CoreProofTemplateCallArgument[];
}

export interface CoreProofTemplatePi extends CoreProofTemplateNodeBase {
    readonly tag: 'pi';
    readonly binder: KernelBinder;
    readonly body: CoreProofTemplateExpression;
}

export interface CoreProofTemplateLambda extends CoreProofTemplateNodeBase {
    readonly tag: 'lambda';
    readonly binder: KernelBinder;
    readonly body: CoreProofTemplateExpression;
}

export type CoreProofTemplateExpression =
    | CoreProofTemplateCore
    | CoreProofTemplatePlaceholder
    | CoreProofTemplateApplication
    | CoreProofTemplateCall
    | CoreProofTemplatePi
    | CoreProofTemplateLambda;

export interface CoreProofTemplateBinding {
    readonly binder: KernelBinder;
    readonly proof: CoreProofPlan;
}

export interface CoreProofTemplateOwnerArgumentInput {
    readonly value: CoreProofTemplateExpression;
    readonly provenance?: Provenance;
}

export interface CoreProofTemplateCallArgumentInput
    extends CoreProofTemplateOwnerArgumentInput {
    readonly plicity: Plicity;
}

const frozenBinder = (binder: KernelBinder): KernelBinder => Object.freeze({
    ...binder,
    mode: Object.freeze({ ...binder.mode })
});

export const coreProofTemplateCore = (
    expression: KernelExpression,
    nodeProvenance: Provenance = expression.provenance
): CoreProofTemplateCore => Object.freeze({
    tag: 'core',
    expression,
    provenance: nodeProvenance
});

export const coreProofTemplatePlaceholder = (
    name: string,
    nodeProvenance: Provenance
): CoreProofTemplatePlaceholder => Object.freeze({
    tag: 'placeholder',
    name,
    provenance: nodeProvenance
});

export const coreProofTemplateApplication = (
    owner: CoreOwnerId,
    inputs: readonly CoreProofTemplateOwnerArgumentInput[],
    nodeProvenance: Provenance
): CoreProofTemplateApplication => Object.freeze({
    tag: 'application',
    owner,
    arguments: Object.freeze(inputs.map(input => Object.freeze({
        value: input.value,
        provenance: input.provenance ?? input.value.provenance
    }))),
    provenance: nodeProvenance
});

export const coreProofTemplateCall = (
    callee: CoreProofTemplateExpression,
    inputs: readonly CoreProofTemplateCallArgumentInput[],
    nodeProvenance: Provenance
): CoreProofTemplateCall => Object.freeze({
    tag: 'call',
    callee,
    arguments: Object.freeze(inputs.map(input => Object.freeze({
        plicity: input.plicity,
        value: input.value,
        provenance: input.provenance ?? input.value.provenance
    }))),
    provenance: nodeProvenance
});

export const coreProofTemplatePi = (
    binder: KernelBinder,
    body: CoreProofTemplateExpression,
    nodeProvenance: Provenance = binder.provenance
): CoreProofTemplatePi => Object.freeze({
    tag: 'pi',
    binder: frozenBinder(binder),
    body,
    provenance: nodeProvenance
});

export const coreProofTemplateLambda = (
    binder: KernelBinder,
    body: CoreProofTemplateExpression,
    nodeProvenance: Provenance = binder.provenance
): CoreProofTemplateLambda => Object.freeze({
    tag: 'lambda',
    binder: frozenBinder(binder),
    body,
    provenance: nodeProvenance
});

export const coreProofTemplateBinding = (
    binder: KernelBinder,
    proof: CoreProofPlan
): CoreProofTemplateBinding => Object.freeze({
    binder: frozenBinder(binder),
    proof
});

export type CoreProofRefineTemplateErrorCode =
    | 'INVALID_TEMPLATE'
    | 'CYCLIC_TEMPLATE'
    | 'DUPLICATE_BINDING'
    | 'UNKNOWN_PLACEHOLDER'
    | 'UNUSED_BINDING'
    | 'NON_SERIALIZABLE_EXPRESSION';

export class CoreProofRefineTemplateError extends Error {
    constructor(
        public readonly code: CoreProofRefineTemplateErrorCode,
        public readonly path: string,
        public readonly provenance: Provenance,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'CoreProofRefineTemplateError';
    }
}

const SAFE_IDENTIFIER = /^[A-Za-z][A-Za-z0-9_]*$/u;

const fail = (
    code: CoreProofRefineTemplateErrorCode,
    path: string,
    nodeProvenance: Provenance,
    message: string
): never => {
    throw new CoreProofRefineTemplateError(
        code,
        path,
        nodeProvenance,
        message
    );
};

const validMode = (binder: KernelBinder): boolean =>
    (binder.mode.plicity === 'explicit' ||
        binder.mode.plicity === 'implicit') &&
    (binder.mode.variation === 'functorial' ||
        binder.mode.variation === 'natural' ||
        binder.mode.variation === 'object-only');

const validateCoreExpression = (
    expression: KernelExpression,
    path: string,
    active: Set<object>
): void => {
    if (active.has(expression)) {
        fail(
            'NON_SERIALIZABLE_EXPRESSION',
            path,
            expression.provenance,
            'Refine template contains a cyclic Core expression'
        );
    }
    active.add(expression);
    switch (expression.tag) {
        case 'universe':
        case 'reference':
        case 'bound':
            break;
        case 'meta':
            fail(
                'NON_SERIALIZABLE_EXPRESSION',
                path,
                expression.provenance,
                'Refine template contains a process-local Core meta'
            );
            break;
        case 'application':
            expression.arguments.forEach((argument, index) =>
                validateCoreExpression(
                    argument.value,
                    `${path}.arguments[${index}].value`,
                    active
                )
            );
            break;
        case 'call':
            validateCoreExpression(expression.callee, `${path}.callee`, active);
            expression.arguments.forEach((argument, index) =>
                validateCoreExpression(
                    argument.value,
                    `${path}.arguments[${index}].value`,
                    active
                )
            );
            break;
        case 'pi':
        case 'lambda':
            validateCoreExpression(
                expression.binder.type,
                `${path}.binder.type`,
                active
            );
            validateCoreExpression(expression.body, `${path}.body`, active);
            break;
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
    active.delete(expression);
};

interface ValidatedTemplate {
    readonly bindingIndexByName: ReadonlyMap<string, number>;
}

const validateTemplate = (
    template: CoreProofTemplateExpression,
    bindings: readonly CoreProofTemplateBinding[]
): ValidatedTemplate => {
    const bindingIndexByName = new Map<string, number>();
    bindings.forEach((binding, index) => {
        const path = `bindings[${index}].binder`;
        if (!SAFE_IDENTIFIER.test(binding.binder.name) ||
            !validMode(binding.binder)) {
            fail(
                'INVALID_TEMPLATE',
                path,
                binding.binder.provenance,
                `Invalid refine-template binding '${binding.binder.name}'`
            );
        }
        if (bindingIndexByName.has(binding.binder.name)) {
            fail(
                'DUPLICATE_BINDING',
                path,
                binding.binder.provenance,
                `Duplicate refine-template binding ` +
                    `'${binding.binder.name}'`
            );
        }
        bindingIndexByName.set(binding.binder.name, index);
    });

    const uses = new Map<string, number>();
    const activeTemplates = new Set<object>();
    const activeCore = new Set<object>();
    const visit = (
        node: CoreProofTemplateExpression,
        path: string
    ): void => {
        if (activeTemplates.has(node)) {
            fail(
                'CYCLIC_TEMPLATE',
                path,
                node.provenance,
                'Refine template contains a cycle'
            );
        }
        activeTemplates.add(node);
        switch (node.tag) {
            case 'core':
                validateCoreExpression(
                    node.expression,
                    `${path}.expression`,
                    activeCore
                );
                break;
            case 'placeholder':
                if (!SAFE_IDENTIFIER.test(node.name)) {
                    fail(
                        'INVALID_TEMPLATE',
                        `${path}.name`,
                        node.provenance,
                        `Invalid refine placeholder '${node.name}'`
                    );
                }
                if (!bindingIndexByName.has(node.name)) {
                    fail(
                        'UNKNOWN_PLACEHOLDER',
                        `${path}.name`,
                        node.provenance,
                        `Unknown refine placeholder '${node.name}'`
                    );
                }
                uses.set(node.name, (uses.get(node.name) ?? 0) + 1);
                break;
            case 'application': {
                const schema = Object.prototype.hasOwnProperty.call(
                    CORE_OWNER_SCHEMAS,
                    node.owner
                )
                    ? CORE_OWNER_SCHEMAS[node.owner]
                    : undefined;
                if (schema === undefined ||
                    node.arguments.length !== schema.slots.length) {
                    fail(
                        'INVALID_TEMPLATE',
                        path,
                        node.provenance,
                        `Invalid refine-template owner application ` +
                            `'${String(node.owner)}'`
                    );
                }
                node.arguments.forEach((argument, index) =>
                    visit(argument.value, `${path}.arguments[${index}].value`)
                );
                break;
            }
            case 'call':
                if (node.arguments.length === 0) {
                    fail(
                        'INVALID_TEMPLATE',
                        path,
                        node.provenance,
                        'Refine-template call requires at least one argument'
                    );
                }
                visit(node.callee, `${path}.callee`);
                node.arguments.forEach((argument, index) => {
                    if (argument.plicity !== 'explicit' &&
                        argument.plicity !== 'implicit') {
                        fail(
                            'INVALID_TEMPLATE',
                            `${path}.arguments[${index}].plicity`,
                            argument.provenance,
                            'Invalid refine-template call plicity'
                        );
                    }
                    visit(
                        argument.value,
                        `${path}.arguments[${index}].value`
                    );
                });
                break;
            case 'pi':
            case 'lambda':
                if (!SAFE_IDENTIFIER.test(node.binder.name) ||
                    !validMode(node.binder)) {
                    fail(
                        'INVALID_TEMPLATE',
                        `${path}.binder`,
                        node.binder.provenance,
                        `Invalid refine-template binder ` +
                            `'${node.binder.name}'`
                    );
                }
                validateCoreExpression(
                    node.binder.type,
                    `${path}.binder.type`,
                    activeCore
                );
                visit(node.body, `${path}.body`);
                break;
            default: {
                const exhaustive: never = node;
                return exhaustive;
            }
        }
        activeTemplates.delete(node);
    };
    visit(template, 'template');

    bindings.forEach((binding, index) => {
        validateCoreExpression(
            binding.binder.type,
            `bindings[${index}].binder.type`,
            activeCore
        );
        if ((uses.get(binding.binder.name) ?? 0) !== 0) return;
        fail(
            'UNUSED_BINDING',
            `bindings[${index}].binder.name`,
            binding.binder.provenance,
            `Unused refine-template binding '${binding.binder.name}'`
        );
    });

    return Object.freeze({ bindingIndexByName });
};

const lowerTemplate = (
    template: CoreProofTemplateExpression,
    bindingIndexByName: ReadonlyMap<string, number>,
    bindingCount: number,
    localDepth = 0
): KernelExpression => {
    switch (template.tag) {
        case 'core':
            return kernelShift(
                template.expression,
                bindingCount,
                localDepth
            );
        case 'placeholder': {
            const bindingIndex = bindingIndexByName.get(template.name)!;
            return kernelBound(
                localDepth + bindingCount - bindingIndex - 1,
                template.provenance
            );
        }
        case 'application':
            return kernelApplication(
                template.owner,
                template.arguments.map(argument => ({
                    value: lowerTemplate(
                        argument.value,
                        bindingIndexByName,
                        bindingCount,
                        localDepth
                    ),
                    provenance: argument.provenance
                })),
                template.provenance
            );
        case 'call':
            return kernelCall(
                lowerTemplate(
                    template.callee,
                    bindingIndexByName,
                    bindingCount,
                    localDepth
                ),
                template.arguments.map(argument => ({
                    plicity: argument.plicity,
                    value: lowerTemplate(
                        argument.value,
                        bindingIndexByName,
                        bindingCount,
                        localDepth
                    ),
                    provenance: argument.provenance
                })),
                template.provenance
            );
        case 'pi': {
            const binder = kernelBinder(
                template.binder.name,
                kernelShift(
                    template.binder.type,
                    bindingCount,
                    localDepth
                ),
                template.binder.mode,
                template.binder.provenance
            );
            return kernelPi(
                binder,
                lowerTemplate(
                    template.body,
                    bindingIndexByName,
                    bindingCount,
                    localDepth + 1
                ),
                template.provenance
            );
        }
        case 'lambda': {
            const binder = kernelBinder(
                template.binder.name,
                kernelShift(
                    template.binder.type,
                    bindingCount,
                    localDepth
                ),
                template.binder.mode,
                template.binder.provenance
            );
            return kernelLambda(
                binder,
                lowerTemplate(
                    template.body,
                    bindingIndexByName,
                    bindingCount,
                    localDepth + 1
                ),
                template.provenance
            );
        }
        default: {
            const exhaustive: never = template;
            return exhaustive;
        }
    }
};

/**
 * Expand a compact expression skeleton to ordinary contextual base plans.
 */
export function coreProofPlanRefine(
    template: CoreProofTemplateExpression,
    bindings: readonly CoreProofTemplateBinding[],
    options: CoreProofPlanNodeOptions = {}
): CoreProofPlan {
    const validated = validateTemplate(template, bindings);
    const bindingCount = bindings.length;
    const solution = lowerTemplate(
        template,
        validated.bindingIndexByName,
        bindingCount
    );
    let plan: CoreProofPlan = coreProofPlanExact(
        solution,
        bindingCount === 0 ? options : {}
    );

    for (let index = bindingCount - 1; index >= 0; index--) {
        const binding = bindings[index];
        const binder = kernelBinder(
            binding.binder.name,
            kernelShift(binding.binder.type, index),
            binding.binder.mode,
            binding.binder.provenance
        );
        plan = coreProofPlanHave(
            binder,
            binding.proof,
            plan,
            index === 0 ? options : {}
        );
    }

    validateCoreProofPlan(plan);
    return plan;
}
