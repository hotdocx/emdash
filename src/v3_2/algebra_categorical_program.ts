/** Retained categorical programs and first lowering to algebra graphs. */

import { AlgebraOperation, AlgebraRuntimeSchema } from './algebra_engine';
import {
    AlgebraComputationGraph,
    AlgebraGraphReference,
    AlgebraGraphValue,
    createAlgebraComputationGraphBuilder
} from './algebra_graph';
import {
    CategoryOperation,
    ComputableCategory,
    planCategoryOperation
} from './algebra_category';
import {
    ALGEBRA_TOWER_PROFILE,
    CategoricalTower,
    ConstructorLoweringRule
} from './algebra_tower';

export const ALGEBRA_CATEGORICAL_PROGRAM_PROFILE = Object.freeze({
    revision: 'emdash-categorical-program-v1' as const,
    valueRevision: 'emdash-categorical-program-value-v1' as const,
    compilationRevision: 'emdash-categorical-compilation-v1' as const,
    lowering: 'explicit-whole-operation-bindings' as const,
    reinterpretationRules: 'retained-not-executed' as const,
    derivedCallbackInlining: false as const,
    optimizer: false as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraCategoricalProgramErrorCode =
    | 'INVALID_PROGRAM'
    | 'DUPLICATE_VALUE'
    | 'DUPLICATE_OUTPUT'
    | 'FOREIGN_VALUE'
    | 'SCHEMA_MISMATCH'
    | 'MISSING_LOWERING'
    | 'DUPLICATE_LOWERING'
    | 'DUPLICATE_COMPILER_RULE'
    | 'FOREIGN_REINTERPRETATION'
    | 'CATEGORY_METHOD_UNAVAILABLE';

export class AlgebraCategoricalProgramError extends Error {
    constructor(
        public readonly code: AlgebraCategoricalProgramErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraCategoricalProgramError';
    }
}

const fail = (
    code: AlgebraCategoricalProgramErrorCode,
    path: string,
    message: string,
    underlying?: unknown
): never => {
    throw new AlgebraCategoricalProgramError(
        code,
        path,
        message,
        underlying instanceof Error ? underlying : undefined
    );
};

const SAFE_ID = /^[A-Za-z][A-Za-z0-9._/-]*$/u;
const key = (kind: string, id: string): string => `${kind}\u0000${id}`;
const operationKey = (operation: CategoryOperation<unknown, unknown>): string =>
    `${operation.id}\u0000${operation.revision}`;
const sameSchema = (left: AlgebraRuntimeSchema<unknown>, right: AlgebraRuntimeSchema<unknown>) =>
    left.identity.id === right.identity.id &&
    left.identity.revision === right.identity.revision;

export interface CategoricalProgramValue<T> {
    readonly profileRevision:
        typeof ALGEBRA_CATEGORICAL_PROGRAM_PROFILE.valueRevision;
    readonly programId: string;
    readonly reference: AlgebraGraphReference;
    readonly schema: AlgebraRuntimeSchema<T>;
}

export interface CategoricalProgramNode {
    readonly id: string;
    readonly operation: CategoryOperation<unknown, unknown>;
    readonly input: AlgebraGraphReference;
    readonly inputSchema: AlgebraRuntimeSchema<unknown>;
    readonly outputSchema: AlgebraRuntimeSchema<unknown>;
}

export interface CategoricalProgram {
    readonly profileRevision: typeof ALGEBRA_CATEGORICAL_PROGRAM_PROFILE.revision;
    readonly id: string;
    readonly revision: string;
    readonly inputs: readonly {
        readonly id: string;
        readonly schema: AlgebraRuntimeSchema<unknown>;
    }[];
    readonly nodes: readonly CategoricalProgramNode[];
    readonly outputs: readonly {
        readonly id: string;
        readonly source: AlgebraGraphReference;
        readonly schema: AlgebraRuntimeSchema<unknown>;
    }[];
}

export const createCategoricalProgramBuilder = (id: string, revision: string) => {
    if (!SAFE_ID.test(id) || !SAFE_ID.test(revision)) {
        return fail('INVALID_PROGRAM', 'program', 'Invalid program identity');
    }
    const inputs: { id: string; schema: AlgebraRuntimeSchema<unknown> }[] = [];
    const nodes: CategoricalProgramNode[] = [];
    const ids = new Set<string>();
    let built = false;
    const value = <T>(reference: AlgebraGraphReference, schema: AlgebraRuntimeSchema<T>):
        CategoricalProgramValue<T> => Object.freeze({
            profileRevision: ALGEBRA_CATEGORICAL_PROGRAM_PROFILE.valueRevision,
            programId: id,
            reference,
            schema
        });
    const reserve = (valueId: string, path: string): void => {
        if (!SAFE_ID.test(valueId) || ids.has(valueId)) {
            fail('DUPLICATE_VALUE', path, `Invalid or duplicate '${valueId}'`);
        }
        ids.add(valueId);
    };
    return Object.freeze({
        input<T>(inputId: string, schema: AlgebraRuntimeSchema<T>) {
            if (built) fail('INVALID_PROGRAM', 'builder', 'Program already built');
            reserve(inputId, 'input');
            inputs.push({ id: inputId, schema: schema as AlgebraRuntimeSchema<unknown> });
            return value(
                Object.freeze({ kind: 'graph-input' as const, id: inputId }),
                schema
            );
        },
        operation<I, O>(
            nodeId: string,
            operation: CategoryOperation<I, O>,
            input: CategoricalProgramValue<I>
        ) {
            if (built) fail('INVALID_PROGRAM', 'builder', 'Program already built');
            reserve(nodeId, 'node');
            if (input.programId !== id) {
                fail('FOREIGN_VALUE', nodeId, 'Foreign categorical value');
            }
            if (!sameSchema(
                input.schema as AlgebraRuntimeSchema<unknown>,
                operation.input as AlgebraRuntimeSchema<unknown>
            )) {
                fail('SCHEMA_MISMATCH', nodeId, 'Operation input schema mismatch');
            }
            nodes.push(Object.freeze({
                id: nodeId,
                operation: operation as CategoryOperation<unknown, unknown>,
                input: input.reference,
                inputSchema: input.schema as AlgebraRuntimeSchema<unknown>,
                outputSchema: operation.output as AlgebraRuntimeSchema<unknown>
            }));
            return value(
                Object.freeze({ kind: 'node-output' as const, id: nodeId }),
                operation.output
            );
        },
        build(outputsInput: readonly {
            readonly id: string;
            readonly value: CategoricalProgramValue<unknown>;
        }[]): CategoricalProgram {
            if (built || outputsInput.length === 0) {
                return fail('INVALID_PROGRAM', 'outputs', 'Invalid program outputs');
            }
            const outputIds = new Set<string>();
            const outputs = outputsInput.map(output => {
                if (!SAFE_ID.test(output.id) || outputIds.has(output.id)) {
                    return fail('DUPLICATE_OUTPUT', output.id, 'Duplicate output');
                }
                if (output.value.programId !== id) {
                    return fail('FOREIGN_VALUE', output.id, 'Foreign output value');
                }
                outputIds.add(output.id);
                return Object.freeze({
                    id: output.id,
                    source: output.value.reference,
                    schema: output.value.schema as AlgebraRuntimeSchema<unknown>
                });
            });
            built = true;
            return Object.freeze({
                profileRevision: ALGEBRA_CATEGORICAL_PROGRAM_PROFILE.revision,
                id,
                revision,
                inputs: Object.freeze(inputs.map(input => Object.freeze(input))),
                nodes: Object.freeze([...nodes]),
                outputs: Object.freeze(outputs)
            });
        }
    });
};

export interface CategoryOperationLowering {
    readonly categoryOperation: CategoryOperation<unknown, unknown>;
    readonly algebraOperation: AlgebraOperation<unknown, unknown>;
}

export interface CategoricalCompilationTraceNode {
    readonly nodeId: string;
    readonly categoryOperationId: string;
    readonly selectedMethodId: string;
    readonly selectedMethodKind: 'primitive' | 'derived';
    readonly algebraOperationId: string;
}

export interface CategoricalCompilationReinterpretation {
    readonly profileRevision:
        typeof ALGEBRA_TOWER_PROFILE.reinterpretationRevision;
    readonly id: string;
    readonly publicCategoryId: string;
    readonly modelingCategoryId: string;
    readonly loweringRules: readonly ConstructorLoweringRule[];
}

export interface CategoricalCompilation {
    readonly profileRevision:
        typeof ALGEBRA_CATEGORICAL_PROGRAM_PROFILE.compilationRevision;
    readonly program: CategoricalProgram;
    readonly tower: CategoricalTower;
    readonly graph: AlgebraComputationGraph;
    readonly nodes: readonly CategoricalCompilationTraceNode[];
    readonly towerRules: readonly ConstructorLoweringRule[];
    readonly reinterpretationRules: readonly ConstructorLoweringRule[];
    readonly loweringRules: readonly ConstructorLoweringRule[];
}

export const compileCategoricalProgram = (input: {
    readonly program: CategoricalProgram;
    readonly category: ComputableCategory<unknown, unknown>;
    readonly tower: CategoricalTower;
    readonly lowerings: readonly CategoryOperationLowering[];
    readonly reinterpretations?: readonly CategoricalCompilationReinterpretation[];
}): CategoricalCompilation => {
    const lowerings = new Map<string, CategoryOperationLowering>();
    input.lowerings.forEach(lowering => {
        const id = operationKey(lowering.categoryOperation);
        if (lowerings.has(id)) fail('DUPLICATE_LOWERING', id, 'Duplicate lowering');
        if (!sameSchema(
            lowering.categoryOperation.input,
            lowering.algebraOperation.input
        ) || !sameSchema(
            lowering.categoryOperation.output,
            lowering.algebraOperation.output
        )) fail('SCHEMA_MISMATCH', id, 'Lowering schemas disagree');
        lowerings.set(id, lowering);
    });
    const compilerRuleIds = new Set<string>();
    const retainRule = (rule: ConstructorLoweringRule, path: string): void => {
        if (compilerRuleIds.has(rule.id)) {
            fail(
                'DUPLICATE_COMPILER_RULE',
                path,
                `Duplicate compiler rule '${rule.id}'`
            );
        }
        compilerRuleIds.add(rule.id);
    };
    input.tower.loweringRules.forEach((rule, index) => retainRule(
        rule,
        `tower.loweringRules[${index}]`
    ));
    const reinterpretationIds = new Set<string>();
    const reinterpretationRules: ConstructorLoweringRule[] = [];
    (input.reinterpretations ?? []).forEach((reinterpretation, index) => {
        if (
            reinterpretation.profileRevision !==
                ALGEBRA_TOWER_PROFILE.reinterpretationRevision ||
            reinterpretation.publicCategoryId !== input.category.identity.id ||
            reinterpretationIds.has(reinterpretation.id)
        ) {
            fail(
                reinterpretationIds.has(reinterpretation.id)
                    ? 'DUPLICATE_COMPILER_RULE'
                    : 'FOREIGN_REINTERPRETATION',
                `reinterpretations[${index}]`,
                `Invalid reinterpretation '${reinterpretation.id}'`
            );
        }
        reinterpretationIds.add(reinterpretation.id);
        reinterpretation.loweringRules.forEach((rule, ruleIndex) => {
            retainRule(
                rule,
                `reinterpretations[${index}].loweringRules[${ruleIndex}]`
            );
            reinterpretationRules.push(rule);
        });
    });
    const builder = createAlgebraComputationGraphBuilder(
        `${input.program.id}.lowered`,
        input.program.revision
    );
    const values = new Map<string, AlgebraGraphValue<unknown>>();
    input.program.inputs.forEach(entry => {
        values.set(key('graph-input', entry.id), builder.input(entry.id, entry.schema));
    });
    const trace: CategoricalCompilationTraceNode[] = [];
    input.program.nodes.forEach(node => {
        const lowering = lowerings.get(operationKey(node.operation));
        if (!lowering) {
            fail('MISSING_LOWERING', node.id, `No lowering for '${node.operation.id}'`);
        }
        let plan;
        try {
            plan = planCategoryOperation(input.category.operations, node.operation);
        } catch (error: unknown) {
            fail(
                'CATEGORY_METHOD_UNAVAILABLE',
                node.id,
                `No category method for '${node.operation.id}'`,
                error
            );
        }
        const source = values.get(key(node.input.kind, node.input.id));
        if (!source) fail('INVALID_PROGRAM', node.id, 'Unavailable node input');
        const output = builder.operation(
            node.id,
            lowering.algebraOperation,
            source
        );
        values.set(key('node-output', node.id), output);
        trace.push(Object.freeze({
            nodeId: node.id,
            categoryOperationId: node.operation.id,
            selectedMethodId: plan.method.id,
            selectedMethodKind: plan.method.kind,
            algebraOperationId: lowering.algebraOperation.identity.id
        }));
    });
    const graph = builder.build(input.program.outputs.map(output => ({
        id: output.id,
        value: values.get(key(output.source.kind, output.source.id))!
    })));
    return Object.freeze({
        profileRevision: ALGEBRA_CATEGORICAL_PROGRAM_PROFILE.compilationRevision,
        program: input.program,
        tower: input.tower,
        graph,
        nodes: Object.freeze(trace),
        towerRules: input.tower.loweringRules,
        reinterpretationRules: Object.freeze(reinterpretationRules),
        loweringRules: Object.freeze([
            ...input.tower.loweringRules,
            ...reinterpretationRules
        ])
    });
};
