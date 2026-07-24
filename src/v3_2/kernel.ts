/**
 * Minimal backend-neutral explicit emdash Core IR.
 *
 * This module deliberately does not import the legacy root `Term` union or a
 * backend symbol catalog. Applications reference semantic owner schemas and
 * record every slot plus source provenance without claiming to typecheck the
 * full active kernel.
 */

import {
    CORE_OWNER_SCHEMAS,
    CoreOwnerId,
    Plicity
} from './schema';

export { CoreOwnerId, Plicity } from './schema';

export type VariationMode = 'functorial' | 'natural' | 'object-only';

export interface BinderMode {
    plicity: Plicity;
    variation: VariationMode;
}

export const binderMode = (
    plicity: Plicity,
    variation: VariationMode
): BinderMode => ({ plicity, variation });

export interface SourcePosition {
    line: number;
    column: number;
}

export interface SourceSpan {
    file: string;
    start: SourcePosition;
    end: SourcePosition;
}

export const sourceSpan = (
    file: string,
    startLine: number,
    startColumn: number,
    endLine: number = startLine,
    endColumn: number = startColumn
): SourceSpan => ({
    file,
    start: { line: startLine, column: startColumn },
    end: { line: endLine, column: endColumn }
});

export type ProvenanceOrigin = 'surface' | 'recovered' | 'derived';

export interface Provenance {
    origin: ProvenanceOrigin;
    span?: SourceSpan;
    detail: string;
}

export const provenance = (
    origin: ProvenanceOrigin,
    detail: string,
    span?: SourceSpan
): Provenance => ({ origin, detail, span });

export interface KernelReference {
    tag: 'reference';
    namespace: 'local';
    name: string;
    provenance: Provenance;
}

export interface KernelArgument {
    plicity: Plicity;
    value: KernelExpression;
    provenance: Provenance;
}

export interface KernelApplication {
    tag: 'application';
    owner: CoreOwnerId;
    arguments: readonly KernelArgument[];
    provenance: Provenance;
}

export interface KernelBinder {
    name: string;
    type: KernelExpression;
    mode: BinderMode;
    provenance: Provenance;
}

export interface KernelPi {
    tag: 'pi';
    binder: KernelBinder;
    body: KernelExpression;
    provenance: Provenance;
}

export interface KernelLambda {
    tag: 'lambda';
    binder: KernelBinder;
    body: KernelExpression;
    provenance: Provenance;
}

export type KernelExpression =
    | KernelReference
    | KernelApplication
    | KernelPi
    | KernelLambda;

const SAFE_IDENTIFIER = /^[A-Za-z][A-Za-z0-9_]*$/;

export function assertSafeIdentifier(name: string, role: string): void {
    if (!SAFE_IDENTIFIER.test(name)) {
        throw new Error(
            `${role} '${name}' is not a portable emdash Core identifier`
        );
    }
}

export const kernelLocal = (
    name: string,
    nodeProvenance: Provenance
): KernelReference => {
    assertSafeIdentifier(name, 'Local name');
    return {
        tag: 'reference',
        namespace: 'local',
        name,
        provenance: nodeProvenance
    };
};

export interface KernelArgumentInput {
    value: KernelExpression;
    provenance?: Provenance;
}

export function kernelApplication(
    owner: CoreOwnerId,
    inputs: readonly KernelArgumentInput[],
    nodeProvenance: Provenance
): KernelApplication {
    const schema = CORE_OWNER_SCHEMAS[owner];
    if (inputs.length !== schema.slots.length) {
        throw new Error(
            `Core owner ${owner} expects ${schema.slots.length} arguments, ` +
            `received ${inputs.length}`
        );
    }

    return {
        tag: 'application',
        owner,
        arguments: inputs.map((input, index) => ({
            plicity: schema.slots[index].plicity,
            value: input.value,
            provenance: input.provenance ?? input.value.provenance
        })),
        provenance: nodeProvenance
    };
}

export const kernelPi = (
    binder: KernelBinder,
    body: KernelExpression,
    nodeProvenance: Provenance
): KernelPi => ({
    tag: 'pi',
    binder,
    body,
    provenance: nodeProvenance
});

export const kernelLambda = (
    binder: KernelBinder,
    body: KernelExpression,
    nodeProvenance: Provenance
): KernelLambda => ({
    tag: 'lambda',
    binder,
    body,
    provenance: nodeProvenance
});

export function kernelExpressionEquals(
    left: KernelExpression,
    right: KernelExpression
): boolean {
    if (left.tag !== right.tag) return false;

    switch (left.tag) {
        case 'reference': {
            const other = right as KernelReference;
            return left.namespace === other.namespace && left.name === other.name;
        }
        case 'application': {
            const other = right as KernelApplication;
            return left.owner === other.owner &&
                left.arguments.length === other.arguments.length &&
                left.arguments.every((argument, index) =>
                    argument.plicity === other.arguments[index].plicity &&
                    kernelExpressionEquals(
                        argument.value,
                        other.arguments[index].value
                    )
                );
        }
        case 'pi':
        case 'lambda': {
            const other = right as KernelPi | KernelLambda;
            return left.binder.name === other.binder.name &&
                left.binder.mode.plicity === other.binder.mode.plicity &&
                left.binder.mode.variation === other.binder.mode.variation &&
                kernelExpressionEquals(left.binder.type, other.binder.type) &&
                kernelExpressionEquals(left.body, other.body);
        }
        default: {
            const exhaustive: never = left;
            return exhaustive;
        }
    }
}

export function formatSourceSpan(span: SourceSpan): string {
    return `${span.file}:${span.start.line}:${span.start.column}`;
}
