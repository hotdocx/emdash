/**
 * Minimal explicit target IR for the active emdash v3.2 Lambdapi owners.
 *
 * This module deliberately does not import the legacy root `Term` union. The
 * target records every argument (including arguments implicit in Lambdapi)
 * and keeps source provenance without claiming to typecheck the kernel.
 */

export type Plicity = 'explicit' | 'implicit';
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

interface KernelSymbolSignature {
    serializedName: string;
    arguments: readonly Plicity[];
}

/**
 * ELAB-0's checked signature manifest, copied from the active declarations in
 * emdash2/emdash3_2.lp. Extending this table requires a fresh owner audit.
 */
export const KERNEL_SYMBOL_SIGNATURES = {
    tau: {
        serializedName: 'τ',
        arguments: ['explicit']
    },
    Obj: {
        serializedName: 'Obj',
        arguments: ['explicit']
    },
    Functor: {
        serializedName: 'Functor',
        arguments: ['explicit', 'explicit']
    },
    Hom: {
        serializedName: 'Hom',
        arguments: ['explicit', 'explicit', 'explicit']
    },
    Transf: {
        serializedName: 'Transf',
        arguments: ['implicit', 'implicit', 'explicit', 'explicit']
    },
    fapp0: {
        serializedName: 'fapp0',
        arguments: ['implicit', 'implicit', 'explicit', 'explicit']
    },
    fapp1_fapp0: {
        serializedName: 'fapp1_fapp0',
        arguments: [
            'implicit',
            'implicit',
            'explicit',
            'implicit',
            'implicit',
            'explicit'
        ]
    },
    tapp1_fapp0: {
        serializedName: 'tapp1_fapp0',
        arguments: [
            'implicit',
            'implicit',
            'implicit',
            'implicit',
            'implicit',
            'implicit',
            'explicit',
            'explicit'
        ]
    }
} as const satisfies Record<string, KernelSymbolSignature>;

export type KernelSymbolName = keyof typeof KERNEL_SYMBOL_SIGNATURES;

export interface KernelReference {
    tag: 'reference';
    namespace: 'local' | 'symbol';
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
    symbol: KernelSymbolName;
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
            `${role} '${name}' is not an ELAB-0-safe Lambdapi identifier`
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

export const kernelSymbol = (
    name: string,
    nodeProvenance: Provenance
): KernelReference => {
    assertSafeIdentifier(name, 'Kernel symbol');
    return {
        tag: 'reference',
        namespace: 'symbol',
        name,
        provenance: nodeProvenance
    };
};

export interface KernelArgumentInput {
    value: KernelExpression;
    provenance?: Provenance;
}

export function kernelApplication(
    symbol: KernelSymbolName,
    inputs: readonly KernelArgumentInput[],
    nodeProvenance: Provenance
): KernelApplication {
    const signature = KERNEL_SYMBOL_SIGNATURES[symbol];
    const argumentPlicities: readonly Plicity[] = signature.arguments;
    if (inputs.length !== argumentPlicities.length) {
        throw new Error(
            `Kernel symbol ${signature.serializedName} expects ` +
            `${argumentPlicities.length} arguments, received ${inputs.length}`
        );
    }

    return {
        tag: 'application',
        symbol,
        arguments: inputs.map((input, index) => ({
            plicity: argumentPlicities[index],
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
            return left.symbol === other.symbol &&
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
            const signature = KERNEL_SYMBOL_SIGNATURES[expression.symbol];
            const argumentPlicities: readonly Plicity[] = signature.arguments;
            const hasImplicitArguments = argumentPlicities.some(
                argument => argument === 'implicit'
            );
            const head = hasImplicitArguments
                ? `@${signature.serializedName}`
                : signature.serializedName;
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

export function formatSourceSpan(span: SourceSpan): string {
    return `${span.file}:${span.start.line}:${span.start.column}`;
}
