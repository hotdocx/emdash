/** Exact typed-input serialization for bounded affine bridge conformance. */

import {
    KernelExpression,
    formatSourceSpan,
    kernelCall,
    kernelFree,
    provenance,
    sourceSpan
} from './kernel';
import { serializeKernelExpression } from './lambdapi';
import { ProbeSourceMapEntry, SerializedProbe } from './probe';
import { AlgebraElement, AlgebraParent } from './algebra_parent';
import {
    AffineFormalCoverRealization
} from './algebra_formal_realization';
import {
    AFFINE_FORMAL_RING_BINDINGS
} from './algebra_formal_reifier';
import {
    AFFINE_FORMAL_COVER_BINDINGS,
    buildAffineFormalFamily
} from './algebra_formal_cover';
import {
    AFFINE_FORMAL_LOCALIZATION_BINDINGS,
    AffineFormalLocalizationRealization,
    buildAffineFormalLocalizationUnitTerms
} from './algebra_formal_localization';
import {
    AFFINE_FORMAL_OVERLAP_BINDINGS,
    AffineFormalCechFaceFactor
} from './algebra_formal_overlap';
import { AFFINE_FORMAL_CECH_BINDINGS } from './algebra_formal_cech';
import {
    AFFINE_FORMAL_ARTIFACT_BINDINGS,
    AffineFormalBridgeArtifact
} from './algebra_formal_artifact';

export const ALGEBRA_FORMAL_CONFORMANCE_PROFILE = Object.freeze({
    revision: 'emdash-affine-formal-conformance-v1' as const,
    defaultRequiredModule:
        'emdash.emdash3_2_commutative_algebra_affine_spec' as const,
    typedInputDeclarations: true as const,
    checksWithLambdapi: 'caller-controlled-bounded-runner' as const,
    semanticStringTemplates: false as const,
    addsCoreOwner: false as const,
    performsIo: false as const
});

export const AFFINE_FORMAL_CONFORMANCE_BINDINGS = Object.freeze({
    bridge_tau: 'τ',
    bridge_CommRing: 'CommRing',
    bridge_eq: '=',
    bridge_comm_ring_carrier: 'comm_ring_carrier',
    bridge_comm_ring_finite_dot: 'comm_ring_finite_dot',
    bridge_IsCommRingLocalizationAt: 'IsCommRingLocalizationAt',
    bridge_CommRingUnitEvidence: 'CommRingUnitEvidence',
    bridge_comm_ring_hom_id: 'comm_ring_hom_id',
    bridge_sigma_Snd: 'sigma_Snd'
});

const ALL_BINDINGS = Object.freeze({
    ...AFFINE_FORMAL_RING_BINDINGS,
    ...AFFINE_FORMAL_COVER_BINDINGS,
    ...AFFINE_FORMAL_LOCALIZATION_BINDINGS,
    ...AFFINE_FORMAL_OVERLAP_BINDINGS,
    ...AFFINE_FORMAL_CECH_BINDINGS,
    ...AFFINE_FORMAL_ARTIFACT_BINDINGS,
    ...AFFINE_FORMAL_CONFORMANCE_BINDINGS
});

export type AlgebraFormalConformanceErrorCode =
    | 'COVER_ARITY_MISMATCH'
    | 'DUPLICATE_INPUT_DECLARATION'
    | 'MISSING_INPUT_DECLARATION'
    | 'EXTRA_INPUT_DECLARATION'
    | 'UNRESOLVED_DECLARATION_TYPE_REFERENCE'
    | 'DUPLICATE_BACKEND_OWNER'
    | 'INVALID_REQUIRED_MODULE';

export class AlgebraFormalConformanceError extends Error {
    constructor(
        public readonly code: AlgebraFormalConformanceErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraFormalConformanceError';
    }
}

const fail = (
    code: AlgebraFormalConformanceErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraFormalConformanceError(code, path, message);
};

const nodeProvenance = provenance('derived', 'affine formal conformance');

type ConformanceBinding = keyof typeof AFFINE_FORMAL_CONFORMANCE_BINDINGS;

interface CallArgument {
    readonly plicity: 'explicit' | 'implicit';
    readonly value: KernelExpression;
}

const reference = (name: ConformanceBinding): KernelExpression =>
    kernelFree(name, nodeProvenance);

const call = (
    name: ConformanceBinding | keyof typeof AFFINE_FORMAL_RING_BINDINGS |
        keyof typeof AFFINE_FORMAL_LOCALIZATION_BINDINGS |
        keyof typeof AFFINE_FORMAL_OVERLAP_BINDINGS,
    arguments_: readonly CallArgument[]
): KernelExpression => kernelCall(
    kernelFree(name, nodeProvenance),
    arguments_,
    nodeProvenance
);

const tau = (classifier: KernelExpression): KernelExpression =>
    call('bridge_tau', [{ plicity: 'explicit', value: classifier }]);

const equalityType = (
    classifier: KernelExpression,
    left: KernelExpression,
    right: KernelExpression
): KernelExpression => tau(call('bridge_eq', [
    { plicity: 'implicit', value: classifier },
    { plicity: 'explicit', value: left },
    { plicity: 'explicit', value: right }
]));

export const affineFormalCommRingType = (): KernelExpression =>
    tau(reference('bridge_CommRing'));

export const affineFormalRingElementType = (
    formalRing: KernelExpression
): KernelExpression => tau(call('bridge_comm_ring_carrier', [{
    plicity: 'explicit',
    value: formalRing
}]));

export const affineFormalIdentityMap = (
    formalRing: KernelExpression
): KernelExpression => call('bridge_comm_ring_hom_id', [{
    plicity: 'explicit',
    value: formalRing
}]);

export interface AffineFormalUnimodularLawInput {
    readonly formalRing: KernelExpression;
    readonly generatorTerms: readonly KernelExpression[];
    readonly coefficientTerms: readonly KernelExpression[];
}

/** Exact law target before any law witness or unimodular package exists. */
export function affineFormalUnimodularLawType(
    input: AffineFormalUnimodularLawInput
): KernelExpression {
    if (input.generatorTerms.length !== input.coefficientTerms.length) {
        throw new AlgebraFormalConformanceError(
            'COVER_ARITY_MISMATCH',
            'unimodularLaw.coefficientTerms',
            'Generator and coefficient family arities differ'
        );
    }
    const carrier = call('bridge_comm_ring_carrier', [{
        plicity: 'explicit',
        value: input.formalRing
    }]);
    const generators = buildAffineFormalFamily(
        carrier,
        input.generatorTerms
    );
    const coefficients = buildAffineFormalFamily(
        carrier,
        input.coefficientTerms
    );
    const dot = call('bridge_comm_ring_finite_dot', [
        { plicity: 'explicit', value: input.formalRing },
        { plicity: 'explicit', value: generators.length },
        { plicity: 'explicit', value: coefficients.family },
        { plicity: 'explicit', value: generators.family }
    ]);
    const one = call('bridge_comm_ring_one', [{
        plicity: 'explicit',
        value: input.formalRing
    }]);
    return equalityType(carrier, dot, one);
}

export function affineFormalCoverLawType<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    realization: AffineFormalCoverRealization<P, C, I>
): KernelExpression {
    return affineFormalUnimodularLawType({
        formalRing: realization.algebra.formalRing,
        generatorTerms: realization.generatorTerms,
        coefficientTerms: realization.coefficientTerms
    });
}

export function affineFormalInverseLawType<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    realization: AffineFormalLocalizationRealization<P, C, I>
): KernelExpression {
    const unit = buildAffineFormalLocalizationUnitTerms(realization);
    const ring = realization.target.formalRing;
    const carrier = call('bridge_comm_ring_carrier', [{
        plicity: 'explicit',
        value: ring
    }]);
    const product = call('bridge_comm_ring_mul', [
        { plicity: 'explicit', value: ring },
        { plicity: 'explicit', value: unit.mappedElement },
        { plicity: 'explicit', value: realization.inverseTerm }
    ]);
    const one = call('bridge_comm_ring_one', [{
        plicity: 'explicit',
        value: ring
    }]);
    return equalityType(carrier, product, one);
}

export function affineFormalLocalizationPropertyType<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    realization: AffineFormalLocalizationRealization<P, C, I>
): KernelExpression {
    return tau(call('bridge_IsCommRingLocalizationAt', [
        { plicity: 'implicit', value: realization.source.formalRing },
        { plicity: 'explicit', value: realization.elementTerm },
        { plicity: 'explicit', value: realization.target.formalRing },
        { plicity: 'explicit', value: realization.formalMap }
    ]));
}

export const affineFormalLocalizationUniversalFromProperty = (
    property: KernelExpression
): KernelExpression => call('bridge_sigma_Snd', [{
    plicity: 'explicit',
    value: property
}]);

export function affineFormalFaceUnitType<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(face: AffineFormalCechFaceFactor<P, C, I>): KernelExpression {
    const sourceRing = face.domain.localization.source.formalRing;
    const targetRing = face.codomain.localization.target.formalRing;
    const mapped = call('bridge_comm_ring_hom_apply', [
        { plicity: 'implicit', value: sourceRing },
        { plicity: 'implicit', value: targetRing },
        { plicity: 'explicit', value: face.codomain.localization.formalMap },
        { plicity: 'explicit', value: face.domain.productTerm }
    ]);
    return tau(call('bridge_CommRingUnitEvidence', [
        { plicity: 'implicit', value: targetRing },
        { plicity: 'explicit', value: mapped }
    ]));
}

export interface AffineFormalConformanceDeclaration {
    readonly name: string;
    readonly type: KernelExpression;
    readonly label?: string;
}

export interface AffineFormalConformanceProbeInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly artifact: AffineFormalBridgeArtifact<P, C, I>;
    readonly declarations: readonly AffineFormalConformanceDeclaration[];
    readonly sourceId?: string;
    readonly requiredModules?: readonly string[];
}

const collectReferences = (
    expression: KernelExpression
): readonly string[] => {
    const output: string[] = [];
    const seen = new Set<string>();
    const visit = (current: KernelExpression): void => {
        switch (current.tag) {
            case 'universe':
            case 'bound':
                return;
            case 'reference':
                if (!seen.has(current.name)) {
                    seen.add(current.name);
                    output.push(current.name);
                }
                return;
            case 'meta':
                current.spine.forEach(visit);
                return;
            case 'application':
                current.arguments.forEach(argument => visit(argument.value));
                return;
            case 'call':
                visit(current.callee);
                current.arguments.forEach(argument => visit(argument.value));
                return;
            case 'pi':
            case 'lambda':
                visit(current.binder.type);
                visit(current.body);
                return;
            default: {
                const exhaustive: never = current;
                return exhaustive;
            }
        }
    };
    visit(expression);
    return Object.freeze(output);
};

const validModule = (moduleId: string): boolean =>
    /^[\p{L}\p{N}_]+(?:\.[\p{L}\p{N}_]+)*$/u.test(moduleId);

const safeComment = (value: string): string =>
    value.replace(/[\r\n]+/gu, ' ').replace(/\*\//gu, '* /');

export function serializeAffineFormalConformanceProbe<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    input: AffineFormalConformanceProbeInput<P, C, I>
): SerializedProbe {
    const sourceId = input.sourceId ?? 'generated/affine-formal-conformance.lp';
    const requiredModules = input.requiredModules ?? [
        ALGEBRA_FORMAL_CONFORMANCE_PROFILE.defaultRequiredModule
    ];
    if (requiredModules.length === 0 || requiredModules.some(
        moduleId => !validModule(moduleId)
    )) {
        return fail(
            'INVALID_REQUIRED_MODULE',
            'formalConformance.requiredModules',
            'Conformance probe requires valid nonempty Lambdapi module IDs'
        );
    }
    const declarationNames = new Set<string>();
    input.declarations.forEach((declaration, index) => {
        if (declarationNames.has(declaration.name)) {
            fail(
                'DUPLICATE_INPUT_DECLARATION',
                `formalConformance.declarations[${index}].name`,
                `Duplicate input declaration '${declaration.name}'`
            );
        }
        declarationNames.add(declaration.name);
    });
    input.artifact.inputReferences.forEach((name, index) => {
        if (!declarationNames.has(name)) {
            fail(
                'MISSING_INPUT_DECLARATION',
                `formalConformance.artifact.inputReferences[${index}]`,
                `Artifact input '${name}' has no typed declaration`
            );
        }
    });
    input.declarations.forEach((declaration, index) => {
        if (!input.artifact.inputReferences.includes(declaration.name)) {
            fail(
                'EXTRA_INPUT_DECLARATION',
                `formalConformance.declarations[${index}].name`,
                `Typed declaration '${declaration.name}' is not an artifact input`
            );
        }
    });
    const allBindings = ALL_BINDINGS as Readonly<Record<string, string>>;
    const usedBindings: Record<string, string> = {
        ...input.artifact.externalBindings
    };
    const backendOwners = new Map<string, string>();
    Object.entries(usedBindings).forEach(([name, backend]) =>
        backendOwners.set(backend, name)
    );
    const preceding = new Set<string>();
    input.declarations.forEach((declaration, index) => {
        collectReferences(declaration.type).forEach(name => {
            const backend = allBindings[name];
            if (backend !== undefined) {
                const existing = backendOwners.get(backend);
                if (existing !== undefined && existing !== name) {
                    fail(
                        'DUPLICATE_BACKEND_OWNER',
                        `formalConformance.declarations[${index}].type`,
                        `Portable references '${existing}' and '${name}' map to ` +
                            `'${backend}'`
                    );
                }
                backendOwners.set(backend, name);
                usedBindings[name] = backend;
                return;
            }
            if (!preceding.has(name)) {
                fail(
                    'UNRESOLVED_DECLARATION_TYPE_REFERENCE',
                    `formalConformance.declarations[${index}].type`,
                    `Declaration type refers to non-earlier input '${name}'`
                );
            }
        });
        preceding.add(declaration.name);
    });
    const serialize = (expression: KernelExpression): string =>
        serializeKernelExpression(expression, {
            externalFreeReferences: usedBindings
        });
    const lines: string[] = [
        '/* Generated from the TypeScript emdash affine formal bridge Core. */',
        ...requiredModules.map(moduleId => `require open ${moduleId};`),
        ''
    ];
    const sourceMap: ProbeSourceMapEntry[] = [];
    const push = (line: string): number => {
        lines.push(line);
        return lines.length;
    };
    input.declarations.forEach((declaration, index) => {
        const span = sourceSpan(sourceId, index + 1, 1, index + 1, 2);
        push(`// ${safeComment(declaration.label ?? declaration.name)}; source ` +
            formatSourceSpan(span));
        const generatedLine = push(
            `symbol ${declaration.name} : ${serialize(declaration.type)};`
        );
        sourceMap.push({
            generatedLine,
            kind: 'declaration',
            label: declaration.name,
            sourceSpan: span
        });
    });
    if (input.declarations.length > 0 && input.artifact.outputs.length > 0) {
        push('');
    }
    input.artifact.outputs.forEach((output, index) => {
        const span = sourceSpan(
            sourceId,
            input.declarations.length + index + 1,
            1,
            input.declarations.length + index + 1,
            2
        );
        push(`// ${safeComment(output.label)}; source ${formatSourceSpan(span)}`);
        const generatedLine = push(
            `assert ⊢ ${serialize(output.term)} : ${serialize(output.type)};`
        );
        sourceMap.push({
            generatedLine,
            kind: 'assertion',
            label: output.label,
            sourceSpan: span
        });
    });
    return Object.freeze({
        source: `${lines.join('\n')}\n`,
        sourceMap: Object.freeze(sourceMap.map(entry => Object.freeze(entry)))
    });
}
