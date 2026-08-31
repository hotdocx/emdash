/** Deterministic named artifact and LF-probe boundary for the affine bridge. */

import {
    KernelExpression,
    assertSafeIdentifier,
    kernelCall,
    kernelFree,
    provenance,
    sourceSpan
} from './kernel';
import { serializeCoreExpression } from './core_serialization';
import { CoreLfDeclarationEnvironment } from './lf_declarations';
import {
    CoreLfKernelProbe,
    serializeCoreLfKernelProbe
} from './lf_probe';
import { SerializedProbe } from './probe';
import { serializeCoreLfWorkspaceCanonicalJson } from './lf_workspace';
import { AFFINE_FORMAL_RING_BINDINGS } from './algebra_formal_reifier';
import {
    AFFINE_FORMAL_COVER_BINDINGS,
    buildAffineFormalCoverTerms
} from './algebra_formal_cover';
import {
    AFFINE_FORMAL_LOCALIZATION_BINDINGS,
    buildAffineFormalCoverLocalizationTerms
} from './algebra_formal_localization';
import { AFFINE_FORMAL_OVERLAP_BINDINGS } from './algebra_formal_overlap';
import {
    AFFINE_FORMAL_CECH_BINDINGS,
    AffineFormalCechPresentation
} from './algebra_formal_cech';
import { AlgebraElement, AlgebraParent } from './algebra_parent';

export const ALGEBRA_FORMAL_ARTIFACT_PROFILE = Object.freeze({
    revision: 'emdash-affine-formal-artifact-v1' as const,
    manifestRevision: 'emdash-affine-formal-artifact-manifest-v1' as const,
    outputProfile: 'typed-ordered-assertions' as const,
    declarationEnvironment: 'caller-supplied-checked' as const,
    semanticStringTemplates: false as const,
    addsCoreOwner: false as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export const AFFINE_FORMAL_ARTIFACT_BINDINGS = Object.freeze({
    bridge_tau: 'τ',
    bridge_CommRingZariskiCoverPresentation:
        'CommRingZariskiCoverPresentation',
    bridge_CommRingZariskiCoverFamily: 'CommRingZariskiCoverFamily',
    bridge_CommRingLocalizationAt: 'CommRingLocalizationAt',
    bridge_CommRingHom: 'CommRingHom',
    bridge_CommRingLocalizationAgreement: 'CommRingLocalizationAgreement',
    bridge_comm_ring_hom_id: 'comm_ring_hom_id',
    bridge_sigma_Snd: 'sigma_Snd'
});

const ALL_BINDINGS = Object.freeze({
    ...AFFINE_FORMAL_RING_BINDINGS,
    ...AFFINE_FORMAL_COVER_BINDINGS,
    ...AFFINE_FORMAL_LOCALIZATION_BINDINGS,
    ...AFFINE_FORMAL_OVERLAP_BINDINGS,
    ...AFFINE_FORMAL_CECH_BINDINGS,
    ...AFFINE_FORMAL_ARTIFACT_BINDINGS
});

export type AlgebraFormalArtifactErrorCode =
    | 'INVALID_ARTIFACT_ID'
    | 'DUPLICATE_OUTPUT'
    | 'DUPLICATE_BACKEND_OWNER'
    | 'UNRESOLVED_REFERENCE'
    | 'MISSING_BINDING_DECLARATION';

export class AlgebraFormalArtifactError extends Error {
    constructor(
        public readonly code: AlgebraFormalArtifactErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraFormalArtifactError';
    }
}

const fail = (
    code: AlgebraFormalArtifactErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraFormalArtifactError(code, path, message);
};

const nodeProvenance = provenance('derived', 'affine formal bridge artifact');

type ArtifactBinding = keyof typeof AFFINE_FORMAL_ARTIFACT_BINDINGS;

interface CallArgument {
    readonly plicity: 'explicit' | 'implicit';
    readonly value: KernelExpression;
}

const call = (
    name: ArtifactBinding | keyof typeof AFFINE_FORMAL_CECH_BINDINGS,
    arguments_: readonly CallArgument[]
): KernelExpression => kernelCall(
    kernelFree(name, nodeProvenance),
    arguments_,
    nodeProvenance
);

const decodedType = (classifier: KernelExpression): KernelExpression =>
    kernelCall(
        kernelFree('bridge_tau', nodeProvenance),
        [{ plicity: 'explicit', value: classifier }],
        nodeProvenance
    );

const collectReferences = (
    expressions: readonly KernelExpression[]
): readonly string[] => {
    const names: string[] = [];
    const seen = new Set<string>();
    const visit = (expression: KernelExpression): void => {
        switch (expression.tag) {
            case 'universe':
            case 'bound':
                return;
            case 'reference':
                if (!seen.has(expression.name)) {
                    seen.add(expression.name);
                    names.push(expression.name);
                }
                return;
            case 'meta':
                expression.spine.forEach(visit);
                return;
            case 'application':
                expression.arguments.forEach(argument => visit(argument.value));
                return;
            case 'call':
                visit(expression.callee);
                expression.arguments.forEach(argument => visit(argument.value));
                return;
            case 'pi':
            case 'lambda':
                visit(expression.binder.type);
                visit(expression.body);
                return;
            default: {
                const exhaustive: never = expression;
                return exhaustive;
            }
        }
    };
    expressions.forEach(visit);
    return Object.freeze(names);
};

export interface AffineFormalArtifactOutput {
    readonly name: string;
    readonly label: string;
    readonly type: KernelExpression;
    readonly term: KernelExpression;
}

export interface AffineFormalBridgeArtifact<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly profileRevision: typeof ALGEBRA_FORMAL_ARTIFACT_PROFILE.revision;
    readonly artifactId: string;
    readonly presentation: AffineFormalCechPresentation<P, C, I>;
    readonly outputs: readonly AffineFormalArtifactOutput[];
    readonly externalBindings: Readonly<Record<string, string>>;
    readonly freeReferences: readonly string[];
    readonly inputReferences: readonly string[];
}

const output = (
    name: string,
    label: string,
    type: KernelExpression,
    term: KernelExpression
): AffineFormalArtifactOutput => Object.freeze({ name, label, type, term });

export function buildAffineFormalBridgeArtifact<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    artifactId: string,
    presentation: AffineFormalCechPresentation<P, C, I>
): AffineFormalBridgeArtifact<P, C, I> {
    try {
        assertSafeIdentifier(artifactId, 'Affine formal artifact ID');
    } catch (error: unknown) {
        return fail(
            'INVALID_ARTIFACT_ID',
            'formalArtifact.artifactId',
            error instanceof Error ? error.message : 'Invalid artifact ID'
        );
    }
    const overlap = presentation.overlap;
    const coverRealization = overlap.cover;
    const sourceRing = coverRealization.algebra.formalRing;
    const cover = buildAffineFormalCoverTerms(coverRealization);
    const degreeZero = overlap.simplices.filter(
        simplex => simplex.simplex.degree === 0
    );
    const coverFamily = buildAffineFormalCoverLocalizationTerms(
        coverRealization,
        degreeZero.map(simplex => simplex.localization)
    );
    const outputs: AffineFormalArtifactOutput[] = [
        output(
            `${artifactId}_cover`,
            'formal algebraic Zariski cover',
            decodedType(call('bridge_CommRingZariskiCoverPresentation', [{
                plicity: 'explicit',
                value: sourceRing
            }])),
            cover.cover
        ),
        output(
            `${artifactId}_cover_family`,
            'formal Zariski cover with chosen localizations',
            decodedType(call('bridge_CommRingZariskiCoverFamily', [{
                plicity: 'explicit',
                value: sourceRing
            }])),
            coverFamily.coverFamily
        )
    ];
    overlap.simplices.forEach(simplex => {
        const suffix = simplex.simplex.indices.join('_');
        outputs.push(
            output(
                `${artifactId}_simplex_${suffix}_localization`,
                `formal localization at simplex ${simplex.simplex.indices.join(',')}`,
                decodedType(call('bridge_CommRingLocalizationAt', [
                    { plicity: 'explicit', value: sourceRing },
                    { plicity: 'explicit', value: simplex.productTerm }
                ])),
                simplex.terms.localization
            ),
            output(
                `${artifactId}_simplex_${suffix}_chart`,
                `formal affine chart at simplex ${simplex.simplex.indices.join(',')}`,
                decodedType(presentation.degrees[0]?.chartCarrier ??
                    call('bridge_Obj', [{
                        plicity: 'explicit',
                        value: call('bridge_AffineSpecBigSlice_cat', [{
                            plicity: 'explicit',
                            value: sourceRing
                        }])
                    }])),
                simplex.terms.chart
            )
        );
    });
    overlap.faces.forEach(face => {
        const suffix = `${face.codomain.simplex.indices.join('_')}_` +
            `drop_${face.face.removedPosition}`;
        const domainRing = face.domain.localization.target.formalRing;
        const codomainRing = face.codomain.localization.target.formalRing;
        outputs.push(
            output(
                `${artifactId}_face_${suffix}_factor`,
                `formal localization factor for face ${suffix}`,
                decodedType(face.factorType),
                face.factor
            ),
            output(
                `${artifactId}_face_${suffix}_map`,
                `formal coordinate restriction for face ${suffix}`,
                decodedType(call('bridge_CommRingHom', [
                    { plicity: 'explicit', value: domainRing },
                    { plicity: 'explicit', value: codomainRing }
                ])),
                face.map
            ),
            output(
                `${artifactId}_face_${suffix}_agreement`,
                `formal ambient-map agreement for face ${suffix}`,
                decodedType(call('bridge_CommRingLocalizationAgreement', [
                    { plicity: 'implicit', value: sourceRing },
                    { plicity: 'implicit', value: domainRing },
                    { plicity: 'implicit', value: codomainRing },
                    { plicity: 'explicit', value: face.domain.localization.formalMap },
                    { plicity: 'explicit', value: face.map },
                    { plicity: 'explicit', value: face.codomain.localization.formalMap }
                ])),
                face.agreement
            )
        );
    });
    presentation.degrees.forEach(degree => outputs.push(output(
        `${artifactId}_degree_${degree.degree}`,
        `packed formal Cech degree ${degree.degree}`,
        decodedType(degree.presentationType),
        degree.presentation
    )));
    outputs.push(output(
        `${artifactId}_degrees`,
        'packed degreewise formal Cech presentation',
        decodedType(call('bridge_FiniteFamily', [
            { plicity: 'explicit', value: presentation.packedCarrier },
            {
                plicity: 'explicit',
                value: presentation.degreePresentations.length
            }
        ])),
        presentation.degreePresentations.family
    ));
    const names = new Set<string>();
    outputs.forEach((entry, index) => {
        if (names.has(entry.name)) {
            fail(
                'DUPLICATE_OUTPUT',
                `formalArtifact.outputs[${index}].name`,
                `Duplicate artifact output '${entry.name}'`
            );
        }
        names.add(entry.name);
    });
    const freeReferences = collectReferences(outputs.flatMap(entry => [
        entry.type,
        entry.term
    ]));
    const allBindings = ALL_BINDINGS as Readonly<Record<string, string>>;
    const externalBindings: Record<string, string> = {};
    const backendOwners = new Map<string, string>();
    freeReferences.forEach(name => {
        const backendName = allBindings[name];
        if (backendName === undefined) return;
        const existing = backendOwners.get(backendName);
        if (existing !== undefined && existing !== name) {
            fail(
                'DUPLICATE_BACKEND_OWNER',
                `formalArtifact.externalBindings.${name}`,
                `Portable references '${existing}' and '${name}' both map to ` +
                    `'${backendName}'`
            );
        }
        backendOwners.set(backendName, name);
        externalBindings[name] = backendName;
    });
    const externalNames = new Set(Object.keys(externalBindings));
    return Object.freeze({
        profileRevision: ALGEBRA_FORMAL_ARTIFACT_PROFILE.revision,
        artifactId,
        presentation,
        outputs: Object.freeze(outputs),
        externalBindings: Object.freeze(externalBindings),
        freeReferences,
        inputReferences: Object.freeze(freeReferences.filter(
            name => !externalNames.has(name)
        ))
    });
}

export function serializeAffineFormalBridgeArtifactCanonicalJson<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    artifact: AffineFormalBridgeArtifact<P, C, I>
): string {
    return serializeCoreLfWorkspaceCanonicalJson({
        revision: ALGEBRA_FORMAL_ARTIFACT_PROFILE.manifestRevision,
        artifactId: artifact.artifactId,
        externalBindings: artifact.externalBindings,
        freeReferences: artifact.freeReferences,
        inputReferences: artifact.inputReferences,
        outputs: artifact.outputs.map(entry => ({
            name: entry.name,
            label: entry.label,
            type: serializeCoreExpression(entry.type),
            term: serializeCoreExpression(entry.term)
        }))
    }, 'affineFormalBridgeArtifact');
}

export function createAffineFormalBridgeKernelProbe<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    artifact: AffineFormalBridgeArtifact<P, C, I>,
    environment: CoreLfDeclarationEnvironment,
    sourceId = 'generated/affine-formal-bridge.ts'
): CoreLfKernelProbe {
    Object.keys(artifact.externalBindings).forEach(name => {
        if (environment.lookup(name) === undefined) {
            return fail(
                'MISSING_BINDING_DECLARATION',
                `formalArtifact.externalBindings.${name}`,
                `Reviewed active binding '${name}' has no checked signature mirror`
            );
        }
    });
    artifact.inputReferences.forEach((name, index) => {
        if (environment.lookup(name) === undefined) {
            return fail(
                'UNRESOLVED_REFERENCE',
                `formalArtifact.inputReferences[${index}]`,
                `Checked declaration environment has no '${name}'`
            );
        }
    });
    return Object.freeze({
        environment,
        externalFreeReferences: artifact.externalBindings,
        assertions: Object.freeze(artifact.outputs.map((entry, index) => ({
            label: entry.label,
            term: entry.term,
            type: entry.type,
            span: sourceSpan(sourceId, index + 1, 1, index + 1, 2)
        })))
    });
}

export function serializeAffineFormalBridgeKernelProbe<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    artifact: AffineFormalBridgeArtifact<P, C, I>,
    environment: CoreLfDeclarationEnvironment,
    sourceId?: string
): SerializedProbe {
    return serializeCoreLfKernelProbe(
        createAffineFormalBridgeKernelProbe(artifact, environment, sourceId)
    );
}
