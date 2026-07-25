/**
 * Reviewed DIRECTED-1C section-evaluation integration.
 *
 * The exact active `piapp0` signature is imported opaquely into a descendant
 * of the reviewed DIRECTED-1B environment. Its transparent Lambdapi body is
 * deliberately not transferred. No runtime or proof-time rule is added:
 * consumers reuse generic outer-LF beta and the closed seven-rule directed
 * runtime already owned by DIRECTED-1B.
 */

import {
    CoreDirected1bCatalog,
    CoreDirected1bRuntimeProgram
} from './directed_1b';
import {
    CORE_DIRECTED_1C_PROPOSAL,
    CoreDirected1cCandidateOwnerId,
    CoreDirected1cExpression,
    CoreDirected1cOwnerProposal,
    LAMBDAPI_V32_DIRECTED_1C_OWNER_BINDING
} from './directed_1c_proposal';
import {
    CORE_DIRECTED_1C_REVIEW,
    validateCoreDirected1cReview
} from './directed_1c_review';
import {
    CoreLfBuilderTerm,
    CoreLfScopedBuilder
} from './lf_builder';
import {
    CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT,
    CoreLfChecker
} from './lf_checker';
import {
    CoreLfDeclarationEnvironment
} from './lf_declarations';
import {
    KernelExpression,
    Provenance,
    binderMode,
    kernelApplication,
    kernelBinder,
    kernelBound,
    kernelCall,
    kernelExpressionEquals,
    kernelFree,
    kernelPi,
    provenance
} from './kernel';
import {
    CORE_OWNER_SCHEMAS,
    CoreOwnerId
} from './schema';

export const CORE_DIRECTED_1C_PRIMITIVE_NAMES = Object.freeze({
    'section-object-evaluation': 'dttlf_piapp0'
} as const satisfies Record<
    CoreDirected1cCandidateOwnerId,
    string
>);

export interface CoreDirected1cPrimitive {
    readonly order: 0;
    readonly owner: CoreDirected1cCandidateOwnerId;
    readonly coreName: string;
    readonly signature: KernelExpression;
    readonly disposition: 'opaque-import';
    readonly backendName: 'piapp0';
    readonly activeAuthority: 'transparent-definition';
    readonly provenance: Provenance;
}

export type CoreDirected1cCatalogErrorCode =
    | 'UNKNOWN_CANDIDATE_OWNER'
    | 'INVALID_CANDIDATE_ARITY'
    | 'MISSING_CANDIDATE_DEPENDENCY'
    | 'FOREIGN_CANDIDATE_ENVIRONMENT';

export class CoreDirected1cCatalogError extends Error {
    constructor(
        public readonly code: CoreDirected1cCatalogErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreDirected1cCatalogError';
    }
}

const explicitFunctorial = binderMode('explicit', 'functorial');

const derived = (
    detail: string,
    source: Provenance
): Provenance => provenance('derived', detail, source.span);

const isBaseOwner = (owner: string): owner is CoreOwnerId =>
    Object.prototype.hasOwnProperty.call(CORE_OWNER_SCHEMAS, owner);

const ownerProposal = (
    owner: CoreDirected1cCandidateOwnerId
): CoreDirected1cOwnerProposal => {
    const proposal = CORE_DIRECTED_1C_PROPOSAL.owners.find(
        entry => entry.owner === owner
    );
    if (!proposal) {
        throw new CoreDirected1cCatalogError(
            'UNKNOWN_CANDIDATE_OWNER',
            `DIRECTED-1C has no reviewed owner '${owner}'`
        );
    }
    return proposal;
};

const boundVariable = (
    name: string,
    scope: readonly string[],
    source: Provenance,
    detail: string
): KernelExpression => {
    const position = scope.lastIndexOf(name);
    if (position < 0) {
        throw new CoreDirected1cCatalogError(
            'MISSING_CANDIDATE_DEPENDENCY',
            `${detail} refers to unavailable variable '${name}'`
        );
    }
    return kernelBound(
        scope.length - position - 1,
        derived(`${detail} variable ${name}`, source)
    );
};

const materializeExpression = (
    expression: CoreDirected1cExpression,
    scope: readonly string[],
    source: Provenance,
    detail: string
): KernelExpression => {
    if (expression.tag === 'variable') {
        return boundVariable(
            expression.name,
            scope,
            source,
            detail
        );
    }
    if (!isBaseOwner(expression.owner)) {
        throw new CoreDirected1cCatalogError(
            'MISSING_CANDIDATE_DEPENDENCY',
            `${detail} may use only an existing base owner; received ` +
            `'${expression.owner}'`
        );
    }
    const arguments_ = expression.arguments.map(
        (argument, index) => materializeExpression(
            argument,
            scope,
            source,
            `${detail}, ${expression.owner} argument ${index}`
        )
    );
    return kernelApplication(
        expression.owner,
        arguments_.map(value => ({ value })),
        derived(`${detail} owner ${expression.owner}`, source)
    );
};

const materializeSignature = (
    owner: CoreDirected1cOwnerProposal,
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

const freezePrimitive = (
    primitive: CoreDirected1cPrimitive
): CoreDirected1cPrimitive => Object.freeze({ ...primitive });

/**
 * Session-local catalog for the exact reviewed DIRECTED-1A + DIRECTED-1B +
 * DIRECTED-1C candidate boundary.
 */
export class CoreDirected1cCatalog {
    private readonly primitiveMap: ReadonlyMap<
        CoreDirected1cCandidateOwnerId,
        CoreDirected1cPrimitive
    >;

    private constructor(
        public readonly directed1b: CoreDirected1bCatalog,
        public readonly environment: CoreLfDeclarationEnvironment,
        public readonly primitives: readonly CoreDirected1cPrimitive[],
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
            'reviewed DIRECTED-1C primitive catalog'
        )
    ): CoreDirected1cCatalog {
        validateCoreDirected1cReview(CORE_DIRECTED_1C_REVIEW);

        const directed1b = CoreDirected1bCatalog.create(source);
        const owner = CORE_DIRECTED_1C_PROPOSAL.owners[0];
        const binding =
            LAMBDAPI_V32_DIRECTED_1C_OWNER_BINDING;
        if (
            binding.order !== owner.order ||
            binding.owner !== owner.owner ||
            binding.candidateDisposition !==
                owner.candidateDisposition ||
            binding.activeAuthority !== owner.activeAuthority
        ) {
            throw new CoreDirected1cCatalogError(
                'MISSING_CANDIDATE_DEPENDENCY',
                'DIRECTED-1C active piapp0 binding does not match its ' +
                'reviewed owner'
            );
        }

        const coreName =
            CORE_DIRECTED_1C_PRIMITIVE_NAMES[owner.owner];
        const ownerProvenance = derived(
            `reviewed DIRECTED-1C primitive ${owner.owner}`,
            source
        );
        const signature = materializeSignature(
            owner,
            ownerProvenance
        );
        /*
         * Omitting the factory deliberately inherits DIRECTED-1B's closed
         * declaration checker: generic beta plus the exact seven-rule runtime.
         */
        const environment = directed1b.environment.extend({
            name: coreName,
            type: signature,
            mode: explicitFunctorial,
            provenance: ownerProvenance,
            transparency: 'opaque'
        });
        const primitive = freezePrimitive({
            order: owner.order,
            owner: owner.owner,
            coreName,
            signature,
            disposition: owner.candidateDisposition,
            backendName: binding.serializedName,
            activeAuthority: binding.activeAuthority,
            provenance: ownerProvenance
        });

        return new CoreDirected1cCatalog(
            directed1b,
            environment,
            [primitive],
            directed1b.runtimeProgram,
            {
                ...directed1b.externalFreeReferences,
                [coreName]: binding.serializedName
            },
            directed1b.externalTransparentDefinitions
        );
    }

    primitive(
        owner: CoreDirected1cCandidateOwnerId
    ): CoreDirected1cPrimitive {
        const primitive = this.primitiveMap.get(owner);
        if (!primitive) {
            throw new CoreDirected1cCatalogError(
                'UNKNOWN_CANDIDATE_OWNER',
                `DIRECTED-1C catalog has no owner '${owner}'`
            );
        }
        return primitive;
    }

    application(
        owner: CoreDirected1cCandidateOwnerId,
        arguments_: readonly KernelExpression[],
        nodeProvenance: Provenance
    ): KernelExpression {
        const primitive = this.primitive(owner);
        const proposal = ownerProposal(owner);
        if (arguments_.length !== proposal.slots.length) {
            throw new CoreDirected1cCatalogError(
                'INVALID_CANDIDATE_ARITY',
                `DIRECTED-1C owner ${owner} expects ` +
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
        owner: CoreDirected1cCandidateOwnerId,
        arguments_: readonly CoreLfBuilderTerm[],
        nodeProvenance?: Provenance
    ): CoreLfBuilderTerm {
        const primitive = this.primitive(owner);
        const proposal = ownerProposal(owner);
        if (arguments_.length !== proposal.slots.length) {
            throw new CoreDirected1cCatalogError(
                'INVALID_CANDIDATE_ARITY',
                `DIRECTED-1C owner ${owner} expects ` +
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

    sectionObjectEvaluation(
        base: KernelExpression,
        family: KernelExpression,
        section: KernelExpression,
        point: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        return this.application(
            'section-object-evaluation',
            [base, family, section, point],
            nodeProvenance
        );
    }

    assertEnvironment(
        environment: CoreLfDeclarationEnvironment
    ): void {
        this.directed1b.assertEnvironment(environment);
        const primitive = this.primitives[0];
        const declaration = environment.lookup(primitive.coreName);
        if (
            !declaration ||
            declaration.transparency !== 'opaque' ||
            declaration.body !== undefined ||
            !kernelExpressionEquals(
                declaration.type,
                primitive.signature
            )
        ) {
            throw new CoreDirected1cCatalogError(
                'FOREIGN_CANDIDATE_ENVIRONMENT',
                'Environment does not preserve reviewed DIRECTED-1C ' +
                `primitive '${primitive.owner}'`
            );
        }
    }

    createChecker(
        environment: CoreLfDeclarationEnvironment = this.environment,
        comparisonStepLimit =
            CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT
    ): CoreLfChecker {
        this.assertEnvironment(environment);
        return this.directed1b.createChecker(
            environment,
            comparisonStepLimit
        );
    }
}
