/**
 * Reviewed DIRECTED-1A integration.
 *
 * The three categorical owners are compiled into opaque declarations in an
 * isolated LF environment. Applications use generic Pi elimination, leaving
 * the frozen base owner catalog, browser API, and MVP manifest unchanged.
 */

import {
    CORE_DIRECTED_1A_REVIEW,
    CORE_LF_CONTINUATION_PROFILE_REVIEW,
    validateCoreDirected1aReview,
    validateCoreLfContinuationProfileReview
} from './continuation_review';
import {
    CORE_DIRECTED_1A_PROPOSAL,
    CoreDirected1aCandidateOwnerId,
    CoreDirected1aOwnerProposal,
    CoreDirected1aSignatureExpression,
    LAMBDAPI_V32_DIRECTED_1A_PROPOSAL_BINDINGS
} from './directed_1a_proposal';
import {
    CoreLfBuilderTerm,
    CoreLfScopedBuilder
} from './lf_builder';
import {
    CoreLfChecker,
    createCoreLfChecker
} from './lf_checker';
import {
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
    kernelPi,
    provenance
} from './kernel';
import {
    CORE_OWNER_SCHEMAS,
    CoreOwnerId
} from './schema';

export const CORE_DIRECTED_1A_PRIMITIVE_NAMES = Object.freeze({
    'displayed-functor-category': 'dttlf_Functord_cat',
    'sigma-category': 'dttlf_Sigma_cat',
    'sigma-telescope-family': 'dttlf_Sigma_catd_functord_catd'
} as const satisfies Record<
    CoreDirected1aCandidateOwnerId,
    string
>);

export interface CoreDirected1aPrimitive {
    readonly order: number;
    readonly owner: CoreDirected1aCandidateOwnerId;
    readonly coreName: string;
    readonly signature: KernelExpression;
    readonly backendName: string;
    readonly provenance: Provenance;
}

export type CoreDirected1aCatalogErrorCode =
    | 'UNKNOWN_CANDIDATE_OWNER'
    | 'INVALID_CANDIDATE_ARITY'
    | 'MISSING_CANDIDATE_DEPENDENCY'
    | 'FOREIGN_CANDIDATE_ENVIRONMENT';

export class CoreDirected1aCatalogError extends Error {
    constructor(
        public readonly code: CoreDirected1aCatalogErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreDirected1aCatalogError';
    }
}

const explicitFunctorial: BinderMode =
    binderMode('explicit', 'functorial');

const isBaseOwner = (
    owner: string
): owner is CoreOwnerId =>
    Object.prototype.hasOwnProperty.call(CORE_OWNER_SCHEMAS, owner);

const ownerProposal = (
    owner: CoreDirected1aCandidateOwnerId
): CoreDirected1aOwnerProposal => {
    const result = CORE_DIRECTED_1A_PROPOSAL.owners.find(
        entry => entry.owner === owner
    );
    if (!result) {
        throw new CoreDirected1aCatalogError(
            'UNKNOWN_CANDIDATE_OWNER',
            `DIRECTED-1A has no reviewed owner '${owner}'`
        );
    }
    return result;
};

const derived = (
    detail: string,
    source: Provenance
): Provenance => provenance('derived', detail, source.span);

const instantiateSignatureExpression = (
    expression: CoreDirected1aSignatureExpression,
    bindings: ReadonlyMap<string, KernelExpression>,
    availablePrimitiveNames: ReadonlyMap<
        CoreDirected1aCandidateOwnerId,
        string
    >,
    source: Provenance
): KernelExpression => {
    if (expression.tag === 'slot') {
        const result = bindings.get(expression.name);
        if (!result) {
            throw new CoreDirected1aCatalogError(
                'MISSING_CANDIDATE_DEPENDENCY',
                `DIRECTED-1A signature slot '${expression.name}' is not ` +
                'available at this telescope position'
            );
        }
        return result;
    }

    const arguments_ = expression.arguments.map(argument =>
        instantiateSignatureExpression(
            argument,
            bindings,
            availablePrimitiveNames,
            source
        )
    );
    const nodeProvenance = derived(
        `DIRECTED-1A signature owner ${expression.owner}`,
        source
    );
    if (isBaseOwner(expression.owner)) {
        return kernelApplication(
            expression.owner,
            arguments_.map(value => ({ value })),
            nodeProvenance
        );
    }

    const coreName = availablePrimitiveNames.get(expression.owner);
    if (!coreName) {
        throw new CoreDirected1aCatalogError(
            'MISSING_CANDIDATE_DEPENDENCY',
            `DIRECTED-1A signature owner '${expression.owner}' is not an ` +
            'earlier primitive'
        );
    }
    const proposal = ownerProposal(expression.owner);
    if (arguments_.length !== proposal.slots.length) {
        throw new CoreDirected1aCatalogError(
            'INVALID_CANDIDATE_ARITY',
            `DIRECTED-1A owner ${expression.owner} expects ` +
            `${proposal.slots.length} arguments, received ` +
            arguments_.length
        );
    }
    return kernelCall(
        kernelFree(coreName, nodeProvenance),
        arguments_.map((value, index) => ({
            plicity: proposal.slots[index].plicity,
            value
        })),
        nodeProvenance
    );
};

const materializeSignature = (
    owner: CoreDirected1aOwnerProposal,
    availablePrimitiveNames: ReadonlyMap<
        CoreDirected1aCandidateOwnerId,
        string
    >,
    source: Provenance
): KernelExpression => {
    const build = (slotIndex: number): KernelExpression => {
        if (slotIndex === owner.slots.length) {
            const bindings = new Map(
                owner.slots.map((slot, index) => [
                    slot.name,
                    kernelBound(
                        owner.slots.length - index - 1,
                        derived(
                            `${owner.owner} result slot ${slot.name}`,
                            source
                        )
                    )
                ])
            );
            return instantiateSignatureExpression(
                owner.result,
                bindings,
                availablePrimitiveNames,
                source
            );
        }

        const slot = owner.slots[slotIndex];
        const earlierBindings = new Map(
            owner.slots.slice(0, slotIndex).map((earlier, index) => [
                earlier.name,
                kernelBound(
                    slotIndex - index - 1,
                    derived(
                        `${owner.owner} slot ${slot.name} dependency ` +
                        earlier.name,
                        source
                    )
                )
            ])
        );
        const type = instantiateSignatureExpression(
            slot.type,
            earlierBindings,
            availablePrimitiveNames,
            source
        );
        return kernelPi(
            kernelBinder(
                slot.name,
                type,
                binderMode(slot.plicity, 'functorial'),
                derived(`${owner.owner} binder ${slot.name}`, source)
            ),
            build(slotIndex + 1),
            derived(`${owner.owner} signature Pi ${slot.name}`, source)
        );
    };
    return build(0);
};

const freezePrimitive = (
    primitive: CoreDirected1aPrimitive
): CoreDirected1aPrimitive => Object.freeze({
    ...primitive
});

/**
 * Session-local compiled catalog for the exact reviewed DIRECTED-1A owners.
 */
export class CoreDirected1aCatalog {
    private readonly primitiveMap: ReadonlyMap<
        CoreDirected1aCandidateOwnerId,
        CoreDirected1aPrimitive
    >;

    private constructor(
        public readonly environment: CoreLfDeclarationEnvironment,
        public readonly primitives: readonly CoreDirected1aPrimitive[],
        public readonly externalFreeReferences: Readonly<
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
        Object.freeze(this);
    }

    static create(
        source: Provenance = provenance(
            'derived',
            'reviewed DIRECTED-1A primitive catalog'
        )
    ): CoreDirected1aCatalog {
        validateCoreLfContinuationProfileReview(
            CORE_LF_CONTINUATION_PROFILE_REVIEW
        );
        validateCoreDirected1aReview(CORE_DIRECTED_1A_REVIEW);

        let environment = CoreLfDeclarationEnvironment.empty();
        const availablePrimitiveNames = new Map<
            CoreDirected1aCandidateOwnerId,
            string
        >();
        const primitives: CoreDirected1aPrimitive[] = [];
        const externalFreeReferences: Record<string, string> = {};

        for (const owner of CORE_DIRECTED_1A_PROPOSAL.owners) {
            const binding =
                LAMBDAPI_V32_DIRECTED_1A_PROPOSAL_BINDINGS[owner.order];
            if (!binding || binding.owner !== owner.owner) {
                throw new CoreDirected1aCatalogError(
                    'MISSING_CANDIDATE_DEPENDENCY',
                    `DIRECTED-1A binding ${owner.order} does not match ` +
                    owner.owner
                );
            }
            const coreName =
                CORE_DIRECTED_1A_PRIMITIVE_NAMES[owner.owner];
            const ownerProvenance = derived(
                `reviewed DIRECTED-1A primitive ${owner.owner}`,
                source
            );
            const signature = materializeSignature(
                owner,
                availablePrimitiveNames,
                ownerProvenance
            );
            environment = environment.extend({
                name: coreName,
                type: signature,
                mode: explicitFunctorial,
                provenance: ownerProvenance
            });
            const primitive = freezePrimitive({
                order: owner.order,
                owner: owner.owner,
                coreName,
                signature,
                backendName: binding.serializedName,
                provenance: ownerProvenance
            });
            primitives.push(primitive);
            availablePrimitiveNames.set(owner.owner, coreName);
            externalFreeReferences[coreName] = binding.serializedName;
        }

        return new CoreDirected1aCatalog(
            environment,
            primitives,
            externalFreeReferences
        );
    }

    primitive(
        owner: CoreDirected1aCandidateOwnerId
    ): CoreDirected1aPrimitive {
        const primitive = this.primitiveMap.get(owner);
        if (!primitive) {
            throw new CoreDirected1aCatalogError(
                'UNKNOWN_CANDIDATE_OWNER',
                `DIRECTED-1A catalog has no owner '${owner}'`
            );
        }
        return primitive;
    }

    application(
        owner: CoreDirected1aCandidateOwnerId,
        arguments_: readonly KernelExpression[],
        nodeProvenance: Provenance
    ): KernelExpression {
        const primitive = this.primitive(owner);
        const proposal = ownerProposal(owner);
        if (arguments_.length !== proposal.slots.length) {
            throw new CoreDirected1aCatalogError(
                'INVALID_CANDIDATE_ARITY',
                `DIRECTED-1A owner ${owner} expects ` +
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
        owner: CoreDirected1aCandidateOwnerId,
        arguments_: readonly CoreLfBuilderTerm[],
        nodeProvenance?: Provenance
    ): CoreLfBuilderTerm {
        const primitive = this.primitive(owner);
        const proposal = ownerProposal(owner);
        if (arguments_.length !== proposal.slots.length) {
            throw new CoreDirected1aCatalogError(
                'INVALID_CANDIDATE_ARITY',
                `DIRECTED-1A owner ${owner} expects ` +
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

    displayedFunctorCategory(
        base: KernelExpression,
        sourceFamily: KernelExpression,
        targetFamily: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        return this.application(
            'displayed-functor-category',
            [base, sourceFamily, targetFamily],
            nodeProvenance
        );
    }

    sigmaCategory(
        base: KernelExpression,
        family: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        return this.application(
            'sigma-category',
            [base, family],
            nodeProvenance
        );
    }

    sigmaTelescopeFamily(
        base: KernelExpression,
        firstFamily: KernelExpression,
        telescope: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        return this.application(
            'sigma-telescope-family',
            [base, firstFamily, telescope],
            nodeProvenance
        );
    }

    assertEnvironment(
        environment: CoreLfDeclarationEnvironment
    ): void {
        for (const primitive of this.primitives) {
            const declaration = environment.lookup(primitive.coreName);
            if (
                !declaration ||
                declaration.body !== undefined ||
                declaration.transparency !== 'opaque' ||
                !kernelExpressionEquals(
                    declaration.type,
                    primitive.signature
                )
            ) {
                throw new CoreDirected1aCatalogError(
                    'FOREIGN_CANDIDATE_ENVIRONMENT',
                    `Environment does not preserve reviewed DIRECTED-1A ` +
                    `primitive '${primitive.owner}'`
                );
            }
        }
    }

    createChecker(
        environment: CoreLfDeclarationEnvironment = this.environment
    ): CoreLfChecker {
        this.assertEnvironment(environment);
        return createCoreLfChecker(environment);
    }
}
