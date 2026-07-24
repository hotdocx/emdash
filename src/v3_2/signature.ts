/**
 * Declarative dependent type signatures for backend-neutral Core owners.
 *
 * Signature expressions may mention only the meta-level universe, earlier
 * telescope slots, and semantic owner applications. The future checker can
 * therefore interpret every owner uniformly without an owner-named branch.
 */

import {
    BinderMode,
    KernelExpression,
    Provenance,
    binderMode,
    kernelApplication,
    kernelBinder,
    kernelBound,
    kernelPi,
    kernelUniverse,
    provenance
} from './kernel';
import {
    CORE_OWNER_SCHEMAS,
    CoreOwnerId,
    Plicity
} from './schema';

export type CoreSignatureExpression =
    | { readonly tag: 'universe' }
    | {
        readonly tag: 'slot';
        readonly name: string;
    }
    | {
        readonly tag: 'owner-application';
        readonly owner: CoreOwnerId;
        readonly arguments: readonly CoreSignatureExpression[];
    };

export interface CoreOwnerTypedSlotSchema {
    readonly name: string;
    readonly plicity: Plicity;
    readonly type: CoreSignatureExpression;
}

export interface CoreOwnerTypeSchema {
    readonly slots: readonly CoreOwnerTypedSlotSchema[];
    readonly result: CoreSignatureExpression;
}

export type CoreOwnerTypeCatalog = {
    readonly [Owner in CoreOwnerId]: CoreOwnerTypeSchema;
};

const universe = (): CoreSignatureExpression => ({ tag: 'universe' });

const slotReference = (name: string): CoreSignatureExpression => ({
    tag: 'slot',
    name
});

const ownerApplication = (
    owner: CoreOwnerId,
    ...arguments_: readonly CoreSignatureExpression[]
): CoreSignatureExpression => ({
    tag: 'owner-application',
    owner,
    arguments: arguments_
});

const typedSlot = (
    name: string,
    plicity: Plicity,
    type: CoreSignatureExpression
): CoreOwnerTypedSlotSchema => ({
    name,
    plicity,
    type
});

const explicit = (
    name: string,
    type: CoreSignatureExpression
): CoreOwnerTypedSlotSchema => typedSlot(name, 'explicit', type);

const implicit = (
    name: string,
    type: CoreSignatureExpression
): CoreOwnerTypedSlotSchema => typedSlot(name, 'implicit', type);

const A = slotReference('A');
const B = slotReference('B');
const F = slotReference('F');
const G = slotReference('G');
const X = slotReference('X');
const Y = slotReference('Y');

const coreUniverse = universe();
const groupoidUniverse = ownerApplication('groupoid-universe');
const categoryUniverse = ownerApplication('category-universe');

const decoded = (
    classifier: CoreSignatureExpression
): CoreSignatureExpression => ownerApplication('decode', classifier);

const objectClassifier = (
    category: CoreSignatureExpression
): CoreSignatureExpression => ownerApplication(
    'object-classifier',
    category
);

const functorClassifier = (
    source: CoreSignatureExpression,
    target: CoreSignatureExpression
): CoreSignatureExpression => ownerApplication(
    'functor-classifier',
    source,
    target
);

const homClassifier = (
    category: CoreSignatureExpression,
    source: CoreSignatureExpression,
    target: CoreSignatureExpression
): CoreSignatureExpression => ownerApplication(
    'hom-classifier',
    category,
    source,
    target
);

const transforClassifier = (
    sourceCategory: CoreSignatureExpression,
    targetCategory: CoreSignatureExpression,
    sourceFunctor: CoreSignatureExpression,
    targetFunctor: CoreSignatureExpression
): CoreSignatureExpression => ownerApplication(
    'transfor-classifier',
    sourceCategory,
    targetCategory,
    sourceFunctor,
    targetFunctor
);

const oppositeCategory = (
    category: CoreSignatureExpression
): CoreSignatureExpression => ownerApplication(
    'opposite-category',
    category
);

const homCategory = (
    category: CoreSignatureExpression,
    source: CoreSignatureExpression,
    target: CoreSignatureExpression
): CoreSignatureExpression => ownerApplication(
    'hom-category',
    category,
    source,
    target
);

const transforCategory = (
    sourceCategory: CoreSignatureExpression,
    targetCategory: CoreSignatureExpression,
    sourceFunctor: CoreSignatureExpression,
    targetFunctor: CoreSignatureExpression
): CoreSignatureExpression => ownerApplication(
    'transfor-category',
    sourceCategory,
    targetCategory,
    sourceFunctor,
    targetFunctor
);

const displayedCategoryCategory = (
    base: CoreSignatureExpression
): CoreSignatureExpression => ownerApplication(
    'displayed-category-category',
    base
);

const displayedFamilyType = (
    base: CoreSignatureExpression
): CoreSignatureExpression => decoded(
    objectClassifier(displayedCategoryCategory(base))
);

const functorObject = (
    sourceCategory: CoreSignatureExpression,
    targetCategory: CoreSignatureExpression,
    functor: CoreSignatureExpression,
    object: CoreSignatureExpression
): CoreSignatureExpression => ownerApplication(
    'functor-object',
    sourceCategory,
    targetCategory,
    functor,
    object
);

const objectType = (
    category: CoreSignatureExpression
): CoreSignatureExpression => decoded(objectClassifier(category));

const functorType = (
    source: CoreSignatureExpression,
    target: CoreSignatureExpression
): CoreSignatureExpression => decoded(functorClassifier(source, target));

const homType = (
    category: CoreSignatureExpression,
    source: CoreSignatureExpression,
    target: CoreSignatureExpression
): CoreSignatureExpression => decoded(
    homClassifier(category, source, target)
);

const transforType = (
    sourceCategory: CoreSignatureExpression,
    targetCategory: CoreSignatureExpression,
    sourceFunctor: CoreSignatureExpression,
    targetFunctor: CoreSignatureExpression
): CoreSignatureExpression => decoded(transforClassifier(
    sourceCategory,
    targetCategory,
    sourceFunctor,
    targetFunctor
));

const functorSlot = (
    name: string,
    plicity: Plicity,
    source: CoreSignatureExpression,
    target: CoreSignatureExpression
): CoreOwnerTypedSlotSchema => typedSlot(
    name,
    plicity,
    functorType(source, target)
);

const objectSlot = (
    name: string,
    plicity: Plicity,
    category: CoreSignatureExpression
): CoreOwnerTypedSlotSchema => typedSlot(
    name,
    plicity,
    objectType(category)
);

/**
 * Complete dependent signatures for the current owner catalog.
 *
 * Repeated `name`/`plicity` fields intentionally mirror the arity catalog:
 * validation below makes divergence an immediate error.
 */
export const CORE_OWNER_TYPE_SCHEMAS = {
    'groupoid-universe': {
        slots: [],
        result: coreUniverse
    },
    'category-universe': {
        slots: [],
        result: coreUniverse
    },
    decode: {
        slots: [
            explicit('classifier', groupoidUniverse)
        ],
        result: coreUniverse
    },
    'object-classifier': {
        slots: [
            explicit('A', categoryUniverse)
        ],
        result: groupoidUniverse
    },
    'functor-classifier': {
        slots: [
            explicit('A', categoryUniverse),
            explicit('B', categoryUniverse)
        ],
        result: groupoidUniverse
    },
    'hom-classifier': {
        slots: [
            explicit('A', categoryUniverse),
            objectSlot('X', 'explicit', A),
            objectSlot('Y', 'explicit', A)
        ],
        result: groupoidUniverse
    },
    'transfor-classifier': {
        slots: [
            implicit('A', categoryUniverse),
            implicit('B', categoryUniverse),
            functorSlot('F', 'explicit', A, B),
            functorSlot('G', 'explicit', A, B)
        ],
        result: groupoidUniverse
    },
    'category-of-categories': {
        slots: [],
        result: categoryUniverse
    },
    'opposite-category': {
        slots: [
            explicit('A', categoryUniverse)
        ],
        result: categoryUniverse
    },
    'hom-category': {
        slots: [
            explicit('A', categoryUniverse),
            objectSlot('X', 'explicit', A),
            objectSlot('Y', 'explicit', A)
        ],
        result: categoryUniverse
    },
    'transfor-category': {
        slots: [
            implicit('A', categoryUniverse),
            implicit('B', categoryUniverse),
            functorSlot('F', 'explicit', A, B),
            functorSlot('G', 'explicit', A, B)
        ],
        result: categoryUniverse
    },
    'displayed-category-category': {
        slots: [
            explicit('K', categoryUniverse)
        ],
        result: categoryUniverse
    },
    'internal-hom-source': {
        slots: [
            implicit('A', categoryUniverse),
            implicit('B', categoryUniverse),
            functorSlot('F', 'explicit', B, A)
        ],
        result: functorType(
            oppositeCategory(A),
            displayedCategoryCategory(B)
        )
    },
    'internal-hom-target': {
        slots: [
            implicit('A', categoryUniverse),
            implicit('B', categoryUniverse),
            functorSlot('F', 'explicit', B, A)
        ],
        result: functorType(
            A,
            displayedCategoryCategory(oppositeCategory(B))
        )
    },
    'displayed-pullback': {
        slots: [
            implicit('A', categoryUniverse),
            implicit('B', categoryUniverse),
            explicit('E', displayedFamilyType(B)),
            functorSlot('F', 'explicit', A, B)
        ],
        result: displayedFamilyType(A)
    },
    'constant-displayed-family': {
        slots: [
            explicit('K', categoryUniverse),
            explicit('A', categoryUniverse)
        ],
        result: displayedFamilyType(slotReference('K'))
    },
    'section-category': {
        slots: [
            implicit('K', categoryUniverse),
            explicit('E', displayedFamilyType(slotReference('K')))
        ],
        result: categoryUniverse
    },
    'functor-object': {
        slots: [
            implicit('A', categoryUniverse),
            implicit('B', categoryUniverse),
            functorSlot('F', 'explicit', A, B),
            objectSlot('X', 'explicit', A)
        ],
        result: objectType(B)
    },
    'functor-hom-full': {
        slots: [
            implicit('A', categoryUniverse),
            implicit('B', categoryUniverse),
            functorSlot('F', 'explicit', A, B),
            objectSlot('X', 'implicit', A),
            objectSlot('Y', 'implicit', A)
        ],
        result: functorType(
            homCategory(A, X, Y),
            homCategory(
                B,
                functorObject(A, B, F, X),
                functorObject(A, B, F, Y)
            )
        )
    },
    'functor-hom-capped': {
        slots: [
            implicit('A', categoryUniverse),
            implicit('B', categoryUniverse),
            functorSlot('F', 'explicit', A, B),
            objectSlot('X', 'implicit', A),
            objectSlot('Y', 'implicit', A),
            explicit('f', homType(A, X, Y))
        ],
        result: homType(
            B,
            functorObject(A, B, F, X),
            functorObject(A, B, F, Y)
        )
    },
    'transfor-component-full': {
        slots: [
            implicit('A', categoryUniverse),
            implicit('B', categoryUniverse),
            functorSlot('F', 'implicit', A, B),
            functorSlot('G', 'implicit', A, B),
            objectSlot('Y', 'explicit', A)
        ],
        result: functorType(
            transforCategory(A, B, F, G),
            homCategory(
                B,
                functorObject(A, B, F, Y),
                functorObject(A, B, G, Y)
            )
        )
    },
    'transfor-component-capped': {
        slots: [
            implicit('A', categoryUniverse),
            implicit('B', categoryUniverse),
            functorSlot('F', 'implicit', A, B),
            functorSlot('G', 'implicit', A, B),
            objectSlot('Y', 'explicit', A),
            explicit('eta', transforType(A, B, F, G))
        ],
        result: homType(
            B,
            functorObject(A, B, F, Y),
            functorObject(A, B, G, Y)
        )
    },
    'transfor-hom-full': {
        slots: [
            implicit('A', categoryUniverse),
            implicit('B', categoryUniverse),
            functorSlot('F', 'implicit', A, B),
            functorSlot('G', 'implicit', A, B),
            objectSlot('X', 'implicit', A),
            objectSlot('Y', 'implicit', A),
            explicit('eta', transforType(A, B, F, G))
        ],
        result: functorType(
            homCategory(A, X, Y),
            homCategory(
                B,
                functorObject(A, B, F, X),
                functorObject(A, B, G, Y)
            )
        )
    },
    'transfor-hom-capped': {
        slots: [
            implicit('A', categoryUniverse),
            implicit('B', categoryUniverse),
            functorSlot('F', 'implicit', A, B),
            functorSlot('G', 'implicit', A, B),
            objectSlot('X', 'implicit', A),
            objectSlot('Y', 'implicit', A),
            explicit('eta', transforType(A, B, F, G)),
            explicit('f', homType(A, X, Y))
        ],
        result: homType(
            B,
            functorObject(A, B, F, X),
            functorObject(A, B, G, Y)
        )
    }
} as const satisfies CoreOwnerTypeCatalog;

export type CoreOwnerTypeCatalogInput = Readonly<
    Record<string, CoreOwnerTypeSchema | undefined>
>;

function validateSignatureExpression(
    expression: CoreSignatureExpression,
    allowedSlots: ReadonlySet<string>,
    role: string
): void {
    switch (expression.tag) {
        case 'universe':
            return;
        case 'slot':
            if (!allowedSlots.has(expression.name)) {
                throw new Error(
                    `${role} refers to unavailable slot '${expression.name}'`
                );
            }
            return;
        case 'owner-application': {
            const owner = CORE_OWNER_SCHEMAS[expression.owner];
            if (expression.arguments.length !== owner.slots.length) {
                throw new Error(
                    `${role} applies owner ${expression.owner} to ` +
                    `${expression.arguments.length} arguments, expected ` +
                    owner.slots.length
                );
            }
            expression.arguments.forEach((argument, index) =>
                validateSignatureExpression(
                    argument,
                    allowedSlots,
                    `${role}, ${expression.owner} argument ${index}`
                )
            );
            return;
        }
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
}

/**
 * Validate exact owner coverage and every dependent telescope boundary.
 */
export function validateCoreOwnerTypeCatalog(
    catalog: CoreOwnerTypeCatalogInput = CORE_OWNER_TYPE_SCHEMAS
): void {
    const ownerIds = Object.keys(CORE_OWNER_SCHEMAS) as CoreOwnerId[];
    const catalogIds = Object.keys(catalog);

    for (const catalogId of catalogIds) {
        if (!(catalogId in CORE_OWNER_SCHEMAS)) {
            throw new Error(
                `Core owner type catalog has unknown owner '${catalogId}'`
            );
        }
    }

    for (const ownerId of ownerIds) {
        const signature = catalog[ownerId];
        if (!signature) {
            throw new Error(
                `Core owner type catalog is missing owner '${ownerId}'`
            );
        }
        const owner = CORE_OWNER_SCHEMAS[ownerId];
        if (signature.slots.length !== owner.slots.length) {
            throw new Error(
                `Core owner ${ownerId} type signature has ` +
                `${signature.slots.length} slots, expected ` +
                owner.slots.length
            );
        }

        const earlierSlots = new Set<string>();
        signature.slots.forEach((typed, index) => {
            const declared = owner.slots[index];
            if (
                typed.name !== declared.name ||
                typed.plicity !== declared.plicity
            ) {
                throw new Error(
                    `Core owner ${ownerId} typed slot ${index} is ` +
                    `${typed.plicity} ${typed.name}, expected ` +
                    `${declared.plicity} ${declared.name}`
                );
            }
            validateSignatureExpression(
                typed.type,
                earlierSlots,
                `Core owner ${ownerId} slot ${typed.name} type`
            );
            earlierSlots.add(typed.name);
        });

        validateSignatureExpression(
            signature.result,
            earlierSlots,
            `Core owner ${ownerId} result type`
        );
    }
}

const signatureProvenance = (
    owner: CoreOwnerId,
    role: string,
    nodeProvenance: Provenance
): Provenance => provenance(
    'derived',
    `${owner} ${role} from the Core owner type signature`,
    nodeProvenance.span
);

export function instantiateCoreSignatureExpression(
    expression: CoreSignatureExpression,
    bindings: Readonly<Record<string, KernelExpression>>,
    nodeProvenance: Provenance,
    detail = 'type expression'
): KernelExpression {
    switch (expression.tag) {
        case 'universe':
            return kernelUniverse(nodeProvenance);
        case 'slot': {
            const value = bindings[expression.name];
            if (!value) {
                throw new Error(
                    `Cannot instantiate Core signature ${detail}: slot ` +
                    `'${expression.name}' has no value`
                );
            }
            return value;
        }
        case 'owner-application':
            return kernelApplication(
                expression.owner,
                expression.arguments.map(argument => ({
                    value: instantiateCoreSignatureExpression(
                        argument,
                        bindings,
                        nodeProvenance,
                        detail
                    )
                })),
                nodeProvenance
            );
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
}

function argumentBindings(
    owner: CoreOwnerId,
    arguments_: readonly KernelExpression[]
): Readonly<Record<string, KernelExpression>> {
    const slots = CORE_OWNER_SCHEMAS[owner].slots;
    return Object.fromEntries(
        arguments_.map((argument, index) => [
            slots[index].name,
            argument
        ])
    );
}

export function coreOwnerSlotType(
    owner: CoreOwnerId,
    slotIndex: number,
    earlierArguments: readonly KernelExpression[],
    nodeProvenance: Provenance
): KernelExpression {
    const signature = CORE_OWNER_TYPE_SCHEMAS[owner];
    if (
        !Number.isSafeInteger(slotIndex) ||
        slotIndex < 0 ||
        slotIndex >= signature.slots.length
    ) {
        throw new Error(
            `Core owner ${owner} has no typed slot at index ${slotIndex}`
        );
    }
    if (earlierArguments.length !== slotIndex) {
        throw new Error(
            `Core owner ${owner} slot ${slotIndex} requires exactly ` +
            `${slotIndex} earlier arguments, received ` +
            earlierArguments.length
        );
    }
    return instantiateCoreSignatureExpression(
        signature.slots[slotIndex].type,
        argumentBindings(owner, earlierArguments),
        signatureProvenance(
            owner,
            `slot ${signature.slots[slotIndex].name} type`,
            nodeProvenance
        )
    );
}

export function coreOwnerResultType(
    owner: CoreOwnerId,
    arguments_: readonly KernelExpression[],
    nodeProvenance: Provenance
): KernelExpression {
    const signature = CORE_OWNER_TYPE_SCHEMAS[owner];
    if (arguments_.length !== signature.slots.length) {
        throw new Error(
            `Core owner ${owner} result type requires ` +
            `${signature.slots.length} arguments, received ` +
            arguments_.length
        );
    }
    return instantiateCoreSignatureExpression(
        signature.result,
        argumentBindings(owner, arguments_),
        signatureProvenance(owner, 'result type', nodeProvenance)
    );
}

const signatureBinderMode = (
    plicity: Plicity
): BinderMode => binderMode(plicity, 'functorial');

/**
 * Materialize an owner's complete dependent Pi telescope as Core.
 */
export function coreOwnerSignatureType(
    owner: CoreOwnerId,
    nodeProvenance: Provenance
): KernelExpression {
    const signature = CORE_OWNER_TYPE_SCHEMAS[owner];

    const build = (slotIndex: number): KernelExpression => {
        if (slotIndex === signature.slots.length) {
            const bindings = Object.fromEntries(
                signature.slots.map((slot, index) => [
                    slot.name,
                    kernelBound(
                        signature.slots.length - index - 1,
                        nodeProvenance
                    )
                ])
            );
            return instantiateCoreSignatureExpression(
                signature.result,
                bindings,
                signatureProvenance(owner, 'result type', nodeProvenance)
            );
        }

        const slot = signature.slots[slotIndex];
        const previousBindings = Object.fromEntries(
            signature.slots.slice(0, slotIndex).map((previous, index) => [
                previous.name,
                kernelBound(slotIndex - index - 1, nodeProvenance)
            ])
        );
        const type = instantiateCoreSignatureExpression(
            slot.type,
            previousBindings,
            signatureProvenance(
                owner,
                `slot ${slot.name} type`,
                nodeProvenance
            )
        );
        return kernelPi(
            kernelBinder(
                slot.name,
                type,
                signatureBinderMode(slot.plicity),
                nodeProvenance
            ),
            build(slotIndex + 1),
            nodeProvenance
        );
    };

    return build(0);
}

validateCoreOwnerTypeCatalog();
