/**
 * Bounded dependent-first constructions over explicit emdash Core.
 *
 * These helpers construct semantic owner applications only. In particular,
 * `coreReindexDisplayedFamily` is an internal categorical operation and is
 * distinct from `kernelSubstitute`, which performs meta-level De Bruijn
 * substitution in the Core syntax.
 */

import {
    KernelExpression,
    Provenance,
    kernelApplication
} from './kernel';
import {
    CoreOwnerId
} from './schema';

const owner = (
    ownerId: CoreOwnerId,
    arguments_: readonly KernelExpression[],
    nodeProvenance: Provenance
): KernelExpression => kernelApplication(
    ownerId,
    arguments_.map(value => ({ value })),
    nodeProvenance
);

/**
 * The type of a directed Cat-valued family over `base`.
 *
 * Active `Catd(base)` is the object classifier of `Catd_cat(base)`. Core keeps
 * the latter semantic route, consistently with D-015, rather than adding a
 * second owner for the definitional `Catd` facade.
 */
export const coreDisplayedFamilyType = (
    base: KernelExpression,
    nodeProvenance: Provenance
): KernelExpression => owner('decode', [
    owner('object-classifier', [
        owner('displayed-category-category', [base], nodeProvenance)
    ], nodeProvenance)
], nodeProvenance);

export const coreOrdinaryFunctorType = (
    source: KernelExpression,
    target: KernelExpression,
    nodeProvenance: Provenance
): KernelExpression => owner('decode', [
    owner('functor-classifier', [source, target], nodeProvenance)
], nodeProvenance);

export const coreConstantDisplayedFamily = (
    base: KernelExpression,
    fibre: KernelExpression,
    nodeProvenance: Provenance
): KernelExpression => owner(
    'constant-displayed-family',
    [base, fibre],
    nodeProvenance
);

/**
 * Reindex `familyOverTarget` along `substitution : source → target`.
 */
export const coreReindexDisplayedFamily = (
    source: KernelExpression,
    target: KernelExpression,
    familyOverTarget: KernelExpression,
    substitution: KernelExpression,
    nodeProvenance: Provenance
): KernelExpression => owner(
    'displayed-pullback',
    [source, target, familyOverTarget, substitution],
    nodeProvenance
);

export const coreSectionCategory = (
    base: KernelExpression,
    family: KernelExpression,
    nodeProvenance: Provenance
): KernelExpression => owner(
    'section-category',
    [base, family],
    nodeProvenance
);

export const coreSectionType = (
    base: KernelExpression,
    family: KernelExpression,
    nodeProvenance: Provenance
): KernelExpression => owner('decode', [
    owner('object-classifier', [
        coreSectionCategory(base, family, nodeProvenance)
    ], nodeProvenance)
], nodeProvenance);

export type CoreBridgeAuthorityClass =
    | 'runtime-reduction'
    | 'proof-time-unification'
    | 'explicit-theorem'
    | 'intentional-distinction';

export interface CoreDependentBridgeSchema {
    /**
     * Owner paths are outermost-to-innermost semantic Core owner sequences.
     */
    readonly displayedOwnerPath: readonly CoreOwnerId[];
    readonly ordinaryOwnerPath: readonly CoreOwnerId[] | null;
    readonly authority: CoreBridgeAuthorityClass;
    readonly requiredNonCollapse: string | null;
}

/**
 * Machine-readable part of the ELAB-2B ordinary/displayed bridge matrix.
 *
 * Exact active backend rules and probes remain in the living plan. This
 * catalog records only backend-neutral semantic paths and authority classes;
 * it does not grant the structural checker conversion powers.
 */
export const CORE_DEPENDENT_BRIDGE_SCHEMAS = {
    'displayed-family-classifier': {
        displayedOwnerPath: [
            'decode',
            'object-classifier',
            'displayed-category-category'
        ],
        ordinaryOwnerPath: [
            'decode',
            'functor-classifier',
            'category-of-categories'
        ],
        authority: 'runtime-reduction',
        requiredNonCollapse:
            'The displayed-category category head remains distinct even when ' +
            'its object classifier reduces to the ordinary functor classifier.'
    },
    'constant-family-reindexing': {
        displayedOwnerPath: [
            'displayed-pullback',
            'constant-displayed-family'
        ],
        ordinaryOwnerPath: [
            'constant-displayed-family'
        ],
        authority: 'runtime-reduction',
        requiredNonCollapse: null
    },
    'constant-family-sections': {
        displayedOwnerPath: [
            'decode',
            'object-classifier',
            'section-category',
            'constant-displayed-family'
        ],
        ordinaryOwnerPath: [
            'decode',
            'functor-classifier'
        ],
        authority: 'proof-time-unification',
        requiredNonCollapse:
            'The section-category facade must not runtime-fold to an ordinary ' +
            'functor category.'
    },
    'general-dependent-sections': {
        displayedOwnerPath: [
            'decode',
            'object-classifier',
            'section-category'
        ],
        ordinaryOwnerPath: null,
        authority: 'intentional-distinction',
        requiredNonCollapse:
            'An arbitrary displayed family has no ordinary codomain category ' +
            'and must remain a genuine section type.'
    }
} as const satisfies Record<string, CoreDependentBridgeSchema>;
