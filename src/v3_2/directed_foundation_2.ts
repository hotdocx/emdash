/**
 * Reviewed DIRECTED-FOUNDATION-2 runtime integration.
 *
 * The sole rule executes only for the decoded Cat-hom classifier. Raw Hom
 * classifiers and Hom_cat category heads remain irreducible, and neither the
 * default LF nor browser paths import this module.
 */

import {
    CORE_DIRECTED_FOUNDATION_2_PROPOSAL,
    CoreDirectedFoundation2RuleId
} from './directed_foundation_2_proposal';
import {
    CORE_DIRECTED_FOUNDATION_2_REVIEW,
    validateCoreDirectedFoundation2Review
} from './directed_foundation_2_review';
import {
    CoreRuntimeHeadRewriteResult,
    CoreRuntimeMatch
} from './evaluator';
import {
    CoreLfCatalogRuntime
} from './lf_conversion';
import {
    KernelExpression,
    Provenance,
    kernelApplication,
    provenance
} from './kernel';
import {
    CORE_OWNER_SCHEMAS,
    CoreOwnerId
} from './schema';

export interface CoreDirectedFoundation2RuntimeRule {
    readonly order: 0;
    readonly id: CoreDirectedFoundation2RuleId;
}

const frozenRules: readonly CoreDirectedFoundation2RuntimeRule[] =
    Object.freeze(
        CORE_DIRECTED_FOUNDATION_2_PROPOSAL.runtimeRules.map(rule =>
            Object.freeze({
                order: rule.order,
                id: rule.id
            })
        )
    );

const matchOwnerApplication = (
    expression: KernelExpression,
    owner: CoreOwnerId
): readonly KernelExpression[] | undefined => {
    if (
        expression.tag !== 'application' ||
        expression.owner !== owner ||
        expression.arguments.length !==
            CORE_OWNER_SCHEMAS[owner].slots.length
    ) {
        return undefined;
    }
    for (let index = 0; index < expression.arguments.length; index++) {
        if (
            expression.arguments[index].plicity !==
            CORE_OWNER_SCHEMAS[owner].slots[index].plicity
        ) {
            return undefined;
        }
    }
    return expression.arguments.map(argument => argument.value);
};

const emptyOwner = (
    expression: KernelExpression,
    owner: CoreOwnerId
): boolean => matchOwnerApplication(expression, owner)?.length === 0;

const decodedCategoryHom = (
    expression: KernelExpression
): readonly [
    source: KernelExpression,
    target: KernelExpression
] | undefined => {
    const decode = matchOwnerApplication(expression, 'decode');
    if (!decode) return undefined;
    const hom = matchOwnerApplication(decode[0], 'hom-classifier');
    if (
        !hom ||
        !emptyOwner(hom[0], 'category-of-categories')
    ) {
        return undefined;
    }
    return [hom[1], hom[2]];
};

const rewrittenProvenance = (
    ruleId: CoreDirectedFoundation2RuleId,
    redex: KernelExpression
): Provenance => provenance(
    'derived',
    `DIRECTED-FOUNDATION-2 runtime rewrite ${ruleId}`,
    redex.provenance.span
);

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
 * Closed exact runtime program for the one approved decoded Cat-hom rule.
 */
export class CoreDirectedFoundation2RuntimeProgram
implements CoreLfCatalogRuntime {
    readonly revision = 'DIRECTED-FOUNDATION-2-REVIEWED';
    readonly rules = frozenRules;
    readonly ruleIds: readonly CoreDirectedFoundation2RuleId[];

    private constructor() {
        this.ruleIds = Object.freeze(this.rules.map(rule => rule.id));
        Object.freeze(this);
    }

    static create(): CoreDirectedFoundation2RuntimeProgram {
        validateCoreDirectedFoundation2Review(
            CORE_DIRECTED_FOUNDATION_2_REVIEW
        );
        return new CoreDirectedFoundation2RuntimeProgram();
    }

    rewriteHead(
        expression: KernelExpression
    ): CoreRuntimeHeadRewriteResult {
        const endpoints = decodedCategoryHom(expression);
        if (!endpoints) {
            return Object.freeze({
                status: 'irreducible',
                expression
            });
        }

        const ruleId = 'directed.category-hom.decode' as const;
        const nodeProvenance =
            rewrittenProvenance(ruleId, expression);
        const [source, target] = endpoints;
        const match: CoreRuntimeMatch = Object.freeze({
            ruleId,
            bindings: Object.freeze([source, target])
        });
        return Object.freeze({
            status: 'rewritten',
            ruleId,
            ruleIndex: 0,
            before: expression,
            after: owner('decode', [
                owner(
                    'functor-classifier',
                    [source, target],
                    nodeProvenance
                )
            ], nodeProvenance),
            match
        });
    }
}
