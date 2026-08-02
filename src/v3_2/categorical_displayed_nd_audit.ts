/**
 * Executable DISPLAYED-ND-0A coherence and higher-action audit.
 *
 * This is a read-only architecture/authority audit. It distinguishes:
 *
 * - introduction of an already coherent displayed transformation;
 * - recursive reconstruction of a coherent outer transformation from typed
 *   component syntax;
 * - object, base-arrow, and next-hom observations of an existing coherent
 *   transformation; and
 * - arbitrary pointwise data, which does not by itself contain naturality.
 *
 * No Lambdapi/Core owner, runtime/proof rule, frontend node, checker branch,
 * or deployed profile is installed here.
 */

import {
    validateCoreCategoricalDisplayedChain2aClosureReview
} from './categorical_displayed_chain_2a_closure_review';
import {
    CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_TRANSFER_BOUNDARY
} from './categorical_displayed_chain_2a_closure_transfer';
import {
    CORE_CATEGORICAL_FIBRED_TRANSFD_CONTRACT,
    validateCoreCategoricalFibredTransfdContract
} from './categorical_fibred_transfd_contract';
import {
    CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_BOUNDARY,
    compileCoreCategoricalFibredTransfdTransfer
} from './categorical_fibred_transfd_transfer';
import {
    CoreCategoricalProgram
} from './categorical_program';

const deepFreeze = <T>(value: T): T => {
    if (
        value !== null &&
        typeof value === 'object' &&
        !Object.isFrozen(value)
    ) {
        Reflect.ownKeys(value as object).forEach(key =>
            deepFreeze((value as Record<PropertyKey, unknown>)[key])
        );
        Object.freeze(value);
    }
    return value;
};

const rawAudit = {
    revision: 'DISPLAYED-ND-0A-AUDIT-1',
    row: 'DISPLAYED-ND-0A',
    status:
        'completed-read-only-audit-with-non-self-authorizing-' +
        'continuation-proposal',
    prerequisite: {
        displayedChain2aCheckpoint:
            '89afe5f64710b99a262ff92cb193e2742a11827f',
        displayedChain2aReviewRevision:
            'DISPLAYED-CHAIN-2A-CLOSURE-0A-REVIEWED-1',
        fibredTransfdContractRevision:
            'FIBRED-TRANSFD-1-DIRECT-NEXT-HOM-CONTRACT-1',
        completedMixedTelescopeRequired: true,
        semanticImplementationAuthorized: false
    },
    retainedArchitecture: {
        sourceBoundary: 'existing-typed-typescript-construction-ir',
        abstraction:
            'syntax-directed-recursion-over-typed-component-subexpressions',
        result:
            'genuine-explicit-core-object-of-Transfd_cat',
        checker: 'existing-generic-core-lf-checker',
        coherenceCriterion:
            'every-successful-lowering-constructs-a-well-typed-outer-' +
            'Transfd-term-through-active-categorical-owners',
        sharedOrdinaryDependentAlgorithmRequired: false,
        rawExprLayerAdded: false,
        secondBidirectionalCheckerAdded: false,
        parserAdded: false,
        wholeBodyRecognizerAdded: false
    },
    binderMeaning: {
        notation: 'lambda k :^nd K. component-body',
        resultClassifier: 'Transfd_cat(E,D,FF,GG)',
        boundSlot: 'object-of-K',
        bodyClassifier: 'indexed-transfor-between-FF[k]-and-GG[k]',
        importantDistinction:
            'a-component-family-is-not-a-displayed-transformation-' +
            'unless-its-base-arrow-coherence-is-constructed',
        constructionPolicy:
            'factor-recursively-only-through-an-existing-coherent-outer-' +
            'constructor-and-fail-closed-otherwise'
    },
    observationMatrix: [
        {
            id: 'object-component',
            surface: 'eta[k]',
            owner: 'tdapp0_fapp0',
            activeKernel: true,
            transferredToTypescript: true,
            surfaceApi: 'displayedTransforComponent',
            status: 'implemented'
        },
        {
            id: 'point-component',
            surface: 'eta[k][u]',
            owner: 'tapp0_fapp0-after-tdapp0_fapp0',
            activeKernel: true,
            transferredToTypescript: true,
            surfaceApi: 'displayedTransforPoint',
            status: 'implemented'
        },
        {
            id: 'base-arrow-cell',
            surface: 'eta[p][u]',
            owner: 'tdapp1_int_cell',
            activeKernel: true,
            transferredToTypescript: true,
            surfaceApi: 'displayedTransforNaturality',
            status: 'implemented'
        },
        {
            id: 'internal-hom-object-action',
            surface: 'tdapp1_int_func_transfd(FF,GG)[eta]',
            owner: 'tdapp1_int_fapp0_transfd',
            activeKernel: true,
            transferredToTypescript: false,
            surfaceApi: 'absent',
            status: 'existing-authority-transfer-gap'
        },
        {
            id: 'next-hom-action',
            surface:
                'tdapp1_int_func_transfd(FF,GG)[m : eta -> theta]',
            owner: 'tdapp1_int_fapp1_func_transfd',
            activeKernel: true,
            transferredToTypescript: false,
            surfaceApi: 'absent',
            status: 'existing-authority-transfer-and-surface-gap'
        }
    ],
    introductionMatrix: [
        {
            id: 'closed-coherent-eta',
            surface: 'lambda k :^nd K. eta[k]',
            outerLowering: 'eta',
            status: 'implemented',
            newKernelSemanticsRequired: false
        },
        {
            id: 'closed-coherent-composite-eta',
            surface: 'lambda k :^nd K. (theta-after-eta)[k]',
            outerLowering:
                'comp_fapp0-at-Functord_cat-before-component-projection',
            status: 'implemented-through-existing-eta-route',
            newKernelSemanticsRequired: false
        },
        {
            id: 'pointwise-vertical-composition',
            surface: 'lambda k :^nd K. theta[k] after eta[k]',
            outerLowering: 'comp_fapp0-at-Functord_cat',
            componentComputation:
                'active-and-transferred-tdapp0-composition-beta',
            baseArrowObservation:
                'well-typed-tdapp1_int_cell-of-the-outer-composite',
            status: 'feasible-recursive-frontend-case',
            exactFrontendGap:
                'generic-typed-categorical-cell-composition-node-and-' +
                'recursive-Transfd-factoring',
            newKernelSemanticsRequired: false
        },
        {
            id: 'pointwise-identity',
            surface: 'lambda k :^nd K. id(FF[k])',
            outerLowering: 'id-at-Functord_cat',
            componentComputation:
                'active-tdapp0-identity-beta',
            baseArrowObservation:
                'tdapp1_int_cell-of-identity-folds-to-fdapp1_int_cell',
            status: 'feasible-later-recursive-frontend-case',
            exactFrontendGap:
                'generic-typed-categorical-cell-identity-node',
            newKernelSemanticsRequired: false
        },
        {
            id: 'arbitrary-pointwise-component-family',
            surface: 'lambda k :^nd K. arbitrary-component(k)',
            outerLowering: 'none',
            status: 'correctly-withheld',
            exactGap:
                'coherence-data-or-a-coherence-carrying-outer-constructor',
            newKernelSemanticsRequired: 'unknown-until-a-concrete-consumer'
        },
        {
            id: 'mixed-variance-transf-catd-section',
            surface: 'section-of-Pi_cat(Transf_catd(A,B,FF,GG))',
            outerLowering: 'not-convertible-by-default-to-Transfd',
            status: 'alternative-pointwise-data-presentation-only',
            exactGap:
                'a-reviewed-coherence-bridge-if-a-concrete-consumer-needs-it',
            newKernelSemanticsRequired: 'not-selected'
        }
    ],
    higherActionAuthority: {
        owners: [
            'tdapp1_int_func_transfd',
            'tdapp1_int_fapp0_transfd',
            'tdapp1_int_fapp1_func_transfd',
            'fdapp1_int_transfd',
            'tdapp1_int_cell'
        ],
        activeChecks: [
            'object-projection-to-tdapp1_int_fapp0_transfd',
            'hom-projection-to-tdapp1_int_fapp1_func_transfd',
            'identity-specialization-to-fdapp1_int_transfd',
            'canonical-cell-projection-to-tdapp1_int_cell'
        ],
        conclusion:
            'next-hom-semantics-exist-in-the-active-kernel-but-the-' +
            'corresponding-generic-transfer-and-surface-observation-are-' +
            'not-yet-in-the-TypeScript-profile'
    },
    computationBoundary: {
        identityComponentBetaActive: true,
        verticalCompositeComponentBetaActive: true,
        identityBaseArrowCellFoldActive: true,
        verticalCompositeBaseArrowCellBetaActive: false,
        verticalCompositeBaseArrowCellStillWellTyped: true,
        interpretation:
            'lack-of-a-componentwise-composite-cell-normal-form-does-not-' +
            'block-coherent-construction-but-remains-a-separate-' +
            'normalization-question-for-a-demanding-consumer'
    },
    alternatives: [
        {
            id: 'extend-the-eta-whole-body-recognizer-by-ad-hoc-cases',
            disposition: 'reject',
            reason:
                'does-not-provide-recursive-composition-of-subexpressions'
        },
        {
            id: 'treat-any-pointwise-family-as-coherent',
            disposition: 'reject',
            reason:
                'forgets-the-base-arrow-and-higher-action-obligations'
        },
        {
            id: 'force-Pi-Transf-catd-to-equal-Transfd',
            disposition: 'defer',
            reason:
                'mixed-variance-pointwise-data-does-not-by-itself-prove-' +
                'the-required-coherence-bridge'
        },
        {
            id: 'new-primitive-nd-lambda-owner',
            disposition: 'reject-for-current-evidence',
            reason:
                'identity-and-vertical-composition-already-have-canonical-' +
                'outer-category-owners'
        },
        {
            id: 'generic-typed-cell-ir-plus-recursive-outer-factoring',
            disposition: 'recommend',
            reason:
                'reuses-the-existing-contextual-compiler-pattern-and-' +
                'produces-checked-coherence-carrying-Core'
        }
    ],
    recommendedContinuation: {
        row: 'DISPLAYED-ND-1A',
        gate: 'H-DTTLF-USABILITY-DISPLAYED-ND-01',
        decision: 'D-DTTLF-USABILITY-018',
        kind: 'non-self-authorizing-bounded-implementation-proposal',
        exactFirstCase:
            'lambda-k-nd-pointwise-vertical-composition',
        surfaceMethod: 'composeCells',
        selectedIr: {
            tag: 'typed-cell-composition',
            role: 'generic-typed-categorical-cell-composition-node',
            firstAcceptedClassifier: 'indexed-transfor',
            typeContract:
                'same-context-index-family-and-category-with-adjacent-' +
                'transformation-endpoints',
            recursion:
                'each-child-factors-independently-to-an-outer-Transfd-term'
        },
        selectedLowering:
            'recursive-factorization-to-comp_fapp0-at-Functord_cat',
        requiredEvidence: [
            'callback-once-and-deeply-frozen-recursive-body',
            'component-beta',
            'base-arrow-cell-typechecks',
            'wrong-index-family-endpoint-and-escape-negatives',
            'unchanged-direct-eta-and-displayed-chain-profiles',
            'bounded-lambdapi-conformance'
        ],
        activeLambdapiOwnerDelta: 0,
        activeLambdapiRuleDelta: 0,
        typescriptTransferEntryDelta: 0,
        intrinsicCoreOwnerDelta: 0,
        ownerSpecificCheckerBranchDelta: 0,
        nextHomTransferIncluded: false,
        nextHomFollowup:
            'DISPLAYED-ND-HIGHER-1B-existing-authority-transfer-audit'
    },
    semanticDelta: {
        activeLambdapiOwners: 0,
        activeLambdapiRuntimeRules: 0,
        activeLambdapiProofRules: 0,
        transferredDeclarations: 0,
        transferredRuntimeRules: 0,
        transferredProofRules: 0,
        frontendNodes: 0,
        checkerBranches: 0,
        evaluatorBranches: 0,
        parserLayers: 0,
        browserPromotions: 0
    },
    nonEffects: [
        'does-not-authorize-DISPLAYED-ND-1A',
        'does-not-claim-arbitrary-pointwise-coherence-synthesis',
        'does-not-collapse-Transfd-to-Pi-of-Transf-catd',
        'does-not-transfer-the-next-hom-package',
        'does-not-add-a-composite-base-arrow-cell-beta',
        'does-not-add-an-LF-or-Core-binder-mode',
        'does-not-add-a-parser-or-second-checker',
        'does-not-promote-browser-or-deployed-profiles',
        'does-not-resume-whole-library-scale-transfer',
        'does-not-broaden-Git-authority'
    ],
    decisionQuestion:
        'Approve H-DTTLF-USABILITY-DISPLAYED-ND-01/' +
        'D-DTTLF-USABILITY-018 as proposed: accept the DISPLAYED-ND-0A ' +
        'audit; preserve :^nd as recursive factoring through genuine ' +
        'coherence-carrying outer Transfd constructors; authorize exactly ' +
        'DISPLAYED-ND-1A with one generic typed-cell-composition IR node, ' +
        'the composeCells TypeScript method, and recursive pointwise ' +
        'vertical-composition lowering to comp_fapp0 at Functord_cat; ' +
        'require object ' +
        'component and base-arrow evidence; and retain arbitrary pointwise ' +
        'coherence, identity syntax, next-hom transfer, mixed variance, new ' +
        'kernel semantics, parsing, deployment, scale transfer, and broader ' +
        'Git authority for later exact decisions?'
} as const;

export type CoreCategoricalDisplayedNdAuditInput =
    typeof rawAudit;

export type CoreCategoricalDisplayedNdAuditErrorCode =
    | 'DISPLAYED_ND_AUDIT_PREREQUISITE_DRIFT'
    | 'DISPLAYED_ND_AUDIT_AUTHORITY_DRIFT'
    | 'DISPLAYED_ND_AUDIT_BOUNDARY_DRIFT';

export class CoreCategoricalDisplayedNdAuditError extends Error {
    constructor(
        public readonly code:
            CoreCategoricalDisplayedNdAuditErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreCategoricalDisplayedNdAuditError';
    }
}

export const CORE_CATEGORICAL_DISPLAYED_ND_AUDIT =
    deepFreeze(rawAudit);

export function measureCoreCategoricalDisplayedNdCurrentEnvelope():
Readonly<{
    etaStatus: 'equal';
    compositeEtaStatus: 'equal';
    componentType: 'transfor';
    pointType: 'hom';
    baseArrowType: 'hom';
    directOrdinaryRuntime: 'not-equal';
    directOrdinaryProofTime: 'solved';
    directOrdinaryObjectRuntime: 'equal';
    directSigmaPiRuntime: 'equal';
}> {
    const emdash = new CoreCategoricalProgram({
        sourceFile: '<displayed-nd-0a-audit>',
        profile: 'fibred-transfd-1'
    });
    const K = emdash.category('nd_audit_K');
    const E = emdash.displayedFamily('nd_audit_E', K);
    const D = emdash.displayedFamily('nd_audit_D', K);
    const FF = emdash.displayedFunctor('nd_audit_FF', E, D);
    const GG = emdash.displayedFunctor('nd_audit_GG', E, D);
    const HH = emdash.displayedFunctor('nd_audit_HH', E, D);
    const eta = emdash.displayedTransfor('nd_audit_eta', FF, GG);
    const theta = emdash.displayedTransfor('nd_audit_theta', GG, HH);
    const composite = emdash.composeDisplayedTransfor(theta, eta);
    const etaAbstraction = emdash.displayedTransforLambda(
        'k',
        FF,
        GG,
        k => emdash.apply(eta, k, {
            expectedShape: 'displayed-component'
        })
    );
    const compositeAbstraction = emdash.displayedTransforLambda(
        'k',
        FF,
        HH,
        k => emdash.apply(composite, k, {
            expectedShape: 'displayed-component'
        })
    );
    const x = emdash.object('nd_audit_x', K);
    const y = emdash.object('nd_audit_y', K);
    const p = emdash.hom('nd_audit_p', K, x, y);
    const u = emdash.object('nd_audit_u', emdash.fibre(E, x));
    const component = emdash.displayedTransforComponent(
        compositeAbstraction,
        x
    );
    const point = emdash.displayedTransforPoint(
        compositeAbstraction,
        x,
        u
    );
    const baseArrow = emdash.displayedTransforNaturality(
        compositeAbstraction,
        p,
        u
    );
    const compatibility =
        emdash.displayedTransforClassifierCompatibility(FF, GG);
    const etaStatus = emdash.compare(etaAbstraction, eta).status;
    const compositeEtaStatus =
        emdash.compare(compositeAbstraction, composite).status;
    if (
        etaStatus !== 'equal' ||
        compositeEtaStatus !== 'equal' ||
        emdash.compile(component).surfaceType.tag !== 'transfor' ||
        emdash.compile(point).surfaceType.tag !== 'hom' ||
        emdash.compile(baseArrow).surfaceType.tag !== 'hom' ||
        compatibility.directOrdinaryRuntime.status !== 'not-equal' ||
        compatibility.directOrdinaryProofTime.status !== 'solved' ||
        compatibility.directOrdinaryObjectRuntime.status !== 'equal' ||
        compatibility.directSigmaPiRuntime.status !== 'equal'
    ) {
        throw new CoreCategoricalDisplayedNdAuditError(
            'DISPLAYED_ND_AUDIT_AUTHORITY_DRIFT',
            'The existing :^nd object/base-arrow/classifier envelope drifted'
        );
    }
    return deepFreeze({
        etaStatus,
        compositeEtaStatus,
        componentType: 'transfor',
        pointType: 'hom',
        baseArrowType: 'hom',
        directOrdinaryRuntime: 'not-equal',
        directOrdinaryProofTime: 'solved',
        directOrdinaryObjectRuntime: 'equal',
        directSigmaPiRuntime: 'equal'
    });
}

export function validateCoreCategoricalDisplayedNdAudit(
    audit: CoreCategoricalDisplayedNdAuditInput =
        CORE_CATEGORICAL_DISPLAYED_ND_AUDIT
): void {
    try {
        validateCoreCategoricalDisplayedChain2aClosureReview();
        validateCoreCategoricalFibredTransfdContract();
    } catch (error: unknown) {
        throw new CoreCategoricalDisplayedNdAuditError(
            'DISPLAYED_ND_AUDIT_PREREQUISITE_DRIFT',
            'A reviewed displayed-chain or Transfd prerequisite drifted: ' +
                (error instanceof Error ? error.message : String(error))
        );
    }
    const transfer = compileCoreCategoricalFibredTransfdTransfer();
    if (
        CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_TRANSFER_BOUNDARY
            .status !==
                'displayed-chain-2a-closure-generic-transfer' ||
        CORE_CATEGORICAL_FIBRED_TRANSFD_CONTRACT.revision !==
            audit.prerequisite.fibredTransfdContractRevision ||
        transfer.compiled.declarations.length !== 7 ||
        CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_BOUNDARY
            .declarationNames.join(',') !==
                'Transfd_cat,Transfd,tdapp0_fapp0,' +
                'id,' +
                'functord_transport_lhs_func,' +
                'functord_transport_rhs_func,tdapp1_int_cell'
    ) {
        throw new CoreCategoricalDisplayedNdAuditError(
            'DISPLAYED_ND_AUDIT_PREREQUISITE_DRIFT',
            'The completed chain or existing Transfd transfer boundary drifted'
        );
    }
    if (
        audit.revision !== 'DISPLAYED-ND-0A-AUDIT-1' ||
        audit.row !== 'DISPLAYED-ND-0A' ||
        audit.observationMatrix.map(entry => entry.id).join(',') !==
            'object-component,point-component,base-arrow-cell,' +
            'internal-hom-object-action,next-hom-action' ||
        audit.introductionMatrix.map(entry => entry.id).join(',') !==
            'closed-coherent-eta,closed-coherent-composite-eta,' +
            'pointwise-vertical-composition,pointwise-identity,' +
            'arbitrary-pointwise-component-family,' +
            'mixed-variance-transf-catd-section' ||
        audit.recommendedContinuation.row !== 'DISPLAYED-ND-1A' ||
        audit.recommendedContinuation.selectedIr.tag !==
            'typed-cell-composition' ||
        audit.recommendedContinuation.surfaceMethod !== 'composeCells' ||
        audit.recommendedContinuation.activeLambdapiOwnerDelta !== 0 ||
        audit.recommendedContinuation.activeLambdapiRuleDelta !== 0 ||
        audit.recommendedContinuation.typescriptTransferEntryDelta !== 0
    ) {
        throw new CoreCategoricalDisplayedNdAuditError(
            'DISPLAYED_ND_AUDIT_BOUNDARY_DRIFT',
            'The frozen DISPLAYED-ND-0A case or continuation boundary drifted'
        );
    }
    if (
        Object.values(audit.semanticDelta).some(value => value !== 0) ||
        audit.alternatives.find(entry =>
            entry.id ===
                'generic-typed-cell-ir-plus-recursive-outer-factoring'
        )?.disposition !== 'recommend'
    ) {
        throw new CoreCategoricalDisplayedNdAuditError(
            'DISPLAYED_ND_AUDIT_AUTHORITY_DRIFT',
            'The read-only semantic or architecture conclusion drifted'
        );
    }
}
