/**
 * Schema-directed ELAB-0 elaboration for the ordinary v3.2 application family.
 *
 * This is intentionally not a second evaluator. It recovers rigid implicit
 * arguments from a checked surface context and lowers to explicit owner apps.
 */

import {
    KernelApplication,
    KernelExpression,
    SourceSpan,
    formatSourceSpan,
    kernelApplication,
    kernelExpressionEquals,
    kernelLocal,
    provenance,
    serializeKernelExpression
} from './kernel';
import {
    CoreType,
    SurfaceContext,
    SurfaceTerm
} from './surface';

export type ElaborationErrorCode =
    | 'UNBOUND_NAME'
    | 'EXPECTED_FUNCTOR'
    | 'EXPECTED_OBJECT'
    | 'EXPECTED_HOM'
    | 'EXPECTED_TRANSFOR'
    | 'CATEGORY_MISMATCH';

export class V32ElaborationError extends Error {
    constructor(
        public readonly code: ElaborationErrorCode,
        public readonly span: SourceSpan,
        message: string
    ) {
        super(`${message} at ${formatSourceSpan(span)}`);
        this.name = 'V32ElaborationError';
    }
}

export interface RecoveredSlot {
    owner: 'fapp0' | 'fapp1_fapp0' | 'tapp1_fapp0';
    slot: string;
    value: KernelExpression;
    span: SourceSpan;
}

export interface ElaboratedSurfaceTerm {
    term: KernelExpression;
    type: CoreType;
    sourceSpan: SourceSpan;
    recovered: readonly RecoveredSlot[];
}

const recoveredProvenance = (
    owner: RecoveredSlot['owner'],
    slot: string,
    span: SourceSpan
) => provenance(
    'recovered',
    `${owner} implicit slot ${slot} recovered from operand types`,
    span
);

const derivedProvenance = (detail: string, span: SourceSpan) =>
    provenance('derived', detail, span);

const surfaceProvenance = (detail: string, span: SourceSpan) =>
    provenance('surface', detail, span);

const renderExpression = (expression: KernelExpression): string =>
    serializeKernelExpression(expression);

function categoryMismatch(
    span: SourceSpan,
    owner: string,
    expected: KernelExpression,
    actual: KernelExpression
): never {
    throw new V32ElaborationError(
        'CATEGORY_MISMATCH',
        span,
        `${owner} expected source category ${renderExpression(expected)}, ` +
        `but received ${renderExpression(actual)}`
    );
}

function recoveredSlot(
    owner: RecoveredSlot['owner'],
    slot: string,
    value: KernelExpression,
    span: SourceSpan
): RecoveredSlot {
    return { owner, slot, value, span };
}

function derivedFapp0(
    sourceCategory: KernelExpression,
    targetCategory: KernelExpression,
    functor: KernelExpression,
    object: KernelExpression,
    span: SourceSpan
): KernelApplication {
    const nodeProvenance = derivedProvenance(
        'result endpoint produced by fapp0',
        span
    );
    return kernelApplication('fapp0', [
        {
            value: sourceCategory,
            provenance: recoveredProvenance('fapp0', 'A', span)
        },
        {
            value: targetCategory,
            provenance: recoveredProvenance('fapp0', 'B', span)
        },
        { value: functor, provenance: functor.provenance },
        { value: object, provenance: object.provenance }
    ], nodeProvenance);
}

export function elaborateSurfaceTerm(
    context: SurfaceContext,
    surface: SurfaceTerm
): ElaboratedSurfaceTerm {
    switch (surface.tag) {
        case 'reference': {
            const binding = context.lookup(surface.name);
            if (!binding) {
                throw new V32ElaborationError(
                    'UNBOUND_NAME',
                    surface.span,
                    `Unbound v3.2 surface name '${surface.name}'`
                );
            }
            return {
                term: kernelLocal(
                    binding.name,
                    surfaceProvenance(
                        `surface reference ${binding.name}`,
                        surface.span
                    )
                ),
                type: binding.coreType,
                sourceSpan: surface.span,
                recovered: []
            };
        }
        case 'fapp0': {
            const functor = elaborateSurfaceTerm(context, surface.functor);
            const object = elaborateSurfaceTerm(context, surface.object);

            if (functor.type.tag !== 'functor') {
                throw new V32ElaborationError(
                    'EXPECTED_FUNCTOR',
                    surface.functor.span,
                    'fapp0 expects its first operand to be an ordinary functor'
                );
            }
            if (object.type.tag !== 'object') {
                throw new V32ElaborationError(
                    'EXPECTED_OBJECT',
                    surface.object.span,
                    'fapp0 expects its second operand to be an object'
                );
            }
            if (!kernelExpressionEquals(
                functor.type.sourceCategory,
                object.type.category
            )) {
                categoryMismatch(
                    surface.object.span,
                    'fapp0',
                    functor.type.sourceCategory,
                    object.type.category
                );
            }

            const nodeProvenance = surfaceProvenance(
                'surface fapp0 application',
                surface.span
            );
            const term = kernelApplication('fapp0', [
                {
                    value: functor.type.sourceCategory,
                    provenance: recoveredProvenance(
                        'fapp0',
                        'A',
                        surface.span
                    )
                },
                {
                    value: functor.type.targetCategory,
                    provenance: recoveredProvenance(
                        'fapp0',
                        'B',
                        surface.span
                    )
                },
                { value: functor.term, provenance: functor.term.provenance },
                { value: object.term, provenance: object.term.provenance }
            ], nodeProvenance);

            return {
                term,
                type: {
                    tag: 'object',
                    category: functor.type.targetCategory
                },
                sourceSpan: surface.span,
                recovered: [
                    ...functor.recovered,
                    ...object.recovered,
                    recoveredSlot(
                        'fapp0',
                        'A',
                        functor.type.sourceCategory,
                        surface.span
                    ),
                    recoveredSlot(
                        'fapp0',
                        'B',
                        functor.type.targetCategory,
                        surface.span
                    )
                ]
            };
        }
        case 'fapp1_fapp0': {
            const functor = elaborateSurfaceTerm(context, surface.functor);
            const arrow = elaborateSurfaceTerm(context, surface.arrow);

            if (functor.type.tag !== 'functor') {
                throw new V32ElaborationError(
                    'EXPECTED_FUNCTOR',
                    surface.functor.span,
                    'fapp1_fapp0 expects an ordinary functor'
                );
            }
            if (arrow.type.tag !== 'hom') {
                throw new V32ElaborationError(
                    'EXPECTED_HOM',
                    surface.arrow.span,
                    'fapp1_fapp0 expects an ordinary source arrow'
                );
            }
            if (!kernelExpressionEquals(
                functor.type.sourceCategory,
                arrow.type.category
            )) {
                categoryMismatch(
                    surface.arrow.span,
                    'fapp1_fapp0',
                    functor.type.sourceCategory,
                    arrow.type.category
                );
            }

            const nodeProvenance = surfaceProvenance(
                'surface fapp1_fapp0 application',
                surface.span
            );
            const term = kernelApplication('fapp1_fapp0', [
                {
                    value: functor.type.sourceCategory,
                    provenance: recoveredProvenance(
                        'fapp1_fapp0',
                        'A',
                        surface.span
                    )
                },
                {
                    value: functor.type.targetCategory,
                    provenance: recoveredProvenance(
                        'fapp1_fapp0',
                        'B',
                        surface.span
                    )
                },
                { value: functor.term, provenance: functor.term.provenance },
                {
                    value: arrow.type.sourceObject,
                    provenance: recoveredProvenance(
                        'fapp1_fapp0',
                        'X',
                        surface.span
                    )
                },
                {
                    value: arrow.type.targetObject,
                    provenance: recoveredProvenance(
                        'fapp1_fapp0',
                        'Y',
                        surface.span
                    )
                },
                { value: arrow.term, provenance: arrow.term.provenance }
            ], nodeProvenance);

            const source = derivedFapp0(
                functor.type.sourceCategory,
                functor.type.targetCategory,
                functor.term,
                arrow.type.sourceObject,
                surface.span
            );
            const target = derivedFapp0(
                functor.type.sourceCategory,
                functor.type.targetCategory,
                functor.term,
                arrow.type.targetObject,
                surface.span
            );

            return {
                term,
                type: {
                    tag: 'hom',
                    category: functor.type.targetCategory,
                    sourceObject: source,
                    targetObject: target
                },
                sourceSpan: surface.span,
                recovered: [
                    ...functor.recovered,
                    ...arrow.recovered,
                    recoveredSlot(
                        'fapp1_fapp0',
                        'A',
                        functor.type.sourceCategory,
                        surface.span
                    ),
                    recoveredSlot(
                        'fapp1_fapp0',
                        'B',
                        functor.type.targetCategory,
                        surface.span
                    ),
                    recoveredSlot(
                        'fapp1_fapp0',
                        'X',
                        arrow.type.sourceObject,
                        surface.span
                    ),
                    recoveredSlot(
                        'fapp1_fapp0',
                        'Y',
                        arrow.type.targetObject,
                        surface.span
                    )
                ]
            };
        }
        case 'tapp1_fapp0': {
            const transformation = elaborateSurfaceTerm(
                context,
                surface.transformation
            );
            const arrow = elaborateSurfaceTerm(context, surface.arrow);

            if (transformation.type.tag !== 'transfor') {
                throw new V32ElaborationError(
                    'EXPECTED_TRANSFOR',
                    surface.transformation.span,
                    'tapp1_fapp0 expects an ordinary transfor'
                );
            }
            if (arrow.type.tag !== 'hom') {
                throw new V32ElaborationError(
                    'EXPECTED_HOM',
                    surface.arrow.span,
                    'tapp1_fapp0 expects an ordinary source arrow'
                );
            }
            if (!kernelExpressionEquals(
                transformation.type.sourceCategory,
                arrow.type.category
            )) {
                categoryMismatch(
                    surface.arrow.span,
                    'tapp1_fapp0',
                    transformation.type.sourceCategory,
                    arrow.type.category
                );
            }

            const nodeProvenance = surfaceProvenance(
                'surface tapp1_fapp0 application',
                surface.span
            );
            const term = kernelApplication('tapp1_fapp0', [
                {
                    value: transformation.type.sourceCategory,
                    provenance: recoveredProvenance(
                        'tapp1_fapp0',
                        'A',
                        surface.span
                    )
                },
                {
                    value: transformation.type.targetCategory,
                    provenance: recoveredProvenance(
                        'tapp1_fapp0',
                        'B',
                        surface.span
                    )
                },
                {
                    value: transformation.type.sourceFunctor,
                    provenance: recoveredProvenance(
                        'tapp1_fapp0',
                        'F',
                        surface.span
                    )
                },
                {
                    value: transformation.type.targetFunctor,
                    provenance: recoveredProvenance(
                        'tapp1_fapp0',
                        'G',
                        surface.span
                    )
                },
                {
                    value: arrow.type.sourceObject,
                    provenance: recoveredProvenance(
                        'tapp1_fapp0',
                        'X',
                        surface.span
                    )
                },
                {
                    value: arrow.type.targetObject,
                    provenance: recoveredProvenance(
                        'tapp1_fapp0',
                        'Y',
                        surface.span
                    )
                },
                {
                    value: transformation.term,
                    provenance: transformation.term.provenance
                },
                { value: arrow.term, provenance: arrow.term.provenance }
            ], nodeProvenance);

            const source = derivedFapp0(
                transformation.type.sourceCategory,
                transformation.type.targetCategory,
                transformation.type.sourceFunctor,
                arrow.type.sourceObject,
                surface.span
            );
            const target = derivedFapp0(
                transformation.type.sourceCategory,
                transformation.type.targetCategory,
                transformation.type.targetFunctor,
                arrow.type.targetObject,
                surface.span
            );

            return {
                term,
                type: {
                    tag: 'hom',
                    category: transformation.type.targetCategory,
                    sourceObject: source,
                    targetObject: target
                },
                sourceSpan: surface.span,
                recovered: [
                    ...transformation.recovered,
                    ...arrow.recovered,
                    recoveredSlot(
                        'tapp1_fapp0',
                        'A',
                        transformation.type.sourceCategory,
                        surface.span
                    ),
                    recoveredSlot(
                        'tapp1_fapp0',
                        'B',
                        transformation.type.targetCategory,
                        surface.span
                    ),
                    recoveredSlot(
                        'tapp1_fapp0',
                        'F',
                        transformation.type.sourceFunctor,
                        surface.span
                    ),
                    recoveredSlot(
                        'tapp1_fapp0',
                        'G',
                        transformation.type.targetFunctor,
                        surface.span
                    ),
                    recoveredSlot(
                        'tapp1_fapp0',
                        'X',
                        arrow.type.sourceObject,
                        surface.span
                    ),
                    recoveredSlot(
                        'tapp1_fapp0',
                        'Y',
                        arrow.type.targetObject,
                        surface.span
                    )
                ]
            };
        }
        default: {
            const exhaustive: never = surface;
            return exhaustive;
        }
    }
}
