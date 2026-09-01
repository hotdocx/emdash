/** Direct category, tower, and graph lowering for polynomial free complexes. */

import {
    AlgebraElement,
    AlgebraParent,
    sameAlgebraParent
} from './algebra_parent';
import {
    AlgebraEngine,
    defineAlgebraRuntimeSchema
} from './algebra_engine';
import {
    CategoryOperation,
    ComputableCategory,
    createCategoryOperationRegistry,
    defineCategoryMethod,
    defineCategoryOperation,
    defineComputableCategory
} from './algebra_category';
import {
    CategoricalCompilation,
    CategoricalProgram,
    CategoryOperationLowering,
    compileCategoricalProgram
} from './algebra_categorical_program';
import {
    ALGEBRA_BASE_DOCTRINES
} from './algebra_doctrine';
import {
    CategoricalTower,
    ComputationalReinterpretation,
    buildCategoricalTower,
    defineCategoryConstructorDescriptor,
    defineComputationalReinterpretation
} from './algebra_tower';
import {
    AlgebraPolynomialBoundedChainMap,
    AlgebraPolynomialBoundedFreeComplex,
    algebraPolynomialBoundedChainMap,
    algebraPolynomialBoundedChainMapCompose,
    algebraPolynomialBoundedChainMapEquals,
    algebraPolynomialBoundedChainMapIdentity,
    algebraPolynomialBoundedFreeComplexEquals
} from './algebra_polynomial_bounded_complex';
import {
    AlgebraPolynomialBoundedChainMapInput,
    AlgebraPolynomialBoundedComplexReferenceOperations,
    algebraPolynomialBoundedComplexReferenceOperations
} from './algebra_polynomial_bounded_complex_reference_operations';
import {
    AlgebraPolynomialRing
} from './algebra_polynomial';
import {
    createAlgebraTypeScriptReferenceEngine
} from './algebra_reference_engine';

export const ALGEBRA_POLYNOMIAL_BOUNDED_COMPLEX_CATEGORY_PROFILE =
    Object.freeze({
        revision: 'emdash-polynomial-bounded-complex-category-v1' as const,
        doctrine: 'category' as const,
        representation: 'direct-polynomial-complex-and-chain-map' as const,
        formalCategoryClaim: false as const,
        performsIo: false as const
    });

export interface AlgebraPolynomialBoundedComplexCategoryModel<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly category: ComputableCategory<
        AlgebraPolynomialBoundedFreeComplex<P, C, I>,
        AlgebraPolynomialBoundedChainMap<P, C, I>
    >;
    readonly chainMapOperation: CategoryOperation<
        AlgebraPolynomialBoundedChainMapInput<P, C, I>,
        AlgebraPolynomialBoundedChainMap<P, C, I>
    >;
    readonly native: AlgebraPolynomialBoundedComplexReferenceOperations<P, C, I>;
    readonly tower: CategoricalTower;
    readonly reinterpretation: ComputationalReinterpretation<
        AlgebraPolynomialBoundedFreeComplex<P, C, I>,
        AlgebraPolynomialBoundedFreeComplex<P, C, I>
    >;
    readonly lowerings: readonly CategoryOperationLowering[];
}

export function algebraPolynomialBoundedComplexCategoryModel<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(ring: AlgebraPolynomialRing<P, C, I>):
    AlgebraPolynomialBoundedComplexCategoryModel<P, C, I> {
    const native = algebraPolynomialBoundedComplexReferenceOperations<P, C, I>();
    const objectSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialBoundedFreeComplex<P, C, I>
    >({
        id: `algebra.category.polynomial-bounded-complex-object/${ring.identity.id}`,
        revision: ALGEBRA_POLYNOMIAL_BOUNDED_COMPLEX_CATEGORY_PROFILE.revision,
        normalize(value: unknown, path: string) {
            if (
                typeof value !== 'object' ||
                value === null ||
                (value as { kind?: unknown }).kind !==
                    'algebra-polynomial-bounded-free-complex'
            ) throw new Error(`bounded polynomial complex expected at ${path}`);
            const complex = value as AlgebraPolynomialBoundedFreeComplex<P, C, I>;
            if (!sameAlgebraParent(complex.ring, ring)) {
                throw new Error(`foreign complex ring at ${path}`);
            }
            return complex;
        }
    });
    const morphismSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialBoundedChainMap<P, C, I>
    >({
        id: `algebra.category.polynomial-bounded-chain-map/${ring.identity.id}`,
        revision: ALGEBRA_POLYNOMIAL_BOUNDED_COMPLEX_CATEGORY_PROFILE.revision,
        normalize(value: unknown, path: string) {
            if (
                typeof value !== 'object' ||
                value === null ||
                (value as { kind?: unknown }).kind !==
                    'algebra-polynomial-bounded-chain-map'
            ) throw new Error(`bounded polynomial chain map expected at ${path}`);
            const map = value as AlgebraPolynomialBoundedChainMap<P, C, I>;
            if (
                !sameAlgebraParent(map.source.ring, ring) ||
                !sameAlgebraParent(map.target.ring, ring)
            ) throw new Error(`foreign chain-map ring at ${path}`);
            return map;
        }
    });
    const chainMapOperation = defineCategoryOperation({
        id: `algebra.category.polynomial-bounded-complex.chain-map/` +
            ring.identity.id,
        revision: ALGEBRA_POLYNOMIAL_BOUNDED_COMPLEX_CATEGORY_PROFILE.revision,
        input: native.chainMapInputSchema,
        output: native.chainMap.output
    });
    const category = defineComputableCategory({
        id: `algebra.category.polynomial-bounded-complex/${ring.identity.id}`,
        revision: ALGEBRA_POLYNOMIAL_BOUNDED_COMPLEX_CATEGORY_PROFILE.revision,
        objectSchema,
        morphismSchema,
        operations: createCategoryOperationRegistry([
            defineCategoryMethod({
                id: 'algebra.polynomial-bounded-complex.chain-map.primitive',
                operation: chainMapOperation,
                kind: 'primitive',
                execute: algebraPolynomialBoundedChainMap
            })
        ]),
        source: map => map.source,
        target: map => map.target,
        identityMorphism: algebraPolynomialBoundedChainMapIdentity,
        compose: algebraPolynomialBoundedChainMapCompose,
        equalObjects: algebraPolynomialBoundedFreeComplexEquals,
        equalMorphisms: algebraPolynomialBoundedChainMapEquals
    });
    const constructor = defineCategoryConstructorDescriptor({
        id: 'category-constructor.polynomial-bounded-free-complexes',
        inputDoctrineId: 'category',
        outputDoctrineId: 'category',
        introducedRoles: ['bounded-free-complex'],
        objectLayer: 'zero-based-polynomial-free-complex',
        morphismLayer: 'componentwise-polynomial-chain-map',
        dualConstructorId: 'category-constructor.polynomial-bounded-free-complexes',
        loweringRules: [{
            id: 'polynomial-complex.chain-map-to-component-squares',
            kind: 'operation-lowering',
            source: 'componentwise-polynomial-chain-map',
            target: native.chainMap.identity.id
        }]
    });
    const tower = buildCategoricalTower(
        `algebra.tower.polynomial-bounded-complex/${ring.identity.id}`,
        ALGEBRA_BASE_DOCTRINES,
        'category',
        [constructor]
    );
    const modelCategoryId =
        `algebra.category.polynomial-bounded-complex-model/${ring.identity.id}`;
    const reinterpretation = defineComputationalReinterpretation({
        id: `algebra.reinterpretation.polynomial-bounded-complex/${ring.identity.id}`,
        publicCategoryId: category.identity.id,
        modelingCategoryId: modelCategoryId,
        toModel: (value: AlgebraPolynomialBoundedFreeComplex<P, C, I>) => value,
        fromModel: (value: AlgebraPolynomialBoundedFreeComplex<P, C, I>) => value,
        loweringRules: [{
            id: 'polynomial-complex.direct-representation',
            kind: 'reinterpretation',
            source: modelCategoryId,
            target: category.identity.id
        }]
    });
    return Object.freeze({
        category,
        chainMapOperation,
        native,
        tower,
        reinterpretation,
        lowerings: Object.freeze([{
            categoryOperation: chainMapOperation,
            algebraOperation: native.chainMap
        }] as CategoryOperationLowering[])
    });
}

export const compileAlgebraPolynomialBoundedComplexProgram = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    model: AlgebraPolynomialBoundedComplexCategoryModel<P, C, I>,
    program: CategoricalProgram
): CategoricalCompilation => compileCategoricalProgram({
    program,
    category: model.category as unknown as ComputableCategory<unknown, unknown>,
    tower: model.tower,
    lowerings: model.lowerings,
    reinterpretations: [model.reinterpretation]
});

export const createAlgebraPolynomialBoundedComplexEngine = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(model: AlgebraPolynomialBoundedComplexCategoryModel<P, C, I>): AlgebraEngine =>
    createAlgebraTypeScriptReferenceEngine({
        id: `algebra.typescript-reference.polynomial-bounded-complex/` +
            model.category.identity.id,
        revision: ALGEBRA_POLYNOMIAL_BOUNDED_COMPLEX_CATEGORY_PROFILE.revision,
        implementations: model.native.implementations
    });
