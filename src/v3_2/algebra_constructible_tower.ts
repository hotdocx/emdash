/** Constructible-set category tower and direct computational reinterpretation. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AlgebraPolynomialRing } from './algebra_polynomial';
import { AlgebraConstructibleSet } from './algebra_constructible';
import { ALGEBRA_BASE_DOCTRINES } from './algebra_doctrine';
import {
    CategoricalTower,
    ComputationalReinterpretation,
    additiveClosureConstructor,
    buildCategoricalTower,
    defineCategoryConstructorDescriptor,
    defineComputationalReinterpretation,
    oppositeConstructorDescriptor
} from './algebra_tower';

export const ALGEBRA_CONSTRUCTIBLE_TOWER_PROFILE = Object.freeze({
    revision: 'emdash-constructible-tower-v1' as const,
    publicRepresentation: 'direct-finite-constructible-union' as const,
    runtimeBoxing: false as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export const constructibleSliceConstructor = () =>
    defineCategoryConstructorDescriptor({
        id: 'category-constructor.slice-over-tensor-unit',
        inputDoctrineId: 'additive-category',
        outputDoctrineId: 'category',
        introducedRoles: ['slice-object'],
        objectLayer: 'arrow-to-tensor-unit',
        morphismLayer: 'slice-commuting-triangle',
        dualConstructorId: 'category-constructor.coslice-under-tensor-unit',
        loweringRules: [{
            id: 'constructible.slice-to-ideal',
            kind: 'operation-lowering',
            source: 'slice-over-tensor-unit',
            target: 'polynomial-ideal-data'
        }]
    });

export const constructiblePosetConstructor = () =>
    defineCategoryConstructorDescriptor({
        id: 'category-constructor.poset-reflection',
        inputDoctrineId: 'category',
        outputDoctrineId: 'category',
        introducedRoles: ['poset-comparison'],
        objectLayer: 'congruence-classes-of-objects',
        morphismLayer: 'mere-computational-inclusion',
        dualConstructorId: 'category-constructor.poset-reflection',
        loweringRules: [{
            id: 'constructible.poset-to-radical-comparison',
            kind: 'operation-lowering',
            source: 'poset-comparison',
            target: 'radical-membership-data'
        }]
    });

export const constructibleStablePosetConstructor = () =>
    defineCategoryConstructorDescriptor({
        id: 'category-constructor.stable-poset',
        inputDoctrineId: 'category',
        outputDoctrineId: 'category',
        introducedRoles: ['stable-comparison'],
        objectLayer: 'stable-poset-object',
        morphismLayer: 'saturation-invariant-inclusion',
        dualConstructorId: 'category-constructor.stable-poset',
        loweringRules: [{
            id: 'constructible.stable-to-saturation',
            kind: 'operation-lowering',
            source: 'stable-comparison',
            target: 'principal-saturation-data'
        }]
    });

export const constructibleDifferencesConstructor = () =>
    defineCategoryConstructorDescriptor({
        id: 'category-constructor.differences',
        inputDoctrineId: 'category',
        outputDoctrineId: 'category',
        introducedRoles: ['difference'],
        objectLayer: 'formal-difference-pair',
        morphismLayer: 'difference-inclusion',
        dualConstructorId: 'category-constructor.differences',
        loweringRules: [{
            id: 'constructible.difference-to-locally-closed',
            kind: 'reinterpretation',
            source: 'formal-difference-pair',
            target: 'saturated-locally-closed-piece'
        }]
    });

export const constructibleUnionsConstructor = () =>
    defineCategoryConstructorDescriptor({
        id: 'category-constructor.finite-unions',
        inputDoctrineId: 'category',
        outputDoctrineId: 'category',
        introducedRoles: ['finite-union'],
        objectLayer: 'finite-list-of-differences',
        morphismLayer: 'constructible-inclusion',
        dualConstructorId: 'category-constructor.finite-unions',
        loweringRules: [{
            id: 'constructible.union-to-piece-list',
            kind: 'reinterpretation',
            source: 'finite-list-of-differences',
            target: 'finite-constructible-piece-list'
        }]
    });

export interface AlgebraConstructibleTowerModel<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly profileRevision: typeof ALGEBRA_CONSTRUCTIBLE_TOWER_PROFILE.revision;
    readonly ring: AlgebraPolynomialRing<P, C, I>;
    readonly tower: CategoricalTower;
    readonly reinterpretation: ComputationalReinterpretation<
        AlgebraConstructibleSet<P, C, I>,
        AlgebraConstructibleSet<P, C, I>
    >;
}

export function algebraConstructibleTowerModel<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(ring: AlgebraPolynomialRing<P, C, I>): AlgebraConstructibleTowerModel<P, C, I> {
    const suffix = ring.identity.id;
    const tower = buildCategoricalTower(
        `algebra.tower.constructible/${suffix}`,
        ALGEBRA_BASE_DOCTRINES,
        'preadditive-category',
        [
            additiveClosureConstructor(),
            constructibleSliceConstructor(),
            constructiblePosetConstructor(),
            constructibleStablePosetConstructor(),
            oppositeConstructorDescriptor(ALGEBRA_BASE_DOCTRINES, 'category'),
            constructibleDifferencesConstructor(),
            constructibleUnionsConstructor()
        ]
    );
    const modelingCategoryId = `algebra.category.constructible-model/${suffix}`;
    const publicCategoryId = `algebra.category.constructible/${suffix}`;
    const reinterpretation = defineComputationalReinterpretation({
        id: `algebra.reinterpretation.constructible/${suffix}`,
        publicCategoryId,
        modelingCategoryId,
        toModel: (value: AlgebraConstructibleSet<P, C, I>) => value,
        fromModel: (value: AlgebraConstructibleSet<P, C, I>) => value,
        loweringRules: [{
            id: `constructible.direct-representation/${suffix}`,
            kind: 'reinterpretation',
            source: modelingCategoryId,
            target: publicCategoryId
        }]
    });
    return Object.freeze({
        profileRevision: ALGEBRA_CONSTRUCTIBLE_TOWER_PROFILE.revision,
        ring,
        tower,
        reinterpretation
    });
}
