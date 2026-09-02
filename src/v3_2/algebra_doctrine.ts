/** Operational categorical doctrines, hierarchy, duality, and qualification. */

import {
    CategoryOperation,
    ComputableCategory,
    planCategoryOperation
} from './algebra_category';

export const ALGEBRA_DOCTRINE_PROFILE = Object.freeze({
    revision: 'emdash-computational-doctrine-v1' as const,
    qualificationRevision: 'emdash-doctrine-qualification-v1' as const,
    authority: 'operational-capability-not-formal-evidence' as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraDoctrineErrorCode =
    | 'INVALID_DOCTRINE'
    | 'DUPLICATE_DOCTRINE'
    | 'UNKNOWN_PARENT'
    | 'HIERARCHY_CYCLE'
    | 'INVALID_DUAL'
    | 'DUPLICATE_ROLE_BINDING';

export class AlgebraDoctrineError extends Error {
    constructor(
        public readonly code: AlgebraDoctrineErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraDoctrineError';
    }
}

const fail = (
    code: AlgebraDoctrineErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraDoctrineError(code, path, message);
};

const SAFE_ID = /^[A-Za-z][A-Za-z0-9._/-]*$/u;
const SAFE_ROLE = /^[a-z][a-z0-9-]*$/u;

export interface DoctrineDuality {
    readonly doctrineId: string;
    readonly roles: Readonly<Record<string, string>>;
}

export interface DoctrineDescriptor {
    readonly profileRevision: typeof ALGEBRA_DOCTRINE_PROFILE.revision;
    readonly id: string;
    readonly parents: readonly string[];
    readonly requiredRoles: readonly string[];
    readonly dual: DoctrineDuality;
}

export const defineDoctrine = (input: {
    readonly id: string;
    readonly parents?: readonly string[];
    readonly requiredRoles?: readonly string[];
    readonly dual?: {
        readonly doctrineId?: string;
        readonly roles?: Readonly<Record<string, string>>;
    };
}): DoctrineDescriptor => {
    if (!SAFE_ID.test(input.id)) {
        return fail('INVALID_DOCTRINE', 'doctrine.id', 'Invalid doctrine ID');
    }
    const parents = [...(input.parents ?? [])];
    const roles = [...(input.requiredRoles ?? [])];
    if (
        parents.some(parent => !SAFE_ID.test(parent)) ||
        roles.some(role => !SAFE_ROLE.test(role)) ||
        new Set(parents).size !== parents.length ||
        new Set(roles).size !== roles.length
    ) {
        return fail(
            'INVALID_DOCTRINE',
            input.id,
            'Doctrine parents and roles must be stable and distinct'
        );
    }
    const dualRoles = { ...(input.dual?.roles ?? {}) };
    for (const [source, target] of Object.entries(dualRoles)) {
        if (!SAFE_ROLE.test(source) || !SAFE_ROLE.test(target)) {
            return fail('INVALID_DUAL', input.id, 'Invalid dual-role mapping');
        }
    }
    return Object.freeze({
        profileRevision: ALGEBRA_DOCTRINE_PROFILE.revision,
        id: input.id,
        parents: Object.freeze(parents),
        requiredRoles: Object.freeze(roles),
        dual: Object.freeze({
            doctrineId: input.dual?.doctrineId ?? input.id,
            roles: Object.freeze(dualRoles)
        })
    });
};

export interface DoctrineRegistry {
    readonly doctrines: readonly DoctrineDescriptor[];
    readonly byId: ReadonlyMap<string, DoctrineDescriptor>;
}

export const createDoctrineRegistry = (
    doctrineInput: readonly DoctrineDescriptor[]
): DoctrineRegistry => {
    const byId = new Map<string, DoctrineDescriptor>();
    doctrineInput.forEach((doctrine, index) => {
        if (byId.has(doctrine.id)) {
            fail('DUPLICATE_DOCTRINE', `doctrines[${index}]`, doctrine.id);
        }
        byId.set(doctrine.id, doctrine);
    });
    const active = new Set<string>();
    const visited = new Set<string>();
    const visit = (id: string): void => {
        if (visited.has(id)) return;
        if (active.has(id)) fail('HIERARCHY_CYCLE', id, 'Doctrine cycle');
        const doctrine = byId.get(id);
        if (!doctrine) fail('UNKNOWN_PARENT', id, 'Unknown doctrine parent');
        active.add(id);
        doctrine.parents.forEach(visit);
        active.delete(id);
        visited.add(id);
    };
    doctrineInput.forEach(doctrine => visit(doctrine.id));
    doctrineInput.forEach(doctrine => {
        const dual = byId.get(doctrine.dual.doctrineId);
        if (!dual || dual.dual.doctrineId !== doctrine.id) {
            fail('INVALID_DUAL', doctrine.id, 'Doctrine dual is not involutive');
        }
        Object.entries(doctrine.dual.roles).forEach(([source, target]) => {
            if (dual.dual.roles[target] !== source) {
                fail('INVALID_DUAL', doctrine.id, 'Role duality is not involutive');
            }
        });
    });
    return Object.freeze({
        doctrines: Object.freeze([...doctrineInput]),
        byId
    });
};

const inheritedRoles = (
    registry: DoctrineRegistry,
    doctrine: DoctrineDescriptor
): readonly string[] => {
    const roles = new Set<string>();
    const visit = (current: DoctrineDescriptor): void => {
        current.parents.forEach(parent => visit(registry.byId.get(parent)!));
        current.requiredRoles.forEach(role => roles.add(role));
    };
    visit(doctrine);
    return Object.freeze([...roles].sort());
};

export interface DoctrineRoleBinding {
    readonly role: string;
    readonly operation: CategoryOperation<unknown, unknown>;
}

export interface DoctrineQualification {
    readonly profileRevision:
        typeof ALGEBRA_DOCTRINE_PROFILE.qualificationRevision;
    readonly categoryId: string;
    readonly doctrineId: string;
    readonly status: 'qualified' | 'missing';
    readonly requiredRoles: readonly string[];
    readonly availableRoles: readonly string[];
    readonly missingRoles: readonly string[];
    readonly bindings: readonly DoctrineRoleBinding[];
}

export const qualifyCategoryDoctrine = (
    category: ComputableCategory<unknown, unknown>,
    registry: DoctrineRegistry,
    doctrineId: string,
    bindingInput: readonly DoctrineRoleBinding[]
): DoctrineQualification => {
    const doctrine = registry.byId.get(doctrineId);
    if (!doctrine) fail('UNKNOWN_PARENT', doctrineId, 'Unknown doctrine');
    const bindings = new Map<string, DoctrineRoleBinding>();
    bindingInput.forEach((binding, index) => {
        if (!SAFE_ROLE.test(binding.role)) {
            fail('INVALID_DOCTRINE', `bindings[${index}]`, 'Invalid role');
        }
        if (bindings.has(binding.role)) {
            fail('DUPLICATE_ROLE_BINDING', binding.role, 'Duplicate role');
        }
        bindings.set(binding.role, Object.freeze({ ...binding }));
    });
    const requiredRoles = inheritedRoles(registry, doctrine);
    const availableRoles = requiredRoles.filter(role => {
        const binding = bindings.get(role);
        if (!binding) return false;
        try {
            planCategoryOperation(category.operations, binding.operation);
            return true;
        } catch {
            return false;
        }
    });
    const missingRoles = requiredRoles.filter(role =>
        !availableRoles.includes(role)
    );
    return Object.freeze({
        profileRevision: ALGEBRA_DOCTRINE_PROFILE.qualificationRevision,
        categoryId: category.identity.id,
        doctrineId,
        status: missingRoles.length === 0 ? 'qualified' : 'missing',
        requiredRoles,
        availableRoles: Object.freeze(availableRoles),
        missingRoles: Object.freeze(missingRoles),
        bindings: Object.freeze([...bindings.values()])
    });
};

export const CATEGORY_DOCTRINE = defineDoctrine({
    id: 'category',
    dual: { doctrineId: 'category' }
});
export const PREADDITIVE_DOCTRINE = defineDoctrine({
    id: 'preadditive-category',
    parents: ['category'],
    requiredRoles: ['zero-morphism', 'add-morphisms', 'negate-morphism'],
    dual: {
        doctrineId: 'preadditive-category',
        roles: {
            'zero-morphism': 'zero-morphism',
            'add-morphisms': 'add-morphisms',
            'negate-morphism': 'negate-morphism'
        }
    }
});
export const ADDITIVE_DOCTRINE = defineDoctrine({
    id: 'additive-category',
    parents: ['preadditive-category'],
    requiredRoles: ['zero-object', 'biproduct'],
    dual: {
        doctrineId: 'additive-category',
        roles: { 'zero-object': 'zero-object', biproduct: 'biproduct' }
    }
});
export const COMPUTATIONAL_WEAK_KERNEL_DOCTRINE = defineDoctrine({
    id: 'additive-category-with-computational-weak-kernels',
    parents: ['additive-category'],
    requiredRoles: [
        'weak-kernel',
        'weak-kernel-object',
        'weak-kernel-morphism',
        'weak-kernel-lift'
    ],
    dual: {
        doctrineId: 'additive-category-with-computational-weak-cokernels',
        roles: {
            'weak-kernel': 'weak-cokernel',
            'weak-kernel-object': 'weak-cokernel-object',
            'weak-kernel-morphism': 'weak-cokernel-morphism',
            'weak-kernel-lift': 'weak-cokernel-colift'
        }
    }
});
export const COMPUTATIONAL_WEAK_COKERNEL_DOCTRINE = defineDoctrine({
    id: 'additive-category-with-computational-weak-cokernels',
    parents: ['additive-category'],
    requiredRoles: [
        'weak-cokernel',
        'weak-cokernel-object',
        'weak-cokernel-morphism',
        'weak-cokernel-colift'
    ],
    dual: {
        doctrineId: 'additive-category-with-computational-weak-kernels',
        roles: {
            'weak-cokernel': 'weak-kernel',
            'weak-cokernel-object': 'weak-kernel-object',
            'weak-cokernel-morphism': 'weak-kernel-morphism',
            'weak-cokernel-colift': 'weak-kernel-lift'
        }
    }
});
export const PREABELIAN_DOCTRINE = defineDoctrine({
    id: 'preabelian-category',
    parents: ['additive-category'],
    requiredRoles: [
        'kernel',
        'kernel-object',
        'kernel-embedding',
        'kernel-lift',
        'cokernel',
        'cokernel-object',
        'cokernel-projection',
        'cokernel-colift'
    ],
    dual: {
        doctrineId: 'preabelian-category',
        roles: {
            kernel: 'cokernel',
            'kernel-object': 'cokernel-object',
            'kernel-embedding': 'cokernel-projection',
            'kernel-lift': 'cokernel-colift',
            cokernel: 'kernel',
            'cokernel-object': 'kernel-object',
            'cokernel-projection': 'kernel-embedding',
            'cokernel-colift': 'kernel-lift'
        }
    }
});
export const ABELIAN_DOCTRINE = defineDoctrine({
    id: 'abelian-category',
    parents: ['preabelian-category'],
    requiredRoles: [
        'monomorphism-witness',
        'epimorphism-witness',
        'lift-along-monomorphism',
        'colift-along-epimorphism',
        'image',
        'image-object',
        'image-embedding',
        'coastriction-to-image',
        'coimage',
        'coimage-object',
        'coimage-projection',
        'astriction-from-coimage',
        'coimage-image-comparison',
        'coimage-image-isomorphism'
    ],
    dual: {
        doctrineId: 'abelian-category',
        roles: {
            'monomorphism-witness': 'epimorphism-witness',
            'epimorphism-witness': 'monomorphism-witness',
            'lift-along-monomorphism': 'colift-along-epimorphism',
            'colift-along-epimorphism': 'lift-along-monomorphism',
            image: 'coimage',
            'image-object': 'coimage-object',
            'image-embedding': 'coimage-projection',
            'coastriction-to-image': 'astriction-from-coimage',
            coimage: 'image',
            'coimage-object': 'image-object',
            'coimage-projection': 'image-embedding',
            'astriction-from-coimage': 'coastriction-to-image',
            'coimage-image-comparison': 'coimage-image-comparison',
            'coimage-image-isomorphism': 'coimage-image-isomorphism'
        }
    }
});

export const ALGEBRA_BASE_DOCTRINES = createDoctrineRegistry([
    CATEGORY_DOCTRINE,
    PREADDITIVE_DOCTRINE,
    ADDITIVE_DOCTRINE,
    COMPUTATIONAL_WEAK_KERNEL_DOCTRINE,
    COMPUTATIONAL_WEAK_COKERNEL_DOCTRINE,
    PREABELIAN_DOCTRINE,
    ABELIAN_DOCTRINE
]);
