/** Stable parent/element identities for focused algebra values. */

export const ALGEBRA_PARENT_PROFILE = Object.freeze({
    revision: 'emdash-algebra-parent-v1' as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraParentErrorCode =
    | 'INVALID_PARENT_IDENTITY'
    | 'INVALID_PARENT'
    | 'FOREIGN_PARENT';

export class AlgebraParentError extends Error {
    constructor(
        public readonly code: AlgebraParentErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraParentError';
    }
}

const fail = (
    code: AlgebraParentErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraParentError(code, path, message);
};

const SAFE_ID = /^[A-Za-z][A-Za-z0-9._/-]*$/u;
const SAFE_REVISION = /^[A-Za-z0-9][A-Za-z0-9._+-]*$/u;
const SAFE_KIND = /^[a-z][a-z0-9-]*$/u;

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

export interface AlgebraParentIdentity {
    readonly kind: 'algebra-parent';
    readonly id: string;
    readonly revision: string;
}

export interface AlgebraParent<Kind extends string = string> {
    readonly profileRevision: typeof ALGEBRA_PARENT_PROFILE.revision;
    readonly kind: Kind;
    readonly identity: AlgebraParentIdentity;
}

export interface AlgebraElement<Parent extends AlgebraParent = AlgebraParent> {
    readonly parent: Parent;
}

export const algebraParentIdentity = (
    id: string,
    revision: string
): AlgebraParentIdentity => {
    if (!SAFE_ID.test(id)) {
        return fail(
            'INVALID_PARENT_IDENTITY',
            'parent.id',
            'Expected one stable algebra parent ID'
        );
    }
    if (!SAFE_REVISION.test(revision)) {
        return fail(
            'INVALID_PARENT_IDENTITY',
            'parent.revision',
            'Expected one stable algebra parent revision'
        );
    }
    return Object.freeze({ kind: 'algebra-parent', id, revision });
};

export const defineAlgebraParent = <Kind extends string>(
    kind: Kind,
    id: string,
    revision: string
): AlgebraParent<Kind> => {
    if (!SAFE_KIND.test(kind)) {
        return fail(
            'INVALID_PARENT',
            'parent.kind',
            'Algebra parent kind must use lower-kebab-case spelling'
        );
    }
    return Object.freeze({
        profileRevision: ALGEBRA_PARENT_PROFILE.revision,
        kind,
        identity: algebraParentIdentity(id, revision)
    });
};

export const validateAlgebraParent = <Kind extends string = string>(
    value: unknown,
    path = 'parent',
    expectedKind?: Kind
): AlgebraParent<Kind> => {
    if (
        !record(value) ||
        value.profileRevision !== ALGEBRA_PARENT_PROFILE.revision ||
        typeof value.kind !== 'string' ||
        !SAFE_KIND.test(value.kind) ||
        !record(value.identity) ||
        value.identity.kind !== 'algebra-parent' ||
        typeof value.identity.id !== 'string' ||
        !SAFE_ID.test(value.identity.id) ||
        typeof value.identity.revision !== 'string' ||
        !SAFE_REVISION.test(value.identity.revision)
    ) {
        return fail(
            'INVALID_PARENT',
            path,
            'Expected one current algebra parent'
        );
    }
    if (expectedKind !== undefined && value.kind !== expectedKind) {
        return fail(
            'FOREIGN_PARENT',
            `${path}.kind`,
            `Expected parent kind '${expectedKind}', received '${value.kind}'`
        );
    }
    return Object.freeze({
        profileRevision: ALGEBRA_PARENT_PROFILE.revision,
        kind: value.kind as Kind,
        identity: algebraParentIdentity(
            value.identity.id,
            value.identity.revision
        )
    });
};

export const sameAlgebraParent = (
    left: AlgebraParent,
    right: AlgebraParent
): boolean => left.kind === right.kind &&
    left.identity.id === right.identity.id &&
    left.identity.revision === right.identity.revision;

export const assertAlgebraParent = <Kind extends string>(
    value: AlgebraParent,
    expected: AlgebraParent<Kind>,
    path = 'element.parent'
): AlgebraParent<Kind> => {
    const normalized = validateAlgebraParent(value, path);
    if (!sameAlgebraParent(normalized, expected)) {
        return fail(
            'FOREIGN_PARENT',
            path,
            `Expected parent '${expected.identity.id}', received ` +
                `'${normalized.identity.id}'`
        );
    }
    return expected;
};
