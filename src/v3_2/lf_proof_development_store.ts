/** Node-owned read-only acquisition of one canonical proof-development file. */

import { createHash } from 'node:crypto';
import { constants } from 'node:fs';
import { lstat, open, realpath } from 'node:fs/promises';
import path from 'node:path';
import {
    CORE_LF_PROOF_DEVELOPMENT_SOURCE_PROFILE,
    CoreLfProofDevelopmentSourceReconstruction,
    parseCoreLfProofDevelopmentSourceText
} from './lf_proof_development_source';

const MIB = 1024 * 1024;
const READ_CHUNK_BYTES = 64 * 1024;

export const CORE_LF_MOUNTED_PROOF_DEVELOPMENT_PROFILE = Object.freeze({
    revision: 'emdash-lf-mounted-proof-development-v3' as const,
    sourceProfileRevision:
        CORE_LF_PROOF_DEVELOPMENT_SOURCE_PROFILE.revision,
    filesystemProfile: 'node-posix-mounted-project-root-v1' as const,
    backend: 'typescript-emdash-explicit-core' as const,
    sourceFileName: 'emdash.proof-development.source.json' as const,
    maximumSourceBytes: 64 * MIB,
    requiresExplicitProjectRoot: true as const,
    performsRootDiscovery: false as const,
    acceptsArbitrarySourcePath: false as const,
    executesHostSource: false as const,
    performsWrites: false as const,
    performsFetch: false as const,
    readsCredentials: false as const,
    readsEnvironment: false as const,
    readsCurrentWorkingDirectory: false as const,
    invokesGit: false as const,
    invokesLambdapi: false as const
});

export type CoreLfMountedProofDevelopmentErrorCode =
    | 'INVALID_ROOT'
    | 'UNSAFE_ROOT'
    | 'SOURCE_MISSING'
    | 'UNSAFE_SOURCE'
    | 'SOURCE_TOO_LARGE'
    | 'INVALID_UTF8'
    | 'INVALID_SOURCE_TEXT'
    | 'IO_FAILURE';

export class CoreLfMountedProofDevelopmentError extends Error {
    public readonly cause: unknown;

    constructor(
        public readonly code: CoreLfMountedProofDevelopmentErrorCode,
        public readonly path: string,
        message: string,
        cause?: unknown
    ) {
        super(`${message} (${path})`);
        this.name = 'CoreLfMountedProofDevelopmentError';
        this.cause = cause;
    }
}

const fail = (
    code: CoreLfMountedProofDevelopmentErrorCode,
    targetPath: string,
    message: string,
    cause?: unknown
): never => {
    throw new CoreLfMountedProofDevelopmentError(
        code,
        targetPath,
        message,
        cause
    );
};

const errnoCode = (error: unknown): string | undefined =>
    typeof error === 'object' &&
    error !== null &&
    'code' in error &&
    typeof (error as { readonly code?: unknown }).code === 'string'
        ? (error as { readonly code: string }).code
        : undefined;

export interface CoreLfMountedProofDevelopmentInput {
    readonly projectRoot: string;
}

export interface CoreLfMountedProofDevelopmentPaths {
    readonly projectRoot: string;
    readonly sourcePath: string;
}

export interface CoreLfMountedProofDevelopmentResult {
    readonly revision:
        typeof CORE_LF_MOUNTED_PROOF_DEVELOPMENT_PROFILE.revision;
    readonly backend:
        typeof CORE_LF_MOUNTED_PROOF_DEVELOPMENT_PROFILE.backend;
    readonly paths: CoreLfMountedProofDevelopmentPaths;
    readonly sourceUtf8Bytes: number;
    readonly sourceSha256: string;
    readonly sourceText: string;
    readonly reconstruction: CoreLfProofDevelopmentSourceReconstruction;
}

const resolveProjectRoot = async (
    input: CoreLfMountedProofDevelopmentInput
): Promise<string> => {
    const prototype = input === null || typeof input !== 'object'
        ? undefined
        : Object.getPrototypeOf(input);
    const keys = input === null || typeof input !== 'object'
        ? []
        : Reflect.ownKeys(input);
    const descriptor = input === null || typeof input !== 'object'
        ? undefined
        : Object.getOwnPropertyDescriptor(input, 'projectRoot');
    if (
        input === null ||
        typeof input !== 'object' ||
        Array.isArray(input) ||
        (prototype !== Object.prototype && prototype !== null) ||
        keys.length !== 1 ||
        keys[0] !== 'projectRoot' ||
        descriptor === undefined ||
        !Object.prototype.hasOwnProperty.call(descriptor, 'value') ||
        descriptor.enumerable !== true ||
        typeof descriptor.value !== 'string' ||
        !path.isAbsolute(descriptor.value) ||
        path.normalize(descriptor.value) !== descriptor.value
    ) {
        return fail(
            'INVALID_ROOT',
            'projectRoot',
            'Proof-development project root must be one canonical absolute path'
        );
    }
    const projectRoot = descriptor.value;
    let stat;
    try {
        stat = await lstat(projectRoot);
    } catch (error: unknown) {
        return fail(
            errnoCode(error) === 'ENOENT' ? 'INVALID_ROOT' : 'IO_FAILURE',
            'projectRoot',
            'Proof-development project root is unavailable',
            error
        );
    }
    if (stat.isSymbolicLink() || !stat.isDirectory()) {
        return fail(
            'UNSAFE_ROOT',
            'projectRoot',
            'Proof-development project root must be a real directory'
        );
    }
    let resolved: string;
    try {
        resolved = await realpath(projectRoot);
    } catch (error: unknown) {
        return fail(
            'IO_FAILURE',
            'projectRoot',
            'Proof-development project root cannot be resolved',
            error
        );
    }
    if (resolved !== projectRoot) {
        return fail(
            'UNSAFE_ROOT',
            'projectRoot',
            'Proof-development root must not traverse symbolic-link parents'
        );
    }
    return resolved;
};

const readSourceBytes = async (sourcePath: string): Promise<Buffer> => {
    let handle;
    try {
        handle = await open(
            sourcePath,
            constants.O_RDONLY |
                constants.O_NOFOLLOW |
                constants.O_NONBLOCK
        );
    } catch (error: unknown) {
        const code = errnoCode(error);
        if (code === 'ENOENT') {
            return fail(
                'SOURCE_MISSING',
                sourcePath,
                'Canonical proof-development source is missing',
                error
            );
        }
        if (code === 'ELOOP') {
            return fail(
                'UNSAFE_SOURCE',
                sourcePath,
                'Proof-development source must not be a symbolic link',
                error
            );
        }
        return fail(
            'IO_FAILURE',
            sourcePath,
            'Proof-development source cannot be opened',
            error
        );
    }
    try {
        const stat = await handle.stat();
        if (!stat.isFile()) {
            return fail(
                'UNSAFE_SOURCE',
                sourcePath,
                'Proof-development source must be a regular file'
            );
        }
        const maximum =
            CORE_LF_MOUNTED_PROOF_DEVELOPMENT_PROFILE.maximumSourceBytes;
        if (stat.size > maximum) {
            return fail(
                'SOURCE_TOO_LARGE',
                sourcePath,
                `Proof-development source exceeds ${maximum} bytes`
            );
        }
        const chunks: Buffer[] = [];
        let byteLength = 0;
        while (true) {
            const remaining = maximum - byteLength;
            const buffer = Buffer.allocUnsafe(Math.min(
                READ_CHUNK_BYTES,
                remaining + 1
            ));
            const { bytesRead } = await handle.read(
                buffer,
                0,
                buffer.byteLength,
                null
            );
            if (bytesRead === 0) break;
            byteLength += bytesRead;
            if (byteLength > maximum) {
                return fail(
                    'SOURCE_TOO_LARGE',
                    sourcePath,
                    `Proof-development source exceeds ${maximum} bytes`
                );
            }
            chunks.push(buffer.subarray(0, bytesRead));
        }
        return Buffer.concat(chunks, byteLength);
    } catch (error: unknown) {
        if (error instanceof CoreLfMountedProofDevelopmentError) throw error;
        return fail(
            'IO_FAILURE',
            sourcePath,
            'Proof-development source cannot be read',
            error
        );
    } finally {
        await handle.close().catch(() => undefined);
    }
};

const decodeUtf8 = (bytes: Buffer, sourcePath: string): string => {
    const text = bytes.toString('utf8');
    if (!Buffer.from(text, 'utf8').equals(bytes)) {
        return fail(
            'INVALID_UTF8',
            sourcePath,
            'Proof-development source is not exact UTF-8'
        );
    }
    return text;
};

const sha256 = (bytes: Buffer): string =>
    `sha256:${createHash('sha256').update(bytes).digest('hex')}`;

/** Read, validate, and reconstruct one fixed canonical source file. */
export async function materializeCoreLfMountedProofDevelopment(
    input: CoreLfMountedProofDevelopmentInput
): Promise<CoreLfMountedProofDevelopmentResult> {
    const projectRoot = await resolveProjectRoot(input);
    const sourcePath = path.join(
        projectRoot,
        CORE_LF_MOUNTED_PROOF_DEVELOPMENT_PROFILE.sourceFileName
    );
    if (path.dirname(sourcePath) !== projectRoot) {
        return fail(
            'UNSAFE_SOURCE',
            sourcePath,
            'Fixed proof-development source escaped its project root'
        );
    }
    const bytes = await readSourceBytes(sourcePath);
    const sourceText = decodeUtf8(bytes, sourcePath);
    let reconstruction: CoreLfProofDevelopmentSourceReconstruction;
    try {
        reconstruction = parseCoreLfProofDevelopmentSourceText(sourceText);
    } catch (error: unknown) {
        return fail(
            'INVALID_SOURCE_TEXT',
            sourcePath,
            'Canonical proof-development source failed reconstruction',
            error
        );
    }
    return Object.freeze({
        revision: CORE_LF_MOUNTED_PROOF_DEVELOPMENT_PROFILE.revision,
        backend: CORE_LF_MOUNTED_PROOF_DEVELOPMENT_PROFILE.backend,
        paths: Object.freeze({ projectRoot, sourcePath }),
        sourceUtf8Bytes: bytes.byteLength,
        sourceSha256: sha256(bytes),
        sourceText,
        reconstruction
    });
}
