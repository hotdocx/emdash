/**
 * Browser-safe public entry point for the reviewed v3.2 Core product path.
 *
 * This intentionally excludes filesystem/process-backed Lambdapi probes,
 * differential harnesses, and migration ledgers. It is a narrow v3.2 API,
 * not a compatibility barrel for the deleted root prototype.
 */

export {
    CoreChecker,
    CoreCheckerError
} from './checker';
export {
    CoreElaborationSession,
    CoreSessionError
} from './session';
export {
    binderMode,
    kernelApplication,
    kernelBinder,
    kernelBound,
    kernelCall,
    kernelFree,
    kernelLambda,
    kernelPi,
    kernelUniverse,
    provenance,
    sourceSpan
} from './kernel';
export {
    serializeKernelExpression
} from './lambdapi';
export {
    CORE_MVP_MANIFEST
} from './manifest';

export type {
    BinderMode,
    KernelExpression,
    Provenance,
    SourceSpan
} from './kernel';
export type {
    CoreMvpManifestInput
} from './manifest';
