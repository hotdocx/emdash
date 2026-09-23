/** Checked closed signatures shared by repository-owned formal adapters. */
import type { CoreLfDeclarationEnvironment } from './lf_declarations';
import type { AffineFormalZariskiInputDeclaration } from './algebra_formal_zariski_signatures';

type SignatureFactory = (
    inputs: readonly AffineFormalZariskiInputDeclaration[]
) => CoreLfDeclarationEnvironment;

const references = new WeakMap<SignatureFactory, CoreLfDeclarationEnvironment>();

/**
 * Use only with deterministic, repository-owned signature factories. Their
 * closed environments are immutable and checked before the factory returns.
 * Cache only that successful empty-input reference; every caller must still
 * validate its supplied environment, model parameters and proofs on each use.
 */
export function checkedFormalSignatureReference(
    factory: SignatureFactory
): CoreLfDeclarationEnvironment {
    const reference = references.get(factory);
    if (reference !== undefined) return reference;
    const checked = factory([]);
    references.set(factory, checked);
    return checked;
}
