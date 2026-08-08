/** Focused AI-PROOF-2 tests for fresh proof documents and artifacts. */

import assert from 'node:assert';
import { readFileSync } from 'node:fs';
import path from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PROOF_DOCUMENT_PROFILE,
    CoreProofArtifact,
    CoreProofArtifactError,
    CoreProofArtifactFingerprint,
    assertCoreProofArtifactCurrent,
    compileCoreAiProofDemo,
    coreProofArtifactJsonlRecords,
    createCoreAiProofDemoFingerprint,
    createCoreProofArtifactFingerprint,
    formatCoreProofArtifact,
    serializeCoreProofArtifact,
    serializeCoreProofArtifactJsonl,
    serializeCoreProofDocumentProfile,
    validateCoreProofArtifactFingerprint
} from '../src/v3_2';

const hash = (digit: string): string =>
    `sha256:${digit.repeat(64)}`;

const fingerprint = () => createCoreAiProofDemoFingerprint(
    hash('a'),
    hash('b')
);

describe('TypeScript v3.2 AI-PROOF-2 proof documents', () => {
    it('compiles a complete theorem in a fresh checked session', () => {
        const first = compileCoreAiProofDemo(
            'complete_identity',
            fingerprint()
        );
        const second = compileCoreAiProofDemo(
            'complete_identity',
            fingerprint()
        );

        assert.equal(first.artifact.state.status, 'complete');
        assert.ok(first.checkedTerm);
        assert.equal(first.checkedTerm.tag, 'lambda');
        assert.equal(
            first.artifact.checkedCore,
            '(lambda (binder explicit natural (free "AIProofA")) ' +
            '(bound 0))'
        );
        assert.deepEqual(first.artifact.state.goals, []);
        assert.equal(Object.isFrozen(first.artifact), true);
        assert.equal(Object.isFrozen(first.artifact.fingerprint), true);
        assert.equal(
            serializeCoreProofArtifact(first.artifact),
            serializeCoreProofArtifact(second.artifact)
        );
    });

    it('publishes an incomplete theorem only as stable named state', () => {
        const first = compileCoreAiProofDemo('open_identity', fingerprint());
        const second = compileCoreAiProofDemo('open_identity', fingerprint());

        assert.equal(first.artifact.state.status, 'incomplete');
        assert.equal(first.checkedTerm, undefined);
        assert.equal(first.artifact.checkedCore, undefined);
        assert.deepEqual(
            first.artifact.state.goals.map(goal => goal.id),
            ['body']
        );
        assert.deepEqual(first.artifact.state.goals[0].context, [{
            index: 0,
            name: 'value',
            plicity: 'explicit',
            variation: 'natural',
            type: 'AIProofA'
        }]);
        assert.equal(first.artifact.state.goals[0].target, 'AIProofA');
        assert.match(first.artifact.state.term, /\?body\[#0\]/u);

        const serialized = serializeCoreProofArtifact(first.artifact);
        assert.equal(
            serialized,
            serializeCoreProofArtifact(second.artifact)
        );
        assert.doesNotMatch(serialized, /\?m\d|session|Symbol/u);
        assert.doesNotMatch(serialized, /checkedCore/u);
    });

    it('emits one proof JSONL record followed by ordered goal records', () => {
        const complete = compileCoreAiProofDemo(
            'complete_identity',
            fingerprint()
        ).artifact;
        const incomplete = compileCoreAiProofDemo(
            'open_identity',
            fingerprint()
        ).artifact;

        const completeRecords = coreProofArtifactJsonlRecords(complete);
        assert.equal(completeRecords.length, 1);
        assert.equal(completeRecords[0].kind, 'proof');

        const incompleteRecords = coreProofArtifactJsonlRecords(incomplete);
        assert.deepEqual(
            incompleteRecords.map(record => record.kind),
            ['proof', 'goal']
        );
        const lines = serializeCoreProofArtifactJsonl(incomplete)
            .trimEnd()
            .split('\n')
            .map(line => JSON.parse(line) as { kind: string });
        assert.deepEqual(lines.map(line => line.kind), ['proof', 'goal']);
        assert.equal(
            serializeCoreProofArtifactJsonl(incomplete).endsWith('\n'),
            true
        );
        assert.match(formatCoreProofArtifact(incomplete), /Goal body/u);
        assert.match(formatCoreProofArtifact(complete), /complete/u);
    });

    it('canonicalizes dependency stamps and rejects malformed inputs', () => {
        const canonical = createCoreProofArtifactFingerprint({
            source: { id: 'local/source.ts', sha256: hash('1') },
            profileSha256: hash('2'),
            dependencies: [
                { moduleId: 'z.module', interfaceSha256: hash('3') },
                { moduleId: 'a.module', interfaceSha256: hash('4') }
            ]
        });
        assert.deepEqual(
            canonical.dependencies.map(item => item.moduleId),
            ['a.module', 'z.module']
        );
        assert.equal(Object.isFrozen(canonical.dependencies), true);

        const wrongProfile = {
            ...canonical,
            profile: {
                ...canonical.profile,
                id: 'wrong-profile'
            }
        } as unknown as CoreProofArtifactFingerprint;
        assert.throws(
            () => validateCoreProofArtifactFingerprint(wrongProfile),
            (error: unknown) => {
                assert.ok(error instanceof CoreProofArtifactError);
                assert.equal(error.code, 'INVALID_FINGERPRINT');
                assert.equal(error.path, 'fingerprint.profile.id');
                return true;
            }
        );

        assert.throws(
            () => createCoreProofArtifactFingerprint({
                source: { id: 'local/source.ts', sha256: 'sha256:bad' },
                profileSha256: hash('2')
            }),
            (error: unknown) => {
                assert.ok(error instanceof CoreProofArtifactError);
                assert.equal(error.code, 'INVALID_FINGERPRINT');
                return true;
            }
        );
        assert.throws(
            () => createCoreProofArtifactFingerprint({
                source: { id: 'local/source.ts', sha256: hash('1') },
                profileSha256: hash('2'),
                dependencies: [
                    { moduleId: 'same', interfaceSha256: hash('3') },
                    { moduleId: 'same', interfaceSha256: hash('4') }
                ]
            }),
            (error: unknown) => {
                assert.ok(error instanceof CoreProofArtifactError);
                assert.equal(error.code, 'DUPLICATE_DEPENDENCY');
                return true;
            }
        );
    });

    it('rejects stale source, profile, or dependency fingerprints', () => {
        const stored = compileCoreAiProofDemo(
            'complete_identity',
            fingerprint()
        ).artifact;
        assert.doesNotThrow(() => assertCoreProofArtifactCurrent(
            stored,
            fingerprint()
        ));

        const changed = createCoreAiProofDemoFingerprint(
            hash('c'),
            hash('b')
        );
        assert.throws(
            () => assertCoreProofArtifactCurrent(stored, changed),
            (error: unknown) => {
                assert.ok(error instanceof CoreProofArtifactError);
                assert.equal(error.code, 'STALE_ARTIFACT');
                assert.match(error.path, /complete_identity/u);
                return true;
            }
        );

        const oldRevision = {
            ...stored,
            revision: 'emdash-proof-artifact-v0'
        } as unknown as CoreProofArtifact;
        assert.throws(
            () => assertCoreProofArtifactCurrent(
                oldRevision,
                fingerprint()
            ),
            (error: unknown) => {
                assert.ok(error instanceof CoreProofArtifactError);
                assert.equal(error.code, 'STALE_ARTIFACT');
                assert.match(error.path, /revision$/u);
                return true;
            }
        );

        const missingCheckedCore = {
            ...stored,
            checkedCore: undefined
        } as CoreProofArtifact;
        assert.throws(
            () => assertCoreProofArtifactCurrent(
                missingCheckedCore,
                fingerprint()
            ),
            (error: unknown) => {
                assert.ok(error instanceof CoreProofArtifactError);
                assert.equal(error.code, 'INVALID_ARTIFACT');
                assert.match(error.path, /checkedCore$/u);
                return true;
            }
        );
    });

    it('keeps profile and proof-document sources browser-safe', () => {
        assert.equal(
            CORE_PROOF_DOCUMENT_PROFILE.nodeBuiltinDependency,
            false
        );
        const repositoryRoot = path.resolve(__dirname, '..');
        for (const relative of [
            'src/v3_2/proof_plan.ts',
            'src/v3_2/proof_document.ts',
            'src/v3_2/ai_proof_demo.ts'
        ]) {
            const source = readFileSync(
                path.join(repositoryRoot, relative),
                'utf8'
            );
            assert.doesNotMatch(source, /from ['"]node:/u);
        }
        assert.match(
            serializeCoreProofDocumentProfile(),
            /emdash-proof-document-compiler-v1/u
        );
    });
});
