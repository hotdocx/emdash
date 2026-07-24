/**
 * MIGRATE-2 post-deletion inventory and completion checks.
 */

import assert from 'node:assert';
import {
    existsSync,
    readFileSync
} from 'node:fs';
import { dirname, resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    LEGACY_MIGRATION_COMPLETION,
    LEGACY_MIGRATION_INVENTORY,
    LEGACY_MIGRATION_READINESS,
    LegacyMigrationCompletion,
    LegacyMigrationInventory,
    validateLegacyMigrationCompletion,
    validateLegacyMigrationInventory
} from '../src/v3_2';

const repositoryRoot = resolve(dirname(__filename), '..');

const assertDeepFrozen = (
    value: unknown,
    seen = new Set<object>()
): void => {
    if (
        value === null ||
        typeof value !== 'object' ||
        seen.has(value)
    ) {
        return;
    }
    seen.add(value);
    assert.equal(Object.isFrozen(value), true);
    for (const child of Object.values(value)) {
        assertDeepFrozen(child, seen);
    }
};

const cloneInventory = (): LegacyMigrationInventory =>
    JSON.parse(JSON.stringify(LEGACY_MIGRATION_INVENTORY));

const cloneCompletion = (): LegacyMigrationCompletion =>
    JSON.parse(JSON.stringify(LEGACY_MIGRATION_COMPLETION));

const runnerImports = (): string[] => {
    const main = readFileSync(
        resolve(repositoryRoot, 'tests/main_tests.ts'),
        'utf8'
    );
    return [...main.matchAll(/^import ['"]\.\/([^'"]+)['"];/gm)]
        .map(match => match[1]);
};

describe('TypeScript v3.2 MIGRATE-2 legacy completion', () => {
    it('preserves the exact reviewed mechanism dispositions', () => {
        assert.deepEqual(
            LEGACY_MIGRATION_INVENTORY.mechanisms.map(entry => entry.id),
            [
                'bidirectional-infer-check',
                'contextual-metavariables',
                'higher-order-pattern-unification',
                'rule-authority-separation',
                'capture-avoiding-substitution',
                'proof-state-traversal',
                'direct-typescript-constructors',
                'legacy-category-constructors',
                'global-mutable-setup',
                'legacy-parser'
            ]
        );
        assert.equal(LEGACY_MIGRATION_INVENTORY.revision, 'MIGRATE-1D');
        assert.equal(
            LEGACY_MIGRATION_INVENTORY.status,
            'ready-for-physical-deletion'
        );
        assert.equal(LEGACY_MIGRATION_INVENTORY.nextSlice, 'MIGRATE-2');
        assert.equal(
            LEGACY_MIGRATION_INVENTORY.mechanisms.every(entry =>
                entry.disposition === 'delete'
                    ? entry.state === 'ready-to-delete'
                    : entry.state === 'covered'
            ),
            true
        );
    });

    it('records and removes all 36 frozen deletion targets', () => {
        assert.deepEqual(
            LEGACY_MIGRATION_COMPLETION.deletedFiles,
            [
                ...LEGACY_MIGRATION_READINESS.deletionBoundary.sourceFiles,
                ...LEGACY_MIGRATION_READINESS.deletionBoundary.testFiles,
                ...LEGACY_MIGRATION_READINESS.deletionBoundary.auxiliaryFiles
            ]
        );
        assert.equal(LEGACY_MIGRATION_COMPLETION.deletedFiles.length, 36);
        assert.equal(
            new Set(LEGACY_MIGRATION_COMPLETION.deletedFiles).size,
            36
        );
        for (const file of LEGACY_MIGRATION_COMPLETION.deletedFiles) {
            assert.equal(
                existsSync(resolve(repositoryRoot, file)),
                false,
                `MIGRATE-2 deletion target ${file} still exists`
            );
        }
    });

    it('loads only retained v3.2 tests through the root runner', () => {
        const imports = runnerImports();
        assert.ok(imports.length > 0);
        assert.equal(
            imports.every(name => name.startsWith('v3_2_')),
            true
        );
        assert.equal(
            imports.includes('v3_2_browser_api_tests'),
            true
        );
        for (const name of imports) {
            assert.equal(
                existsSync(resolve(repositoryRoot, `tests/${name}.ts`)),
                true,
                `Retained runner target tests/${name}.ts is absent`
            );
        }
    });

    it('keeps every surviving replacement and mechanism evidence present', () => {
        const deleted = new Set(LEGACY_MIGRATION_COMPLETION.deletedFiles);
        for (const entry of LEGACY_MIGRATION_INVENTORY.testFiles) {
            for (const replacement of entry.replacementTests) {
                assert.equal(deleted.has(replacement), false);
                assert.equal(
                    existsSync(resolve(repositoryRoot, replacement)),
                    true,
                    `${entry.file} replacement ${replacement} is absent`
                );
                assert.match(replacement, /^tests\/v3_2_.*_tests\.ts$/);
            }
        }
        for (const entry of LEGACY_MIGRATION_INVENTORY.mechanisms) {
            for (const evidence of entry.evidence) {
                assert.equal(deleted.has(evidence), false);
                assert.equal(
                    existsSync(resolve(repositoryRoot, evidence)),
                    true,
                    `${entry.id} evidence ${evidence} is absent`
                );
            }
        }
    });

    it('publishes the exact no-compatibility completion boundary', () => {
        assert.equal(LEGACY_MIGRATION_COMPLETION.revision, 'MIGRATE-2');
        assert.equal(LEGACY_MIGRATION_COMPLETION.status, 'complete');
        assert.equal(
            LEGACY_MIGRATION_COMPLETION.readinessRevision,
            LEGACY_MIGRATION_READINESS.revision
        );
        assert.deepEqual(
            LEGACY_MIGRATION_COMPLETION.completedEdits,
            LEGACY_MIGRATION_READINESS.deletionBoundary.requiredEdits.map(
                edit => edit.file
            )
        );
        assert.deepEqual(
            LEGACY_MIGRATION_COMPLETION.removedRuntimeDependencies,
            ['parsimmon']
        );
        assert.equal(
            LEGACY_MIGRATION_COMPLETION.browserEntryPoint,
            'src/v3_2/browser.ts'
        );
        assert.equal(
            LEGACY_MIGRATION_COMPLETION.compatibilityApiRetained,
            false
        );
        assert.equal(
            LEGACY_MIGRATION_COMPLETION.parserReplacement,
            'not-implemented-h06-required'
        );
        assert.equal(
            LEGACY_MIGRATION_COMPLETION.nextSlice,
            'GRADUATE-1'
        );
    });

    it('deep-freezes all records and rejects inventory/completion drift', () => {
        assertDeepFrozen(LEGACY_MIGRATION_INVENTORY);
        assertDeepFrozen(LEGACY_MIGRATION_COMPLETION);
        assert.doesNotThrow(() => validateLegacyMigrationInventory());
        assert.doesNotThrow(() => validateLegacyMigrationCompletion());

        const changedInventory = cloneInventory() as unknown as {
            mechanisms: Array<{ state: string }>;
        };
        changedInventory.mechanisms[0].state = 'partial';
        assert.throws(
            () => validateLegacyMigrationInventory(
                changedInventory as unknown as LegacyMigrationInventory
            ),
            /differs from the canonical MIGRATE-1D disposition ledger/
        );

        const changedCompletion = cloneCompletion() as unknown as {
            completedEdits: string[];
        };
        changedCompletion.completedEdits.pop();
        assert.throws(
            () => validateLegacyMigrationCompletion(
                changedCompletion as unknown as LegacyMigrationCompletion
            ),
            /differs from the canonical MIGRATE-2 deletion result/
        );
    });
});
