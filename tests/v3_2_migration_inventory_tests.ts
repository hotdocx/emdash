/**
 * Focused MIGRATE-1 closed-world source and test disposition checks.
 */

import assert from 'node:assert';
import {
    existsSync,
    readFileSync,
    readdirSync
} from 'node:fs';
import { dirname, resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    LEGACY_MIGRATION_INVENTORY,
    LegacyMigrationInventory,
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

const legacyTestImports = (): string[] => {
    const main = readFileSync(
        resolve(repositoryRoot, 'tests/main_tests.ts'),
        'utf8'
    );
    return [...main.matchAll(/^import ['"]\.\/([^'"]+)['"];/gm)]
        .map(match => match[1])
        .filter(name => !name.startsWith('v3_2_'))
        .map(name => `tests/${name}.ts`);
};

const legacySourceFiles = (): string[] =>
    readdirSync(resolve(repositoryRoot, 'src'), {
        withFileTypes: true
    })
        .filter(entry => entry.isFile() && entry.name.endsWith('.ts'))
        .map(entry => `src/${entry.name}`)
        .sort();

describe('TypeScript v3.2 MIGRATE-1 legacy inventory', () => {
    it('classifies all ten generic mechanisms with exact next boundaries', () => {
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
        assert.equal(
            LEGACY_MIGRATION_INVENTORY.mechanisms.find(
                entry => entry.id === 'higher-order-pattern-unification'
            )?.state,
            'covered'
        );
        assert.equal(
            LEGACY_MIGRATION_INVENTORY.mechanisms.find(
                entry => entry.id === 'proof-state-traversal'
            )?.state,
            'covered'
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

    it('accounts for every root legacy source file exactly once', () => {
        assert.deepEqual(
            LEGACY_MIGRATION_INVENTORY.sourceFiles
                .map(entry => entry.file)
                .sort(),
            legacySourceFiles()
        );
        assert.equal(
            new Set(
                LEGACY_MIGRATION_INVENTORY.sourceFiles.map(
                    entry => entry.file
                )
            ).size,
            LEGACY_MIGRATION_INVENTORY.sourceFiles.length
        );
    });

    it('accounts for every loaded legacy test in runner order', () => {
        assert.deepEqual(
            LEGACY_MIGRATION_INVENTORY.testFiles.map(entry => entry.file),
            legacyTestImports()
        );
        assert.equal(
            new Set(
                LEGACY_MIGRATION_INVENTORY.testFiles.map(entry => entry.file)
            ).size,
            LEGACY_MIGRATION_INVENTORY.testFiles.length
        );
    });

    it('points every claimed replacement test at a tracked file', () => {
        for (const entry of LEGACY_MIGRATION_INVENTORY.testFiles) {
            for (const replacement of entry.replacementTests) {
                assert.equal(
                    existsSync(resolve(repositoryRoot, replacement)),
                    true,
                    `${entry.file} replacement ${replacement} is absent`
                );
                assert.match(replacement, /^tests\/v3_2_.*_tests\.ts$/);
            }
        }
    });

    it('is deeply frozen and rejects any disposition drift', () => {
        assertDeepFrozen(LEGACY_MIGRATION_INVENTORY);
        assert.doesNotThrow(() => validateLegacyMigrationInventory());

        const changedState = cloneInventory() as unknown as {
            mechanisms: Array<{ state: string }>;
        };
        changedState.mechanisms[0].state = 'partial';
        assert.throws(
            () => validateLegacyMigrationInventory(
                changedState as unknown as LegacyMigrationInventory
            ),
            /differs from the canonical MIGRATE-1D disposition ledger/
        );

        const missingTest = cloneInventory() as unknown as {
            testFiles: unknown[];
        };
        missingTest.testFiles.pop();
        assert.throws(
            () => validateLegacyMigrationInventory(
                missingTest as unknown as LegacyMigrationInventory
            ),
            /differs from the canonical MIGRATE-1D disposition ledger/
        );
    });
});
