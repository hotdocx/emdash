/**
 * MIGRATE-1D replacement-readiness and physical-deletion boundary audit.
 */

import assert from 'node:assert';
import {
    existsSync,
    readFileSync,
    readdirSync
} from 'node:fs';
import {
    dirname,
    extname,
    relative,
    resolve,
    sep
} from 'node:path';
import { describe, it } from 'node:test';
import {
    LEGACY_MIGRATION_INVENTORY,
    LEGACY_MIGRATION_READINESS,
    LegacyMigrationReadiness,
    validateLegacyMigrationReadiness
} from '../src/v3_2';

const repositoryRoot = resolve(dirname(__filename), '..');

interface ImportEdge {
    readonly importer: string;
    readonly target: string;
}

const repositoryPath = (absolutePath: string): string =>
    relative(repositoryRoot, absolutePath).split(sep).join('/');

const sourceFilesUnder = (directory: string): string[] => {
    const absoluteDirectory = resolve(repositoryRoot, directory);
    const found: string[] = [];

    for (const entry of readdirSync(absoluteDirectory, {
        withFileTypes: true
    })) {
        const absoluteEntry = resolve(absoluteDirectory, entry.name);
        if (entry.isDirectory()) {
            found.push(...sourceFilesUnder(repositoryPath(absoluteEntry)));
        } else if (
            entry.isFile() &&
            ['.ts', '.tsx'].includes(extname(entry.name))
        ) {
            found.push(repositoryPath(absoluteEntry));
        }
    }

    return found.sort();
};

const moduleSpecifiers = (file: string): string[] => {
    const source = readFileSync(resolve(repositoryRoot, file), 'utf8');
    const fromSpecifiers = [...source.matchAll(
        /\bfrom\s+['"]([^'"]+)['"]/g
    )].map(match => match[1]);
    const sideEffectSpecifiers = [...source.matchAll(
        /\bimport\s+['"]([^'"]+)['"]/g
    )].map(match => match[1]);
    return [...new Set([
        ...fromSpecifiers,
        ...sideEffectSpecifiers
    ])];
};

const resolveRelativeModule = (
    importer: string,
    specifier: string
): string | undefined => {
    if (!specifier.startsWith('.')) return undefined;

    const rawTarget = resolve(
        dirname(resolve(repositoryRoot, importer)),
        specifier
    );
    const extension = extname(rawTarget);
    const candidates = extension === '.js'
        ? [
            rawTarget.slice(0, -extension.length) + '.ts',
            rawTarget.slice(0, -extension.length) + '.tsx'
        ]
        : extension.length > 0
            ? [rawTarget]
            : [
                `${rawTarget}.ts`,
                `${rawTarget}.tsx`,
                resolve(rawTarget, 'index.ts'),
                resolve(rawTarget, 'index.tsx')
            ];
    const target = candidates.find(candidate => existsSync(candidate));
    return target === undefined ? undefined : repositoryPath(target);
};

const codeFiles = [
    ...sourceFilesUnder('src'),
    ...sourceFilesUnder('tests'),
    ...sourceFilesUnder('emdash-template/src')
];

const importEdges: readonly ImportEdge[] = codeFiles.flatMap(importer =>
    moduleSpecifiers(importer).flatMap(specifier => {
        const target = resolveRelativeModule(importer, specifier);
        return target === undefined ? [] : [{ importer, target }];
    })
);

const sourceDeletionSet = new Set(
    LEGACY_MIGRATION_READINESS.deletionBoundary.sourceFiles
);
const testDeletionSet = new Set(
    LEGACY_MIGRATION_READINESS.deletionBoundary.testFiles
);
const auxiliaryDeletionSet = new Set(
    LEGACY_MIGRATION_READINESS.deletionBoundary.auxiliaryFiles
);
const completeDeletionSet = new Set([
    ...sourceDeletionSet,
    ...testDeletionSet,
    ...auxiliaryDeletionSet
]);

const uniqueSorted = (values: readonly string[]): string[] =>
    [...new Set(values)].sort();

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

const cloneReadiness = (): LegacyMigrationReadiness =>
    JSON.parse(JSON.stringify(LEGACY_MIGRATION_READINESS));

describe('TypeScript v3.2 MIGRATE-1D deletion readiness', () => {
    it('freezes the exact inventory-derived deletion boundary', () => {
        assert.equal(LEGACY_MIGRATION_READINESS.revision, 'MIGRATE-1D');
        assert.equal(
            LEGACY_MIGRATION_READINESS.inventoryRevision,
            LEGACY_MIGRATION_INVENTORY.revision
        );
        assert.equal(
            LEGACY_MIGRATION_READINESS.status,
            'ready-for-physical-deletion'
        );
        assert.equal(LEGACY_MIGRATION_READINESS.nextSlice, 'MIGRATE-2');
        assert.deepEqual(
            LEGACY_MIGRATION_READINESS.deletionBoundary.sourceFiles,
            LEGACY_MIGRATION_INVENTORY.sourceFiles.map(entry => entry.file)
        );
        assert.deepEqual(
            LEGACY_MIGRATION_READINESS.deletionBoundary.testFiles,
            LEGACY_MIGRATION_INVENTORY.testFiles.map(entry => entry.file)
        );
        assert.deepEqual(
            LEGACY_MIGRATION_READINESS.deletionBoundary.auxiliaryFiles,
            ['tests/utils.ts']
        );
        assert.equal(completeDeletionSet.size, 36);
    });

    it('retains only surviving evidence for every mechanism decision', () => {
        for (const mechanism of LEGACY_MIGRATION_INVENTORY.mechanisms) {
            assert.equal(
                mechanism.disposition === 'delete'
                    ? mechanism.state === 'ready-to-delete'
                    : mechanism.state === 'covered',
                true,
                `${mechanism.id} has an unfinished disposition`
            );
            assert.ok(mechanism.evidence.length > 0);
            for (const evidence of mechanism.evidence) {
                assert.equal(
                    completeDeletionSet.has(evidence),
                    false,
                    `${mechanism.id} relies on deletion target ${evidence}`
                );
                assert.equal(
                    existsSync(resolve(repositoryRoot, evidence)),
                    true,
                    `${mechanism.id} evidence ${evidence} is absent`
                );
            }
        }
    });

    it('proves the legacy source and test graphs close over the deletion set', () => {
        const sourceEdges = importEdges.filter(edge =>
            sourceDeletionSet.has(edge.importer)
        );
        assert.equal(
            sourceEdges.every(edge => sourceDeletionSet.has(edge.target)),
            true
        );

        const testEdges = importEdges.filter(edge =>
            testDeletionSet.has(edge.importer)
        );
        assert.equal(
            testEdges.every(edge => completeDeletionSet.has(edge.target)),
            true
        );

        const externalSourceImporters = uniqueSorted(
            importEdges
                .filter(edge =>
                    sourceDeletionSet.has(edge.target) &&
                    !sourceDeletionSet.has(edge.importer) &&
                    !testDeletionSet.has(edge.importer)
                )
                .map(edge => edge.importer)
        );
        assert.deepEqual(externalSourceImporters, [
            'emdash-template/src/emdash_api.ts',
            'tests/main_tests.ts'
        ]);

        const externalTestImporters = uniqueSorted(
            importEdges
                .filter(edge =>
                    testDeletionSet.has(edge.target) &&
                    !testDeletionSet.has(edge.importer)
                )
                .map(edge => edge.importer)
        );
        assert.deepEqual(externalTestImporters, ['tests/main_tests.ts']);

        const auxiliaryImporters = uniqueSorted(
            importEdges
                .filter(edge => auxiliaryDeletionSet.has(edge.target))
                .map(edge => edge.importer)
        );
        assert.ok(auxiliaryImporters.length > 0);
        assert.equal(
            auxiliaryImporters.every(importer =>
                testDeletionSet.has(importer)
            ),
            true
        );
    });

    it('keeps v3.2 implementation and tests isolated from legacy modules', () => {
        const v3SourceFiles = codeFiles.filter(file =>
            file.startsWith('src/v3_2/')
        );
        const v3SourceEdges = importEdges.filter(edge =>
            v3SourceFiles.includes(edge.importer)
        );
        assert.equal(
            v3SourceEdges.every(edge => edge.target.startsWith('src/v3_2/')),
            true
        );

        const v3TestEdges = importEdges.filter(edge =>
            edge.importer.startsWith('tests/v3_2_')
        );
        assert.equal(
            v3TestEdges.some(edge => completeDeletionSet.has(edge.target)),
            false
        );
    });

    it('records every direct and transitive consumer edit before deletion', () => {
        assert.deepEqual(
            LEGACY_MIGRATION_READINESS.deletionBoundary.requiredEdits.map(
                entry => entry.file
            ),
            [
                'tests/main_tests.ts',
                'tests/v3_2_migration_inventory_tests.ts',
                'tests/v3_2_migration_readiness_tests.ts',
                'emdash-template/src/emdash_api.ts',
                'emdash-template/src/App.tsx',
                'emdash-template/README.md',
                'package.json',
                'pnpm-lock.yaml'
            ]
        );
        for (
            const edit of
            LEGACY_MIGRATION_READINESS.deletionBoundary.requiredEdits
        ) {
            assert.equal(
                existsSync(resolve(repositoryRoot, edit.file)),
                true,
                `Required edit ${edit.file} is absent`
            );
        }

        assert.deepEqual(
            uniqueSorted(
                importEdges
                    .filter(edge =>
                        edge.importer ===
                            'emdash-template/src/emdash_api.ts' &&
                        sourceDeletionSet.has(edge.target)
                    )
                    .map(edge => edge.target)
            ),
            [...sourceDeletionSet].sort()
        );
        assert.ok(
            moduleSpecifiers('emdash-template/src/App.tsx').includes(
                './emdash_api'
            )
        );
        assert.match(
            readFileSync(
                resolve(repositoryRoot, 'emdash-template/README.md'),
                'utf8'
            ),
            /\.\.\/src\/types\.ts/
        );
        assert.equal(
            readFileSync(resolve(repositoryRoot, 'package.json'), 'utf8')
                .includes('"parsimmon"'),
            true
        );
    });

    it('is deeply frozen and rejects readiness-boundary drift', () => {
        assertDeepFrozen(LEGACY_MIGRATION_READINESS);
        assert.doesNotThrow(() => validateLegacyMigrationReadiness());
        assert.equal(
            LEGACY_MIGRATION_READINESS.checkpointGates.length,
            6
        );

        const changed = cloneReadiness() as unknown as {
            deletionBoundary: {
                requiredEdits: Array<{ file: string }>;
            };
        };
        changed.deletionBoundary.requiredEdits[0].file = 'tests/other.ts';
        assert.throws(
            () => validateLegacyMigrationReadiness(
                changed as unknown as LegacyMigrationReadiness
            ),
            /differs from the canonical MIGRATE-1D physical-deletion boundary/
        );
    });
});
