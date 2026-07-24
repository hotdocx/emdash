/**
 * MIGRATE-2 post-deletion import, consumer, and package audit.
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
    LEGACY_MIGRATION_COMPLETION,
    LEGACY_MIGRATION_READINESS,
    LegacyMigrationReadiness,
    validateLegacyMigrationReadiness
} from '../src/v3_2';

const repositoryRoot = resolve(dirname(__filename), '..');

interface ModuleImport {
    readonly importer: string;
    readonly specifier: string;
    readonly target?: string;
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

const relativeModuleCandidates = (
    importer: string,
    specifier: string
): string[] => {
    if (!specifier.startsWith('.')) return [];

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
    return candidates.map(repositoryPath);
};

const resolveRelativeModule = (
    importer: string,
    specifier: string
): string | undefined => relativeModuleCandidates(importer, specifier)
    .find(candidate => existsSync(resolve(repositoryRoot, candidate)));

const codeFiles = [
    ...sourceFilesUnder('src'),
    ...sourceFilesUnder('tests'),
    ...sourceFilesUnder('emdash-template/src')
];

const moduleImports: readonly ModuleImport[] = codeFiles.flatMap(importer =>
    moduleSpecifiers(importer).map(specifier => ({
        importer,
        specifier,
        target: resolveRelativeModule(importer, specifier)
    }))
);

const deletionSet = new Set(LEGACY_MIGRATION_COMPLETION.deletedFiles);

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

const reachableBrowserModules = (): {
    readonly files: ReadonlySet<string>;
    readonly nodeImports: readonly ModuleImport[];
} => {
    const files = new Set<string>();
    const nodeImports: ModuleImport[] = [];
    const pending: string[] = [
        LEGACY_MIGRATION_COMPLETION.browserEntryPoint
    ];

    while (pending.length > 0) {
        const file = pending.pop() as string;
        if (files.has(file)) continue;
        files.add(file);

        for (
            const moduleImport of
            moduleImports.filter(entry => entry.importer === file)
        ) {
            if (moduleImport.specifier.startsWith('node:')) {
                nodeImports.push(moduleImport);
            }
            if (
                moduleImport.target?.startsWith('src/v3_2/') &&
                !files.has(moduleImport.target)
            ) {
                pending.push(moduleImport.target);
            }
        }
    }

    return { files, nodeImports };
};

describe('TypeScript v3.2 MIGRATE-2 physical deletion audit', () => {
    it('leaves no source/test/helper deletion target or forbidden import', () => {
        for (const file of deletionSet) {
            assert.equal(
                existsSync(resolve(repositoryRoot, file)),
                false,
                `Deleted legacy path ${file} reappeared`
            );
        }

        for (const moduleImport of moduleImports) {
            const forbiddenTargets = relativeModuleCandidates(
                moduleImport.importer,
                moduleImport.specifier
            ).filter(candidate => deletionSet.has(candidate));
            assert.deepEqual(
                forbiddenTargets,
                [],
                `${moduleImport.importer} imports deleted legacy module ` +
                    moduleImport.specifier
            );
        }

        assert.equal(
            sourceFilesUnder('src').every(file =>
                file.startsWith('src/v3_2/')
            ),
            true
        );
        assert.equal(
            sourceFilesUnder('tests').every(file =>
                file === 'tests/main_tests.ts' ||
                file.startsWith('tests/v3_2_')
            ),
            true
        );
    });

    it('keeps the browser product entry point transitively Node-free', () => {
        const reachable = reachableBrowserModules();
        assert.ok(reachable.files.size > 1);
        assert.deepEqual(reachable.nodeImports, []);
        assert.equal(
            reachable.files.has('src/v3_2/checker.ts'),
            true
        );
        assert.equal(
            reachable.files.has('src/v3_2/session.ts'),
            true
        );
        assert.equal(
            reachable.files.has('src/v3_2/manifest.ts'),
            true
        );
        assert.equal(
            [...reachable.files].some(file =>
                /(?:probe|differential|migration)\.ts$/.test(file)
            ),
            false
        );
    });

    it('rewrites the standalone fixture without a compatibility API', () => {
        const apiImports = moduleImports.filter(
            entry => entry.importer ===
                'emdash-template/src/emdash_api.ts'
        );
        assert.deepEqual(
            apiImports.map(entry => entry.target),
            ['src/v3_2/browser.ts']
        );

        const app = readFileSync(
            resolve(repositoryRoot, 'emdash-template/src/App.tsx'),
            'utf8'
        );
        assert.match(app, /new emdash\.CoreElaborationSession\(\)/);
        assert.match(app, /new emdash\.CoreChecker\(session\)/);
        assert.doesNotMatch(
            app,
            /\b(?:D0|D1|MkCat|ComposeMorph|MkFunctorTerm|defineGlobal|globalDefs|resetMyLambdaPi|elaborate)\b/
        );

        const api = readFileSync(
            resolve(repositoryRoot, 'emdash-template/src/emdash_api.ts'),
            'utf8'
        );
        assert.doesNotMatch(
            api,
            /\b(?:D0|D1|types|state|stdlib|parser|globals)\b/
        );
    });

    it('updates fixture packaging and removes the parser dependency', () => {
        const fixtureReadme = readFileSync(
            resolve(repositoryRoot, 'emdash-template/README.md'),
            'utf8'
        );
        assert.match(fixtureReadme, /src\/v3_2\/browser\.ts/);
        assert.doesNotMatch(fixtureReadme, /\.\.\/src\/types\.ts/);
        assert.doesNotMatch(fixtureReadme, /\.\.\/\.\.\/src\/(?!v3_2)/);

        const packageManifest = JSON.parse(readFileSync(
            resolve(repositoryRoot, 'package.json'),
            'utf8'
        )) as {
            dependencies?: Record<string, string>;
        };
        assert.equal(packageManifest.dependencies?.parsimmon, undefined);
        assert.doesNotMatch(
            readFileSync(resolve(repositoryRoot, 'pnpm-lock.yaml'), 'utf8'),
            /\bparsimmon\b/
        );
    });

    it('fulfills every frozen consumer edit and retains no global runner setup', () => {
        assert.deepEqual(
            LEGACY_MIGRATION_COMPLETION.completedEdits,
            LEGACY_MIGRATION_READINESS.deletionBoundary.requiredEdits.map(
                edit => edit.file
            )
        );
        for (const file of LEGACY_MIGRATION_COMPLETION.completedEdits) {
            assert.equal(
                existsSync(resolve(repositoryRoot, file)),
                true,
                `Completed edit ${file} is absent`
            );
        }

        const runner = readFileSync(
            resolve(repositoryRoot, 'tests/main_tests.ts'),
            'utf8'
        );
        assert.doesNotMatch(
            runner,
            /getDebugVerbose|setDebugVerbose|\.\.\/src\/state/
        );
        assert.equal(
            [...runner.matchAll(/^import ['"]\.\/([^'"]+)['"];/gm)]
                .every(match => match[1].startsWith('v3_2_')),
            true
        );
    });

    it('preserves the frozen readiness record and rejects its drift', () => {
        assertDeepFrozen(LEGACY_MIGRATION_READINESS);
        assert.doesNotThrow(() => validateLegacyMigrationReadiness());

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
