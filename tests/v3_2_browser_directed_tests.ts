/**
 * Focused BROWSER-DIRECTED-1A additive browser-entry tests.
 */

import assert from 'node:assert/strict';
import {
    createHash
} from 'node:crypto';
import {
    existsSync,
    readFileSync
} from 'node:fs';
import {
    dirname,
    resolve
} from 'node:path';
import {
    describe,
    it
} from 'node:test';
import ts from 'typescript';
import * as frozenBrowser from '../src/v3_2/browser';
import {
    CORE_DIRECTED_BROWSER_DEMO_BOUNDARY,
    CORE_MVP_MANIFEST,
    CoreDirectedDependentDemoResult,
    formatCoreDirectedDependentDemo,
    runCoreDirectedBrowserDemo
} from '../src/v3_2/browser_directed';

let cachedResult: CoreDirectedDependentDemoResult | undefined;

const result = (): CoreDirectedDependentDemoResult => {
    cachedResult ??= runCoreDirectedBrowserDemo();
    return cachedResult;
};

const nodeBuiltins = new Set([
    'assert',
    'buffer',
    'child_process',
    'crypto',
    'events',
    'fs',
    'http',
    'https',
    'module',
    'net',
    'os',
    'path',
    'perf_hooks',
    'process',
    'stream',
    'timers',
    'tls',
    'tty',
    'url',
    'util',
    'v8',
    'vm',
    'worker_threads',
    'zlib'
]);

const moduleSpecifiers = (
    file: string,
    source: string
): readonly string[] => {
    const syntax = ts.createSourceFile(
        file,
        source,
        ts.ScriptTarget.Latest,
        true,
        ts.ScriptKind.TS
    );
    const specifiers: string[] = [];
    const visit = (node: ts.Node): void => {
        if (
            (
                ts.isImportDeclaration(node) ||
                ts.isExportDeclaration(node)
            ) &&
            node.moduleSpecifier !== undefined &&
            ts.isStringLiteral(node.moduleSpecifier)
        ) {
            specifiers.push(node.moduleSpecifier.text);
        }
        if (
            ts.isCallExpression(node) &&
            node.expression.kind === ts.SyntaxKind.ImportKeyword &&
            node.arguments.length === 1 &&
            ts.isStringLiteral(node.arguments[0])
        ) {
            specifiers.push(node.arguments[0].text);
        }
        ts.forEachChild(node, visit);
    };
    visit(syntax);
    return Object.freeze(specifiers);
};

const resolveLocalModule = (
    importingFile: string,
    specifier: string
): string => {
    const unresolved = resolve(dirname(importingFile), specifier);
    const candidates = specifier.endsWith('.js')
        ? [
            `${unresolved.slice(0, -3)}.ts`,
            `${unresolved.slice(0, -3)}.tsx`
        ]
        : [
            unresolved,
            `${unresolved}.ts`,
            `${unresolved}.tsx`,
            resolve(unresolved, 'index.ts')
        ];
    const resolved = candidates.find(candidate => existsSync(candidate));
    assert.notEqual(
        resolved,
        undefined,
        `Cannot resolve browser dependency ${specifier} from ${importingFile}`
    );
    return resolved as string;
};

const collectLocalClosure = (
    entry: string
): ReadonlySet<string> => {
    const pending = [resolve(entry)];
    const visited = new Set<string>();
    while (pending.length > 0) {
        const file = pending.pop() as string;
        if (visited.has(file)) continue;
        visited.add(file);
        const source = readFileSync(file, 'utf8');
        assert.doesNotMatch(
            source,
            /\brequire\s*\(/u,
            `Browser dependency uses runtime require: ${file}`
        );
        for (const specifier of moduleSpecifiers(file, source)) {
            if (specifier.startsWith('.')) {
                pending.push(resolveLocalModule(file, specifier));
                continue;
            }
            const bare = specifier.startsWith('node:')
                ? specifier.slice('node:'.length)
                : specifier.split('/')[0];
            assert.equal(
                specifier.startsWith('node:') || nodeBuiltins.has(bare),
                false,
                `Browser dependency reaches Node builtin ${specifier} ` +
                    `from ${file}`
            );
        }
    }
    return visited;
};

describe('BROWSER-DIRECTED-1A additive browser entry', () => {
    it('runs the actual reviewed dependent checker/evaluator witness', () => {
        const report = result();
        assert.equal(
            report.profile,
            CORE_DIRECTED_BROWSER_DEMO_BOUNDARY.continuationResultProfile
        );
        assert.equal(report.productionLambdapiDependency, false);
        assert.equal(
            report.negativeDiagnostic.code,
            'TYPE_MISMATCH'
        );
        assert.deepEqual(
            report.trace.map(entry => entry.step),
            [1, 2]
        );
        const formatted = formatCoreDirectedDependentDemo(report);
        assert.match(formatted, /Explicit Core:/u);
        assert.match(formatted, /Inferred type:/u);
        assert.match(formatted, /Reduced type:/u);
        assert.match(formatted, /Production Lambdapi dependency: no/u);
    });

    it('publishes a deeply frozen exact non-semantic boundary', () => {
        assert.equal(
            Object.isFrozen(CORE_DIRECTED_BROWSER_DEMO_BOUNDARY),
            true
        );
        assert.deepEqual(CORE_DIRECTED_BROWSER_DEMO_BOUNDARY, {
            revision: 'BROWSER-DIRECTED-1A',
            status: 'opt-in-browser-demonstration',
            baseProfile: 'emdash-v3.2-mvp-1',
            continuationResultProfile:
                'emdash-v3.2-dttlf-directed-1',
            entryPoint: 'src/v3_2/browser_directed.ts',
            actualCheckerAndEvaluatorExecute: true,
            productionLambdapiDependency: false,
            nodeBuiltinDependency: false,
            parserDependency: false,
            categoricalBrowserProfileIncluded: false,
            baseManifestUnchanged: true
        });
        assert.equal(
            CORE_MVP_MANIFEST.contentHash,
            'sha256:28834e9c0361b98e9f14f66f02aac8f59900a98b9c8c1ce1c62ae0e5396f8ff0'
        );
    });

    it('keeps the frozen minimal browser source and API unchanged', () => {
        const source = readFileSync('src/v3_2/browser.ts', 'utf8');
        assert.equal(
            createHash('sha256').update(source).digest('hex'),
            '9923a7a85672d6fbf6441f23f69f1062c702764167338ee40e1a65be9e42cfcc'
        );
        assert.equal('runCoreDirectedBrowserDemo' in frozenBrowser, false);
        assert.equal(
            'CORE_DIRECTED_BROWSER_DEMO_BOUNDARY' in frozenBrowser,
            false
        );
    });

    it('has a transitive local closure with no Node builtin', () => {
        const closure = collectLocalClosure(
            'src/v3_2/browser_directed.ts'
        );
        assert.equal(
            closure.has(resolve('src/v3_2/browser_directed.ts')),
            true
        );
        assert.equal(
            closure.has(resolve('src/v3_2/directed_dependent_demo.ts')),
            true
        );
        assert.equal(
            closure.has(resolve('src/v3_2/checker.ts')),
            true
        );
        assert.equal(
            closure.has(resolve('src/v3_2/lf_transfer_acquisition.ts')),
            false
        );
        assert.equal(closure.size >= 30, true);
    });

    it('keeps AI proof documents Node-free and the CLI outside', () => {
        const closure = collectLocalClosure(
            'src/v3_2/ai_proof_demo.ts'
        );
        assert.equal(
            closure.has(resolve('src/v3_2/ai_proof_demo.ts')),
            true
        );
        assert.equal(
            closure.has(resolve('src/v3_2/proof_document.ts')),
            true
        );
        assert.equal(
            closure.has(resolve('src/v3_2/proof_plan.ts')),
            true
        );
        assert.equal(
            closure.has(resolve('src/v3_2/checker.ts')),
            true
        );
        assert.equal(
            closure.has(resolve('src/v3_2/ai_proof_cli.ts')),
            false
        );
    });

    it('keeps the declaration workspace graph Node-free', () => {
        const closure = collectLocalClosure('src/v3_2/lf_workspace.ts');
        assert.equal(
            closure.has(resolve('src/v3_2/lf_workspace.ts')),
            true
        );
        assert.equal(
            closure.has(resolve('src/v3_2/lf_transfer_compiler.ts')),
            true
        );
        assert.equal(
            closure.has(resolve('src/v3_2/lf_transfer_visibility.ts')),
            true
        );
        assert.equal(
            closure.has(resolve('src/v3_2/lf_declarations.ts')),
            true
        );
        assert.equal(
            closure.has(resolve('src/v3_2/lf_transfer_acquisition.ts')),
            false
        );
        assert.equal(
            closure.has(resolve('src/v3_2/ai_proof_cli.ts')),
            false
        );
    });

    it('keeps exact-closure proof attachment Node-free', () => {
        const closure = collectLocalClosure(
            'src/v3_2/lf_workspace_proof.ts'
        );
        assert.equal(
            closure.has(resolve('src/v3_2/lf_workspace_proof.ts')),
            true
        );
        assert.equal(
            closure.has(resolve('src/v3_2/lf_workspace.ts')),
            true
        );
        assert.equal(
            closure.has(resolve('src/v3_2/proof_document.ts')),
            true
        );
        assert.equal(
            closure.has(resolve('src/v3_2/checker.ts')),
            true
        );
        assert.equal(
            closure.has(resolve('src/v3_2/ai_proof_cli.ts')),
            false
        );
        assert.equal(
            closure.has(resolve('src/v3_2/lf_transfer_acquisition.ts')),
            false
        );
    });

    it('keeps the general proof-development catalog Node-free', () => {
        const closure = collectLocalClosure(
            'src/v3_2/lf_proof_development.ts'
        );
        assert.equal(
            closure.has(resolve('src/v3_2/lf_proof_development.ts')),
            true
        );
        assert.equal(
            closure.has(resolve('src/v3_2/lf_workspace_proof.ts')),
            true
        );
        assert.equal(
            closure.has(resolve('src/v3_2/lf_workspace.ts')),
            true
        );
        assert.equal(
            closure.has(resolve('src/v3_2/proof_document.ts')),
            true
        );
        assert.equal(
            closure.has(resolve('src/v3_2/ai_proof_cli.ts')),
            false
        );
        assert.equal(
            closure.has(resolve('src/v3_2/lf_remote_workspace_store.ts')),
            false
        );
    });

    it('keeps exact same-module fragment workspaces Node-free', () => {
        const closure = collectLocalClosure(
            'src/v3_2/lf_fragment_workspace.ts'
        );
        assert.equal(
            closure.has(resolve('src/v3_2/lf_fragment_workspace.ts')),
            true
        );
        assert.equal(
            closure.has(resolve('src/v3_2/lf_transfer_mixed.ts')),
            true
        );
        assert.equal(
            closure.has(resolve('src/v3_2/lf_transfer_runtime.ts')),
            true
        );
        assert.equal(
            closure.has(resolve('src/v3_2/lf_transfer_proof.ts')),
            true
        );
        assert.equal(
            closure.has(resolve('src/v3_2/lf_transfer_acquisition.ts')),
            false
        );
        assert.equal(
            closure.has(resolve('src/v3_2/ai_proof_cli.ts')),
            false
        );
    });

    it('keeps exact cross-module fragment graphs Node-free', () => {
        const closure = collectLocalClosure(
            'src/v3_2/lf_fragment_module_workspace.ts'
        );
        assert.equal(
            closure.has(resolve(
                'src/v3_2/lf_fragment_module_workspace.ts'
            )),
            true
        );
        assert.equal(
            closure.has(resolve('src/v3_2/lf_fragment_workspace.ts')),
            true
        );
        assert.equal(
            closure.has(resolve('src/v3_2/lf_transfer_visibility.ts')),
            true
        );
        assert.equal(
            closure.has(resolve('src/v3_2/lf_transfer_acquisition.ts')),
            false
        );
        assert.equal(
            closure.has(resolve('src/v3_2/ai_proof_cli.ts')),
            false
        );
    });

    it('keeps remote lock reconstruction browser-safe and hashing outside', () => {
        const closure = collectLocalClosure(
            'src/v3_2/lf_remote_workspace_contract.ts'
        );
        assert.equal(
            closure.has(resolve(
                'src/v3_2/lf_remote_workspace_contract.ts'
            )),
            true
        );
        assert.equal(
            closure.has(resolve(
                'src/v3_2/lf_fragment_module_workspace.ts'
            )),
            true
        );
        assert.equal(
            closure.has(resolve('src/v3_2/lf_remote_workspace.ts')),
            false
        );
        assert.equal(
            closure.has(resolve('src/v3_2/lf_transfer_acquisition.ts')),
            false
        );
        assert.equal(
            closure.has(resolve('src/v3_2/ai_proof_cli.ts')),
            false
        );
    });

    it('targets a portable static project-subpath build', () => {
        const viteConfig = readFileSync(
            'emdash-template/vite.config.ts',
            'utf8'
        );
        const apiBridge = readFileSync(
            'emdash-template/src/emdash_api.ts',
            'utf8'
        );
        assert.match(viteConfig, /base:\s*['"]\.\/['"]/u);
        assert.match(
            apiBridge,
            /src\/v3_2\/browser_directed\.js/u
        );
        assert.equal(
            existsSync('emdash-template/public/index.html'),
            false
        );
    });
});
