/** Focused AGENT-EVAL-12B2 lazy browser-presentation and bundle gates. */

import assert from 'node:assert/strict';
import { existsSync, readFileSync, statSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { describe, it } from 'node:test';
import { gzipSync } from 'node:zlib';
import ts from 'typescript';

const repositoryRoot = resolve(__dirname, '..');
const browserDist = resolve(repositoryRoot, 'emdash-template/dist');
const corpusRevision = 'emdash-lf-proof-agent-public-corpus-v1';
const verifyBuiltBundle =
    process.env.EMDASH_VERIFY_PROOF_AGENT_BROWSER_BUILD === '1';

interface BuiltModuleReferences {
    readonly staticImports: readonly string[];
    readonly dynamicImports: readonly string[];
}

const builtModuleReferences = (
    file: string
): BuiltModuleReferences => {
    const source = readFileSync(file, 'utf8');
    const syntax = ts.createSourceFile(
        file,
        source,
        ts.ScriptTarget.Latest,
        true,
        ts.ScriptKind.JS
    );
    const staticImports: string[] = [];
    const dynamicImports: string[] = [];
    const visit = (node: ts.Node): void => {
        if (
            ts.isImportDeclaration(node) &&
            ts.isStringLiteral(node.moduleSpecifier)
        ) {
            staticImports.push(node.moduleSpecifier.text);
        } else if (
            ts.isCallExpression(node) &&
            node.expression.kind === ts.SyntaxKind.ImportKeyword &&
            node.arguments.length === 1 &&
            ts.isStringLiteral(node.arguments[0])
        ) {
            dynamicImports.push(node.arguments[0].text);
        }
        ts.forEachChild(node, visit);
    };
    visit(syntax);
    return { staticImports, dynamicImports };
};

const resolveBuiltImport = (
    importingFile: string,
    specifier: string
): string => {
    assert.equal(
        specifier.startsWith('.'),
        true,
        `Built browser module retained bare import ${specifier}`
    );
    const file = resolve(dirname(importingFile), specifier);
    assert.equal(
        file.startsWith(`${browserDist}/`),
        true,
        `Built browser import escaped dist: ${specifier}`
    );
    assert.equal(existsSync(file), true, `Missing built import ${file}`);
    return file;
};

const collectStaticBuiltClosure = (
    roots: readonly string[]
): ReadonlySet<string> => {
    const pending = [...roots];
    const closure = new Set<string>();
    while (pending.length > 0) {
        const file = pending.pop() as string;
        if (closure.has(file)) continue;
        closure.add(file);
        for (const specifier of builtModuleReferences(file).staticImports) {
            pending.push(resolveBuiltImport(file, specifier));
        }
    }
    return closure;
};

const closureContains = (
    closure: ReadonlySet<string>,
    pattern: string
): boolean => [...closure].some(file =>
    readFileSync(file, 'utf8').includes(pattern)
);

const closureBytes = (
    closure: ReadonlySet<string>
): { readonly raw: number; readonly gzip: number } => {
    let raw = 0;
    let gzip = 0;
    for (const file of closure) {
        const bytes = readFileSync(file);
        raw += statSync(file).size;
        gzip += gzipSync(bytes).byteLength;
    }
    return { raw, gzip };
};

describe('AGENT-EVAL-12B2 browser presentation', () => {
    it('keeps page load inert and exposes one explicit lazy action', () => {
        const bridge = readFileSync(resolve(
            repositoryRoot,
            'emdash-template/src/emdash_api.ts'
        ), 'utf8');
        const app = readFileSync(resolve(
            repositoryRoot,
            'emdash-template/src/App.tsx'
        ), 'utf8');
        assert.match(
            bridge,
            /loadCoreProofAgentBenchmark[\s\S]*import\([\s\S]*lf_proof_agent_public_corpus\.js/u
        );
        assert.doesNotMatch(
            bridge,
            /export \* from ['"][^'"]*lf_proof_agent_public_corpus/u
        );
        const actionStart = app.indexOf('const runProofAgentBenchmark');
        const loaderCall = app.indexOf('loadCoreProofAgentBenchmark()');
        assert.notEqual(actionStart, -1);
        assert.equal(loaderCall > actionStart, true);
        assert.equal(
            (app.match(/loadCoreProofAgentBenchmark\(\)/gu) ?? []).length,
            1
        );
        assert.doesNotMatch(
            app.slice(0, actionStart),
            /createCoreLfProofAgentPublicCorpus\(\)/u
        );
        assert.doesNotMatch(
            app,
            /serializeCoreLfProofAgentPublicCorpus|setBenchmark\(corpus\)/u
        );
    });

    it('states the exact compact evidence and non-authority boundary', () => {
        const app = readFileSync(resolve(
            repositoryRoot,
            'emdash-template/src/App.tsx'
        ), 'utf8');
        for (const required of [
            'Load reference benchmark',
            'freshly replayed baseline',
            'not proof authority',
            'leaderboard',
            'model-performance claim',
            'No provider or',
            'model runs in this browser',
            'benchmark.entries.map',
            'entry.sourceOwner',
            'entry.referenceOwner',
            "entry.features.join(' · ')",
            'benchmark.outcomes.acceptedComplete',
            'benchmark.outcomes.abstained',
            'retains only the compact'
        ]) {
            assert.match(app, new RegExp(required.replace(
                /[.*+?^${}()|[\]\\]/gu,
                '\\$&'
            ), 'u'));
        }
    });

    it('enforces complete initial and lazy Vite closure budgets', {
        skip: !verifyBuiltBundle
    }, () => {
        assert.equal(
            existsSync(resolve(browserDist, 'index.html')),
            true,
            'Run the direct emdash-template Vite build before this gate'
        );
        const html = readFileSync(resolve(browserDist, 'index.html'), 'utf8');
        const initialRoots = [...html.matchAll(
            /<script\b[^>]*\bsrc="([^"]+\.js)"[^>]*>/gu
        )].map(match => resolve(browserDist, match[1]));
        assert.equal(initialRoots.length > 0, true);
        initialRoots.forEach(file => assert.equal(existsSync(file), true));

        const initialClosure = collectStaticBuiltClosure(initialRoots);
        assert.equal(closureContains(initialClosure, corpusRevision), false);
        const initialSize = closureBytes(initialClosure);
        assert.equal(
            initialSize.raw <= 465000,
            true,
            `Initial closure is ${initialSize.raw} bytes (cap 465000)`
        );
        assert.equal(
            initialSize.gzip <= 130000,
            true,
            `Initial closure is ${initialSize.gzip} gzip bytes (cap 130000)`
        );

        const dynamicTargets = new Set<string>();
        for (const file of initialClosure) {
            for (const specifier of builtModuleReferences(file).dynamicImports) {
                dynamicTargets.add(resolveBuiltImport(file, specifier));
            }
        }
        const benchmarkClosures = [...dynamicTargets]
            .map(target => collectStaticBuiltClosure([target]))
            .filter(closure => closureContains(closure, corpusRevision));
        assert.equal(
            benchmarkClosures.length,
            1,
            'Expected one explicit lazy benchmark closure'
        );
        const incrementalBenchmarkClosure = new Set(
            [...benchmarkClosures[0]].filter(file =>
                !initialClosure.has(file)
            )
        );
        assert.equal(
            closureContains(incrementalBenchmarkClosure, corpusRevision),
            true
        );
        const benchmarkSize = closureBytes(incrementalBenchmarkClosure);
        assert.equal(
            benchmarkSize.raw <= 650000,
            true,
            `Benchmark closure is ${benchmarkSize.raw} bytes (cap 650000)`
        );
        assert.equal(
            benchmarkSize.gzip <= 175000,
            true,
            `Benchmark closure is ${benchmarkSize.gzip} gzip bytes (cap 175000)`
        );
    });
});
