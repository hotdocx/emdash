/** Browser-panel and dependency-closure checks for PathOut presentation 1F. */

import assert from 'node:assert/strict';
import { builtinModules } from 'node:module';
import { existsSync, readFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { describe, it } from 'node:test';
import ts from 'typescript';
import {
    CORE_PATHOUT_PRESENTATION_1F_MANIFEST,
    createCorePathoutQualificationReport,
    parseCorePathoutPresentationText
} from '../src/v3_2/pathout_presentation';

const repositoryRoot = resolve(__dirname, '..');
const nodeBuiltins = new Set(
    builtinModules.map(name => name.replace(/^node:/u, '').split('/')[0])
);

const moduleSpecifiers = (
    file: string,
    source: string
): readonly string[] => {
    const syntax = ts.createSourceFile(
        file,
        source,
        ts.ScriptTarget.Latest,
        true,
        file.endsWith('.tsx') ? ts.ScriptKind.TSX : ts.ScriptKind.TS
    );
    const specifiers: string[] = [];
    const visit = (node: ts.Node): void => {
        if (
            ts.isImportDeclaration(node) &&
            ts.isStringLiteral(node.moduleSpecifier)
        ) {
            specifiers.push(node.moduleSpecifier.text);
        } else if (
            ts.isExportDeclaration(node) &&
            node.moduleSpecifier !== undefined &&
            ts.isStringLiteral(node.moduleSpecifier)
        ) {
            specifiers.push(node.moduleSpecifier.text);
        } else if (
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
    const withoutJs = specifier.endsWith('.js')
        ? unresolved.slice(0, -3)
        : unresolved;
    const candidates = [
        withoutJs,
        `${withoutJs}.ts`,
        `${withoutJs}.tsx`,
        resolve(withoutJs, 'index.ts')
    ];
    const resolved = candidates.find(candidate => existsSync(candidate));
    assert.notEqual(
        resolved,
        undefined,
        `Cannot resolve PathOut browser dependency ${specifier} from ` +
            importingFile
    );
    return resolved as string;
};

const collectLocalClosure = (entry: string): ReadonlySet<string> => {
    const pending = [resolve(repositoryRoot, entry)];
    const visited = new Set<string>();
    while (pending.length > 0) {
        const file = pending.pop() as string;
        if (visited.has(file)) continue;
        visited.add(file);
        const source = readFileSync(file, 'utf8');
        for (const specifier of moduleSpecifiers(file, source)) {
            if (specifier.startsWith('.')) {
                pending.push(resolveLocalModule(file, specifier));
                continue;
            }
            const bare = specifier.startsWith('node:')
                ? specifier.slice('node:'.length).split('/')[0]
                : specifier.split('/')[0];
            assert.equal(
                specifier.startsWith('node:') || nodeBuiltins.has(bare),
                false,
                `PathOut browser closure reaches Node builtin ${specifier}`
            );
        }
    }
    return visited;
};

describe('PATHOUT-LIBRARY-PRESENTATION-1F browser integration', () => {
    it('presents all four forms only as pinned, non-fresh evidence', () => {
        for (const form of CORE_PATHOUT_PRESENTATION_1F_MANIFEST.forms) {
            const request = parseCorePathoutPresentationText(
                form.canonicalSource,
                'browser-pathout.emdash'
            );
            const report = createCorePathoutQualificationReport(request);
            assert.equal(report.request.formId, form.id);
            assert.equal(report.status, 'qualified-at-pinned-checkpoint');
            assert.equal(report.freshSemanticCheck, false);
            assert.equal(report.browserSemanticExecution, false);
        }
    });

    it('keeps the lazy browser closure finite and transfer-free', () => {
        const closure = collectLocalClosure(
            'src/v3_2/pathout_presentation.ts'
        );
        assert.deepEqual(
            [...closure],
            [resolve(repositoryRoot, 'src/v3_2/pathout_presentation.ts')]
        );
        for (const forbidden of [
            'src/v3_2/pathout_presentation_check.ts',
            'src/v3_2/pathout_foundation_transfer.ts',
            'src/v3_2/pathind_fixed_source_transfer.ts',
            'src/v3_2/pathout_transitivity_transfer.ts'
        ]) {
            assert.equal(
                closure.has(resolve(repositoryRoot, forbidden)),
                false,
                forbidden
            );
        }
    });

    it('wires one lazy static panel without a browser check action', () => {
        const bridge = readFileSync(
            resolve(repositoryRoot, 'emdash-template/src/emdash_api.ts'),
            'utf8'
        );
        const app = readFileSync(
            resolve(repositoryRoot, 'emdash-template/src/App.tsx'),
            'utf8'
        );
        assert.match(
            bridge,
            /loadCorePathoutPresentation[\s\S]*import\([\s\S]*pathout_presentation\.js/u
        );
        assert.doesNotMatch(bridge, /pathout_presentation_check/u);
        assert.match(app, /PathOut and arrow induction/u);
        assert.match(app, /not a browser check/u);
        assert.match(app, /does not assemble the semantic transfer/u);
        assert.match(app, /Show pinned qualification/u);
        assert.match(app, /pathout-output/u);
        assert.doesNotMatch(app, /checkCorePathoutPresentationRequest/u);
        assert.doesNotMatch(app, /loadSemanticCheck/u);
    });
});
