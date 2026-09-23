import { readdirSync, readFileSync, existsSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import ts from 'typescript';

export function testRegistration(root) {
  const testsRoot = path.resolve(root, 'tests');
  const visited = new Set();
  const pending = [path.join(testsRoot, 'main_tests.ts')];
  while (pending.length) {
    const file = pending.pop();
    if (visited.has(file)) continue;
    visited.add(file);
    const source = ts.createSourceFile(file, readFileSync(file, 'utf8'), ts.ScriptTarget.Latest);
    for (const node of source.statements) {
      if (!ts.isImportDeclaration(node) || node.importClause?.isTypeOnly) continue;
      if (node.importClause?.namedBindings && ts.isNamedImports(node.importClause.namedBindings)
          && !node.importClause.name && node.importClause.namedBindings.elements.length
          && node.importClause.namedBindings.elements.every((item) => item.isTypeOnly)) continue;
      const name = node.moduleSpecifier.text;
      if (!name.startsWith('.')) continue;
      const stem = path.resolve(path.dirname(file), name.replace(/\.(?:js|ts)$/, ''));
      const target = [stem + '.ts', path.join(stem, 'index.ts')].find(existsSync);
      if (target && target.startsWith(testsRoot + path.sep)) pending.push(target);
    }
  }
  const expected = readdirSync(testsRoot).filter((name) => name.endsWith('_tests.ts'));
  return {
    total: expected.length - 1,
    missing: expected.filter((name) => !visited.has(path.join(testsRoot, name))),
  };
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const result = testRegistration(fileURLToPath(new URL('../', import.meta.url)));
  if (result.missing.length) {
    console.error('Test files unreachable from tests/main_tests.ts:\n' + result.missing.join('\n'));
    process.exitCode = 1;
  } else {
    console.log(`Test registration passed: ${result.total} suites reachable, including transitive imports.`);
  }
}
