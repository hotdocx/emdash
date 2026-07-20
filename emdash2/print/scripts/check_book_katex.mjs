import { execFileSync } from 'node:child_process';
import path from 'node:path';
import process from 'node:process';
import katex from 'katex';
import { REPO_ROOT } from './book_manifest.mjs';

function loadTypographyInventory() {
  const checker = path.join(REPO_ROOT, 'scripts', 'check_book_typography.py');
  const output = execFileSync('python3', [checker, '--math-json'], {
    cwd: REPO_ROOT,
    encoding: 'utf8',
    maxBuffer: 32 * 1024 * 1024,
  });
  return JSON.parse(output);
}

function main() {
  const inventory = loadTypographyInventory();
  const issues = [...inventory.issues.map((item) =>
    item.file + ':' + item.line + ': ' + item.kind + ': ' + item.message
  )];

  for (const span of inventory.math) {
    try {
      katex.renderToString(span.latex, {
        displayMode: span.display,
        output: 'htmlAndMathml',
        strict: 'error',
        throwOnError: true,
        trust: false,
      });
    } catch (error) {
      issues.push(
        span.file + ':' + span.line + ': KaTeX strict parse failed: ' +
        (error?.message || String(error))
      );
    }
  }

  if (issues.length > 0) {
    for (const issue of issues) console.error(issue);
    process.exitCode = 1;
    return;
  }
  console.log(
    'book KaTeX check passed: ' + inventory.sourceCount + ' source file(s), ' +
    inventory.math.length + ' math span(s)'
  );
}

try {
  main();
} catch (error) {
  console.error('book KaTeX check failed: ' + (error?.message || error));
  process.exitCode = 1;
}
