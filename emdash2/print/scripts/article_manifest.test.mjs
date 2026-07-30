import assert from 'node:assert/strict';
import fs from 'node:fs';
import test from 'node:test';

import {
  ARTICLE_MANIFEST_PATH,
  loadArticleManifest,
  validateArticleManifest,
} from './article_manifest.mjs';
import { loadDocumentRegistry } from './document_registry.mjs';

function fixture() {
  return JSON.parse(fs.readFileSync(ARTICLE_MANIFEST_PATH, 'utf8'));
}

test('the live article manifest resolves one active authored overview', () => {
  const manifest = loadArticleManifest();
  assert.equal(manifest.articles.length, 1);
  assert.equal(manifest.articles[0].document.id, 'index-3-2');
  assert.match(manifest.articles[0].artifactPath, /emdash2\/output\/pdf\/.+\.pdf$/);
});

test('an article cannot escape the generated PDF directory', () => {
  const manifest = fixture();
  manifest.articles[0].artifact = 'docs/not-an-intermediate.pdf';
  assert.throws(
    () => validateArticleManifest(manifest, { registry: loadDocumentRegistry() }),
    /artifact must be a PDF strictly under emdash2\/output\/pdf/
  );
});

test('article distribution paths are restricted to docs', () => {
  const manifest = fixture();
  manifest.articles[0].distribution.markdown = 'README.md';
  assert.throws(
    () => validateArticleManifest(manifest, { registry: loadDocumentRegistry() }),
    /distribution\.markdown must be a \.md file directly under docs/
  );
});

test('the page budget is ordered', () => {
  const manifest = fixture();
  manifest.articles[0].pageBudget.minimum = 17;
  manifest.articles[0].pageBudget.maximum = 15;
  assert.throws(
    () => validateArticleManifest(manifest, { registry: loadDocumentRegistry() }),
    /minimum <= target <= maximum/
  );
});
