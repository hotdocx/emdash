import assert from 'node:assert/strict';
import fs from 'node:fs';
import test from 'node:test';

import {
  ARTICLE_MANIFEST_PATH,
  articlePageCountAllowed,
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
  assert.equal(manifest.articles[0].document.id, 'emdash-v3-2-overview');
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

test('an explicit null maximum permits a longer overview but keeps minimum and target', () => {
  const manifest = fixture();
  manifest.articles[0].pageBudget = { minimum: 14, target: 16, maximum: null };
  const budget = validateArticleManifest(manifest).articles[0].pageBudget;
  assert.equal(articlePageCountAllowed(19, budget), true);
  assert.equal(articlePageCountAllowed(40, budget), true);
  for (const count of [0, 13, 18.5, NaN, Infinity]) {
    assert.equal(articlePageCountAllowed(count, budget), false);
  }
});

test('a numeric maximum still constrains other bounded article profiles', () => {
  const manifest = fixture();
  manifest.articles[0].pageBudget = { minimum: 14, target: 16, maximum: 18 };
  const budget = validateArticleManifest(manifest).articles[0].pageBudget;
  assert.equal(articlePageCountAllowed(18, budget), true);
  assert.equal(articlePageCountAllowed(19, budget), false);
});

test('uncapped budgets still reject reversed lower bounds and malformed maxima', () => {
  const reversed = fixture();
  reversed.articles[0].pageBudget = { minimum: 17, target: 16, maximum: null };
  assert.throws(() => validateArticleManifest(reversed), /minimum <= target/);
  for (const maximum of [undefined, 0, -1, 18.5, 'none', Infinity]) {
    const manifest = fixture();
    manifest.articles[0].pageBudget.maximum = maximum;
    assert.throws(() => validateArticleManifest(manifest), /positive integer or null/);
  }
});
