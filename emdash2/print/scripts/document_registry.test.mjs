import assert from 'node:assert/strict';
import fs from 'node:fs';
import test from 'node:test';

import {
  loadDocumentRegistry,
  validateDocumentRegistry,
} from './document_registry.mjs';

const registryUrl = new URL('../documents.json', import.meta.url);

function registryFixture() {
  return JSON.parse(fs.readFileSync(registryUrl, 'utf8'));
}

const everyAuthorityExists = () => true;

test('the live registry has explicit valid authorities and lifecycles', () => {
  const registry = loadDocumentRegistry();
  assert.equal(registry.version, 2);
  assert.ok(registry.documents.some((document) =>
    document.kind === 'article' && document.lifecycle === 'active-workbench'
  ));
});

test('an authored document owns its exact public Markdown source', () => {
  const registry = registryFixture();
  const article = registry.documents.find((document) => document.kind === 'article');
  article.source.authority = 'print/public/not-the-article.md';
  assert.throws(
    () => validateDocumentRegistry(registry, { authorityExists: everyAuthorityExists }),
    /authored document authority must be print\/public\/emdash-v3-2-overview\.md/
  );
});

test('a generated document cannot claim its generated output as authority', () => {
  const registry = registryFixture();
  const book = registry.documents.find((document) => document.kind === 'book');
  book.source.authority = 'print/public/emdash-book.md';
  assert.throws(
    () => validateDocumentRegistry(registry, { authorityExists: everyAuthorityExists }),
    /generated document authority must be outside its generated output/
  );
});

test('every declared authority must exist', () => {
  const registry = registryFixture();
  assert.throws(
    () => validateDocumentRegistry(registry, { authorityExists: () => false }),
    /source\.authority does not exist/
  );
});

test('the registry retains an explicit active article workbench', () => {
  const registry = registryFixture();
  for (const document of registry.documents) {
    if (document.kind === 'article') document.lifecycle = 'archival';
  }
  assert.throws(
    () => validateDocumentRegistry(registry, { authorityExists: everyAuthorityExists }),
    /at least one article must be an active workbench/
  );
});
