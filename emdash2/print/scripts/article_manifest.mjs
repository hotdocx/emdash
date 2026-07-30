import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import { loadDocumentRegistry } from './document_registry.mjs';

export const GIT_ROOT = fileURLToPath(new URL('../../../', import.meta.url));
export const ARTICLE_MANIFEST_PATH = fileURLToPath(
  new URL('../articles.json', import.meta.url)
);

const SAFE_ID = /^[A-Za-z0-9][A-Za-z0-9-]*$/;
const SAFE_REPO_PATH = /^[A-Za-z0-9][A-Za-z0-9_./-]*$/;

function fail(context, message) {
  throw new Error(context + ': ' + message);
}

function readJson() {
  try {
    return JSON.parse(fs.readFileSync(ARTICLE_MANIFEST_PATH, 'utf8'));
  } catch (error) {
    fail('print/articles.json', error.message);
  }
}

export function resolveGitPath(raw, context, { mustExist = true } = {}) {
  if (
    typeof raw !== 'string' ||
    !SAFE_REPO_PATH.test(raw) ||
    raw.startsWith('/') ||
    raw.split('/').includes('..')
  ) {
    fail(context, 'expected a safe repository-relative path');
  }
  const resolved = path.resolve(GIT_ROOT, raw);
  const relative = path.relative(GIT_ROOT, resolved);
  if (
    relative === '' ||
    relative === '..' ||
    relative.startsWith('..' + path.sep) ||
    path.isAbsolute(relative)
  ) {
    fail(context, 'path escapes or names the repository root');
  }
  if (mustExist) {
    if (!fs.existsSync(resolved)) fail(context, 'file does not exist: ' + raw);
    if (!fs.statSync(resolved).isFile()) fail(context, 'expected a file: ' + raw);
  }
  return resolved;
}

export function validateArticleManifest(
  manifest,
  { registry = loadDocumentRegistry() } = {}
) {
  if (!manifest || manifest.version !== 1 || !Array.isArray(manifest.articles)) {
    fail('print/articles.json', 'expected version 1 and an articles array');
  }
  if (manifest.articles.length === 0) {
    fail('print/articles.json', 'articles must not be empty');
  }

  const ids = new Set();
  const documentIds = new Set();
  const artifacts = new Set();
  const distributions = new Set();

  for (const [index, article] of manifest.articles.entries()) {
    const context = 'print/articles.json:articles[' + index + ']';
    if (!article || typeof article !== 'object' || Array.isArray(article)) {
      fail(context, 'article must be an object');
    }
    if (typeof article.id !== 'string' || !SAFE_ID.test(article.id)) {
      fail(context, 'id must be an ASCII identifier');
    }
    if (ids.has(article.id)) fail(context, 'duplicate id ' + article.id);
    ids.add(article.id);

    if (typeof article.documentId !== 'string' || !SAFE_ID.test(article.documentId)) {
      fail(context, 'documentId must be an ASCII identifier');
    }
    if (documentIds.has(article.documentId)) {
      fail(context, 'documentId is already published: ' + article.documentId);
    }
    documentIds.add(article.documentId);
    const document = registry.documents.find(
      (candidate) => candidate.id === article.documentId
    );
    if (
      !document ||
      document.kind !== 'article' ||
      document.source.mode !== 'authored' ||
      document.lifecycle !== 'active-workbench'
    ) {
      fail(context, 'documentId must select an active authored article');
    }
    article.document = document;
    article.sourcePath = resolveGitPath(
      path.posix.join('emdash2', document.source.authority),
      context + '.source'
    );

    for (const field of ['displayTitle', 'edition', 'editionVersion', 'publicationDate', 'status']) {
      if (typeof article[field] !== 'string' || article[field].trim() === '') {
        fail(context, field + ' must be a non-empty string');
      }
    }
    if (!/^\d+\.\d+\.\d+(?:-[A-Za-z0-9.-]+)?$/.test(article.editionVersion)) {
      fail(context, 'editionVersion must be a version identifier');
    }
    if (!/^\d{4}-\d{2}-\d{2}$/.test(article.publicationDate)) {
      fail(context, 'publicationDate must be YYYY-MM-DD');
    }
    for (const field of ['authors', 'keywords', 'requiredText']) {
      if (
        !Array.isArray(article[field]) ||
        article[field].length === 0 ||
        !article[field].every(
          (entry) => typeof entry === 'string' && entry.trim() !== ''
        )
      ) {
        fail(context, field + ' must be a non-empty array of strings');
      }
    }

    article.artifactPath = resolveGitPath(
      article.artifact,
      context + '.artifact',
      { mustExist: false }
    );
    const artifactRelative = path.relative(
      path.join(GIT_ROOT, 'emdash2', 'output', 'pdf'),
      article.artifactPath
    );
    if (
      artifactRelative === '' ||
      artifactRelative === '..' ||
      artifactRelative.startsWith('..' + path.sep) ||
      path.isAbsolute(artifactRelative) ||
      path.extname(article.artifactPath).toLowerCase() !== '.pdf'
    ) {
      fail(context, 'artifact must be a PDF strictly under emdash2/output/pdf');
    }
    if (artifacts.has(article.artifactPath)) fail(context, 'duplicate artifact path');
    artifacts.add(article.artifactPath);

    if (
      !article.distribution ||
      typeof article.distribution !== 'object' ||
      Array.isArray(article.distribution)
    ) {
      fail(context, 'distribution must be an object');
    }
    article.distributionPaths = {};
    for (const [kind, extension] of [['markdown', '.md'], ['pdf', '.pdf']]) {
      const raw = article.distribution[kind];
      const resolved = resolveGitPath(raw, context + '.distribution.' + kind, {
        mustExist: false,
      });
      if (
        path.dirname(resolved) !== path.join(GIT_ROOT, 'docs') ||
        path.extname(resolved).toLowerCase() !== extension
      ) {
        fail(
          context,
          'distribution.' + kind + ' must be a ' + extension + ' file directly under docs'
        );
      }
      if (distributions.has(resolved)) fail(context, 'duplicate distribution path');
      distributions.add(resolved);
      article.distributionPaths[kind] = resolved;
    }

    const budget = article.pageBudget;
    if (!budget || typeof budget !== 'object' || Array.isArray(budget)) {
      fail(context, 'pageBudget must be an object');
    }
    for (const field of ['minimum', 'target', 'maximum']) {
      if (!Number.isSafeInteger(budget[field]) || budget[field] < 1) {
        fail(context, 'pageBudget.' + field + ' must be a positive integer');
      }
    }
    if (!(budget.minimum <= budget.target && budget.target <= budget.maximum)) {
      fail(context, 'pageBudget must satisfy minimum <= target <= maximum');
    }
  }

  return manifest;
}

export function loadArticleManifest() {
  return validateArticleManifest(readJson());
}

export function selectArticle(id) {
  const manifest = loadArticleManifest();
  const article = manifest.articles.find((candidate) => candidate.id === id);
  if (!article) fail('article selection', 'unknown article ' + JSON.stringify(id));
  return article;
}
