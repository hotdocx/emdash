import { execFileSync } from 'node:child_process';
import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { chromium } from 'playwright';
import {
  PDFArray,
  PDFDict,
  PDFDocument,
  PDFHexString,
  PDFName,
  PDFStream,
  PDFString,
} from 'pdf-lib';

import { GIT_ROOT, selectArticle } from './article_manifest.mjs';
import { documentQuery } from './document_registry.mjs';
import {
  startPreviewServer,
  waitForCompletedPagination,
  withTimeout,
} from './preview_runtime.mjs';

const PIPELINE_NAME = 'emdash deterministic article pipeline';
const ARTICLE_ID = process.argv[2] || 'emdash-v3-2-overview';
const PRINT_PAGE_CSS = `
  @page { size: 8.5in 11in; margin: 0; }
  html, body { margin: 0 !important; padding: 0 !important; }
  .preview-controls, .loading-indicator { display: none !important; }
  .preview-content-area { padding: 0 !important; }
  .pagedjs_pages {
    display: block !important;
    margin: 0 !important;
    padding: 0 !important;
    background: white !important;
  }
  .pagedjs_page {
    width: 8.5in !important;
    height: 11in !important;
    margin: 0 !important;
    box-shadow: none !important;
    overflow: hidden !important;
    break-after: page !important;
    page-break-after: always !important;
  }
  .pagedjs_page:last-child,
  .pagedjs_page:last-of-type {
    break-after: auto !important;
    page-break-after: auto !important;
  }
`;

function sha256(filePath) {
  return crypto.createHash('sha256').update(fs.readFileSync(filePath)).digest('hex');
}

function canonicalizeStructureNodeIds(pdf) {
  const pattern = /^node\d{8}$/;
  const identifiers = new Set();

  const visit = (object, seen, replace) => {
    if (!object || seen.has(object)) return;
    if (typeof object === 'object') seen.add(object);
    if (object instanceof PDFString || object instanceof PDFHexString) {
      const identifier = object.decodeText();
      if (!pattern.test(identifier)) return;
      identifiers.add(identifier);
      if (replace) return replace(identifier, object);
      return;
    }
    if (object instanceof PDFArray) {
      for (let index = 0; index < object.size(); index += 1) {
        const replacement = visit(object.get(index), seen, replace);
        if (replacement) object.set(index, replacement);
      }
      return;
    }
    if (object instanceof PDFDict) {
      for (const [key, value] of object.entries()) {
        const replacement = visit(value, seen, replace);
        if (replacement) object.set(key, replacement);
      }
      return;
    }
    if (object instanceof PDFStream) visit(object.dict, seen, replace);
  };

  for (const [, object] of pdf.context.enumerateIndirectObjects()) {
    visit(object, new Set(), null);
  }
  const ordered = [...identifiers].sort(
    (left, right) => Number(left.slice(4)) - Number(right.slice(4))
  );
  const canonical = new Map(
    ordered.map((identifier, index) => [
      identifier,
      'node' + String(index + 1).padStart(8, '0'),
    ])
  );
  const replace = (identifier, original) => {
    const normalized = canonical.get(identifier);
    return original instanceof PDFHexString
      ? PDFHexString.fromText(normalized)
      : PDFString.of(normalized);
  };
  for (const [reference, object] of pdf.context.enumerateIndirectObjects()) {
    const replacement = visit(object, new Set(), replace);
    if (replacement) pdf.context.assign(reference, replacement);
  }
}

async function normalizePdfMetadata(rawPath, normalizedPath, article) {
  const pdf = await PDFDocument.load(fs.readFileSync(rawPath), {
    updateMetadata: false,
  });
  const publicationDate = new Date(article.publicationDate + 'T00:00:00.000Z');

  pdf.catalog.delete(PDFName.of('Metadata'));
  pdf.setTitle(article.displayTitle);
  pdf.setAuthor(article.authors.join(', '));
  pdf.setSubject(
    article.edition + '; version ' + article.editionVersion +
    '; status ' + article.status
  );
  pdf.setKeywords(article.keywords);
  pdf.setCreator(PIPELINE_NAME);
  pdf.setProducer(PIPELINE_NAME);
  pdf.setCreationDate(publicationDate);
  pdf.setModificationDate(publicationDate);

  canonicalizeStructureNodeIds(pdf);
  const bytes = await pdf.save({
    addDefaultPage: false,
    objectsPerTick: 100000,
    useObjectStreams: false,
  });
  fs.writeFileSync(normalizedPath, bytes);
}

async function main() {
  if (process.argv.length > 3) {
    throw new Error('usage: export_article_pdf.mjs [article-id]');
  }
  const article = selectArticle(ARTICLE_ID);
  const document = article.document;
  const temporaryDirectory = path.join(GIT_ROOT, 'emdash2', 'tmp', 'pdfs');
  const stem = article.id + '-' + process.pid;
  const rawPath = path.join(temporaryDirectory, stem + '.raw.pdf');
  const normalizedPath = path.join(temporaryDirectory, stem + '.normalized.pdf');
  const candidatePath = path.join(temporaryDirectory, stem + '.candidate.pdf');
  fs.mkdirSync(temporaryDirectory, { recursive: true });
  fs.mkdirSync(path.dirname(article.artifactPath), { recursive: true });

  let preview = null;
  let browser = null;
  let cleanupPromise = null;
  const cleanup = () => {
    if (!cleanupPromise) {
      cleanupPromise = (async () => {
        if (browser) {
          await browser.close().catch(() => {});
          browser = null;
        }
        if (preview) {
          await preview.stop().catch(() => {});
          preview = null;
        }
        for (const temporaryPath of [rawPath, normalizedPath, candidatePath]) {
          fs.rmSync(temporaryPath, { force: true });
        }
      })();
    }
    return cleanupPromise;
  };

  const onSignal = (signal, exitCode) => {
    void cleanup().finally(() => {
      console.error('Article PDF export interrupted by ' + signal);
      process.exit(exitCode);
    });
  };
  const onSigint = () => onSignal('SIGINT', 130);
  const onSigterm = () => onSignal('SIGTERM', 143);
  process.once('SIGINT', onSigint);
  process.once('SIGTERM', onSigterm);

  try {
    preview = await startPreviewServer();
    browser = await chromium.launch({ headless: true });
    const context = await browser.newContext({
      locale: 'en-US',
      timezoneId: 'UTC',
    });
    const page = await context.newPage();
    page.setDefaultTimeout(document.timeoutMs);
    page.setDefaultNavigationTimeout(document.timeoutMs);

    const failures = [];
    const localOrigin = new URL(preview.baseUrl).origin;
    page.on('pageerror', (error) => {
      failures.push('pageerror: ' + (error.message || String(error)));
    });
    page.on('console', (message) => {
      const text = message.text();
      if (message.type() === 'error') failures.push('console.error: ' + text);
      if (
        message.type() === 'warning' &&
        (text.includes('LaTeX-incompatible input') ||
          text.includes('[mathVsTextAccents]'))
      ) {
        failures.push('console.warn (KaTeX): ' + text);
      }
    });
    page.on('requestfailed', (request) => {
      failures.push(
        'requestfailed: ' + request.url() + ' ' +
        (request.failure()?.errorText || '')
      );
    });
    page.on('request', (request) => {
      const url = new URL(request.url());
      if (['data:', 'blob:', 'about:'].includes(url.protocol)) return;
      if (url.origin !== localOrigin) failures.push('external request: ' + request.url());
    });

    await page.goto(preview.baseUrl + documentQuery(document), {
      waitUntil: 'domcontentloaded',
    });
    const pageCount = await withTimeout(
      waitForCompletedPagination(page, document.timeoutMs),
      document.timeoutMs,
      document.file + ' PDF pagination'
    );
    const renderErrors = await page.locator(
      '.katex-error, .vega-error, .mermaid-error, .arrowgram-error'
    ).allTextContents();
    if (renderErrors.length > 0) {
      failures.push('rendered error box: ' + renderErrors.slice(0, 3).join(' / '));
    }
    if (
      pageCount < article.pageBudget.minimum ||
      pageCount > article.pageBudget.maximum
    ) {
      failures.push(
        'page count ' + pageCount + ' is outside article budget ' +
        article.pageBudget.minimum + '-' + article.pageBudget.maximum
      );
    }
    if (failures.length > 0) {
      throw new Error('Article PDF browser gate failed:\n- ' + failures.join('\n- '));
    }

    await page.emulateMedia({ media: 'print' });
    await page.addStyleTag({ content: PRINT_PAGE_CSS });
    await page.pdf({
      path: rawPath,
      width: '8.5in',
      height: '11in',
      margin: { top: '0', right: '0', bottom: '0', left: '0' },
      displayHeaderFooter: false,
      outline: true,
      preferCSSPageSize: true,
      printBackground: true,
      tagged: true,
    });

    await normalizePdfMetadata(rawPath, normalizedPath, article);
    execFileSync(
      'qpdf',
      [
        '--deterministic-id',
        '--object-streams=generate',
        '--recompress-flate',
        '--compression-level=9',
        normalizedPath,
        candidatePath,
      ],
      { stdio: 'inherit' }
    );
    fs.renameSync(candidatePath, article.artifactPath);
    console.log(
      'article PDF exported: ' +
      path.relative(GIT_ROOT, article.artifactPath) +
      ', pages=' + pageCount +
      ', target=' + article.pageBudget.target +
      ', sha256=' + sha256(article.artifactPath)
    );
  } finally {
    process.off('SIGINT', onSigint);
    process.off('SIGTERM', onSigterm);
    await cleanup();
  }
}

main().catch((error) => {
  console.error('article PDF export failed: ' + (error?.message || error));
  process.exitCode = 1;
});
