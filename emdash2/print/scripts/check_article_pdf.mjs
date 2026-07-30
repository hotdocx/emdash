import { execFileSync } from 'node:child_process';
import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { PDFDocument, PDFName } from 'pdf-lib';

import { GIT_ROOT, selectArticle } from './article_manifest.mjs';

const PIPELINE_NAME = 'emdash deterministic article pipeline';
const ARTICLE_ID = process.argv[2] || 'emdash-v3-2-overview';
const LETTER_WIDTH_POINTS = 612;
const LETTER_HEIGHT_POINTS = 792;

function fail(message) {
  throw new Error(message);
}

function run(command, args) {
  return execFileSync(command, args, {
    encoding: 'utf8',
    maxBuffer: 64 * 1024 * 1024,
  });
}

function normalizeText(text) {
  return text.replace(/\s+/g, ' ').trim();
}

function checkFonts(pdfPath) {
  const output = run('pdffonts', [pdfPath]);
  const lines = output.split(/\r?\n/).filter((line) =>
    line.trim() !== '' &&
    !/^name\s+/i.test(line) &&
    !/^-{3,}/.test(line)
  );
  if (lines.length === 0) fail('pdffonts found no fonts');
  for (const line of lines) {
    const flags = line.match(/\s+(yes|no)\s+(yes|no)\s+(yes|no)\s+\d+\s+\d+\s*$/i);
    if (!flags) fail('could not parse pdffonts row: ' + line);
    if (flags[1].toLowerCase() !== 'yes') {
      fail('PDF font is not embedded: ' + line);
    }
  }
  return lines.length;
}

async function main() {
  if (process.argv.length > 3) {
    fail('usage: check_article_pdf.mjs [article-id]');
  }
  const article = selectArticle(ARTICLE_ID);
  const pdfPath = article.artifactPath;
  if (!fs.existsSync(pdfPath) || fs.statSync(pdfPath).size < 100000) {
    fail('PDF is missing or unexpectedly small: ' + path.relative(GIT_ROOT, pdfPath));
  }

  run('qpdf', ['--check', pdfPath]);
  const pdf = await PDFDocument.load(fs.readFileSync(pdfPath), {
    updateMetadata: false,
  });
  const expectedDate = new Date(article.publicationDate + 'T00:00:00.000Z');
  const expectedSubject =
    article.edition + '; version ' + article.editionVersion +
    '; status ' + article.status;
  for (const [name, actual, expected] of [
    ['title', pdf.getTitle(), article.displayTitle],
    ['author', pdf.getAuthor(), article.authors.join(', ')],
    ['subject', pdf.getSubject(), expectedSubject],
    ['creator', pdf.getCreator(), PIPELINE_NAME],
    ['producer', pdf.getProducer(), PIPELINE_NAME],
  ]) {
    if (actual !== expected) {
      fail(
        'PDF ' + name + ' differs: expected ' +
        JSON.stringify(expected) + ', got ' + JSON.stringify(actual)
      );
    }
  }
  for (const [name, actual] of [
    ['creation date', pdf.getCreationDate()],
    ['modification date', pdf.getModificationDate()],
  ]) {
    if (!(actual instanceof Date) || actual.getTime() !== expectedDate.getTime()) {
      fail('PDF ' + name + ' is not the fixed publication date');
    }
  }

  const pageCount = pdf.getPageCount();
  if (
    pageCount < article.pageBudget.minimum ||
    pageCount > article.pageBudget.maximum
  ) {
    fail(
      'PDF page count ' + pageCount + ' is outside ' +
      article.pageBudget.minimum + '-' + article.pageBudget.maximum
    );
  }
  for (const [index, page] of pdf.getPages().entries()) {
    const size = page.getSize();
    if (
      Math.abs(size.width - LETTER_WIDTH_POINTS) > 1 ||
      Math.abs(size.height - LETTER_HEIGHT_POINTS) > 1
    ) {
      fail(
        'PDF page ' + (index + 1) + ' is not US Letter: ' +
        size.width.toFixed(2) + ' x ' + size.height.toFixed(2) + ' pt'
      );
    }
  }
  for (const catalogEntry of ['Outlines', 'StructTreeRoot']) {
    if (!pdf.catalog.has(PDFName.of(catalogEntry))) {
      fail('PDF catalog is missing ' + catalogEntry);
    }
  }

  const info = run('pdfinfo', [pdfPath]);
  const infoPages = Number(info.match(/^Pages:\s+(\d+)$/m)?.[1]);
  if (infoPages !== pageCount) {
    fail('pdfinfo page count differs from pdf-lib: ' + infoPages + ' vs ' + pageCount);
  }
  for (const [field, expected] of [
    ['Tagged', 'yes'],
    ['Suspects', 'no'],
    ['Encrypted', 'no'],
    ['JavaScript', 'no'],
  ]) {
    const actual = info.match(new RegExp('^' + field + ':\\s+(\\S+)$', 'm'))?.[1];
    if (actual !== expected) {
      fail('pdfinfo ' + field + ' differs: expected ' + expected + ', got ' + actual);
    }
  }

  const extracted = run('pdftotext', ['-enc', 'UTF-8', pdfPath, '-']);
  const normalized = normalizeText(extracted);
  for (const required of article.requiredText) {
    if (!normalized.includes(required)) {
      fail('PDF text is missing required phrase: ' + JSON.stringify(required));
    }
  }
  if (extracted.includes('\uFFFD')) {
    fail('PDF text contains the Unicode replacement character');
  }
  for (const forbidden of [
    'Diagram Error',
    'Chart Error',
    'Could not load',
    'katex-error',
    'arrowgram-error',
  ]) {
    if (normalized.includes(forbidden)) {
      fail('PDF contains render failure text: ' + forbidden);
    }
  }
  const literalTex = extracted.match(
    /\\(?:to|circ|mathsf|operatorname|mathrm|qquad|quad|longrightarrow)\b/
  );
  if (literalTex) {
    fail('PDF text contains a literal TeX command: ' + JSON.stringify(literalTex[0]));
  }

  const textPages = extracted.split('\f');
  if (textPages.at(-1)?.trim() === '') textPages.pop();
  if (textPages.length !== pageCount) {
    fail(
      'pdftotext page count differs from PDF page count: ' +
      textPages.length + ' vs ' + pageCount
    );
  }
  for (const [index, text] of textPages.entries()) {
    if (normalizeText(text).length < 10) {
      fail('PDF page ' + (index + 1) + ' is blank or nearly blank');
    }
  }

  const fontCount = checkFonts(pdfPath);
  const digest = crypto.createHash('sha256')
    .update(fs.readFileSync(pdfPath))
    .digest('hex');
  console.log(
    'article PDF check passed: ' + path.relative(GIT_ROOT, pdfPath) +
    ', pages=' + pageCount +
    ', target=' + article.pageBudget.target +
    ', embedded-fonts=' + fontCount +
    ', sha256=' + digest
  );
}

main().catch((error) => {
  console.error('article PDF check failed: ' + (error?.message || error));
  process.exitCode = 1;
});
