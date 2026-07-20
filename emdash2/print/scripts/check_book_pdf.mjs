import { execFileSync } from 'node:child_process';
import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { PDFDocument, PDFName } from 'pdf-lib';
import {
  REPO_ROOT,
  loadBookManifest,
  resolveRepoPath,
} from './book_manifest.mjs';

const PIPELINE_NAME = 'emdash deterministic book pipeline';
const LETTER_WIDTH_POINTS = 612;
const LETTER_HEIGHT_POINTS = 792;

function fail(message) {
  throw new Error(message);
}

function sha256(filePath) {
  return crypto.createHash('sha256').update(fs.readFileSync(filePath)).digest('hex');
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

function requireText(haystack, needle, context) {
  if (!haystack.includes(needle)) {
    fail('PDF text is missing ' + context + ': ' + JSON.stringify(needle));
  }
}

function checkFonts(pdfPath) {
  const output = run('pdffonts', [pdfPath]);
  const lines = output.split(/\r?\n/).filter((line) =>
    line.trim() !== '' && !/^name\s+/i.test(line) && !/^-{3,}/.test(line)
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
  const { manifest } = loadBookManifest();
  const pdfPath = resolveRepoPath(
    manifest.artifacts.pdf,
    'book/book.json:artifacts.pdf'
  );
  if (fs.statSync(pdfPath).size < 100000) {
    fail('PDF is unexpectedly small: ' + fs.statSync(pdfPath).size + ' bytes');
  }

  run('qpdf', ['--check', pdfPath]);
  const pdf = await PDFDocument.load(fs.readFileSync(pdfPath), {
    updateMetadata: false,
  });
  const expectedDate = new Date(manifest.publicationDate + 'T00:00:00.000Z');
  const expectedSubject =
    manifest.edition + '; version ' + manifest.editionVersion + '; status ' + manifest.status;
  const expectedAuthor = manifest.authors.join(', ');

  const metadata = [
    ['title', pdf.getTitle(), manifest.displayTitle],
    ['author', pdf.getAuthor(), expectedAuthor],
    ['subject', pdf.getSubject(), expectedSubject],
    ['creator', pdf.getCreator(), PIPELINE_NAME],
    ['producer', pdf.getProducer(), PIPELINE_NAME],
  ];
  for (const [name, actual, expected] of metadata) {
    if (actual !== expected) {
      fail('PDF ' + name + ' differs: expected ' + JSON.stringify(expected) +
        ', got ' + JSON.stringify(actual));
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
  if (pageCount < 50) fail('PDF has too few pages for the initial book: ' + pageCount);
  for (const [index, page] of pdf.getPages().entries()) {
    const size = page.getSize();
    if (Math.abs(size.width - LETTER_WIDTH_POINTS) > 1 ||
        Math.abs(size.height - LETTER_HEIGHT_POINTS) > 1) {
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
  for (const [needle, context] of [
    [manifest.displayTitle, 'book title'],
    ['8. Synthetic Directed Homotopy Theory', 'Chapter 8 heading'],
    ['WalkingEnd', 'walking-endomorphism computation'],
    ['Bibliography', 'bibliography'],
    ['Credits And Third-Party Attribution', 'credits'],
    ['Creative Commons Attribution-ShareAlike 3.0 Unported', 'license'],
  ]) {
    requireText(normalized, needle, context);
  }
  if (extracted.includes('\uFFFD')) fail('PDF text contains the Unicode replacement character');
  if (/^\s*\|?.*\|.*\|\s*$/m.test(extracted) &&
      /^\s*\|?\s*:?-{3,}:?\s*(?:\|\s*:?-{3,}:?\s*)+\|?\s*$/m.test(extracted)) {
    fail('PDF contains raw Markdown table syntax');
  }
  for (const forbidden of [
    'Diagram Error',
    'Chart Error',
    'Could not load',
    'katex-error',
    'arrowgram-error',
  ]) {
    if (normalized.includes(forbidden)) fail('PDF contains render failure text: ' + forbidden);
  }
  const literalTex = extracted.match(
    /\\(?:to|circ|mathsf|operatorname|mathrm|qquad|quad|longrightarrow)\b/
  );
  if (literalTex) {
    fail('PDF text contains a literal TeX command: ' + JSON.stringify(literalTex[0]));
  }
  const bareTexWord = extracted.match(
    /\b(?:qquad|longrightarrow|mathsfclassifier|mathsfcatLevel)\b/
  );
  if (bareTexWord) {
    fail('PDF text contains an unrendered TeX control word: ' + JSON.stringify(bareTexWord[0]));
  }

  const textPages = extracted.split('\f');
  if (textPages.at(-1)?.trim() === '') textPages.pop();
  if (textPages.length !== pageCount) {
    fail('pdftotext page count differs from PDF page count: ' + textPages.length + ' vs ' + pageCount);
  }
  for (const [index, text] of textPages.entries()) {
    if (normalizeText(text).length < 10) {
      fail('PDF page ' + (index + 1) + ' is blank or nearly blank');
    }
  }

  const fontCount = checkFonts(pdfPath);
  console.log(
    'book PDF check passed: ' + path.relative(REPO_ROOT, pdfPath) +
    ', pages=' + pageCount + ', embedded-fonts=' + fontCount +
    ', sha256=' + sha256(pdfPath)
  );
}

main().catch((error) => {
  console.error('book PDF check failed: ' + (error?.message || error));
  process.exitCode = 1;
});
