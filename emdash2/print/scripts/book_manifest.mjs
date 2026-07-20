import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

export const REPO_ROOT = fileURLToPath(new URL('../../', import.meta.url));
export const BOOK_MANIFEST_PATH = path.join(REPO_ROOT, 'book', 'book.json');
const SAFE_ID = /^[A-Za-z0-9][A-Za-z0-9-]*$/;

export function resolveRepoPath(raw, context, options = {}) {
  const mustExist = options.mustExist !== false;
  if (typeof raw !== 'string' || raw === '' || path.isAbsolute(raw)) {
    throw new Error(context + ': expected a non-empty repository-relative path');
  }
  const normalized = path.normalize(raw);
  if (normalized === '..' || normalized.startsWith('..' + path.sep)) {
    throw new Error(context + ': path escapes the repository: ' + raw);
  }
  const resolved = path.resolve(REPO_ROOT, normalized);
  const relative = path.relative(REPO_ROOT, resolved);
  if (relative === '..' || relative.startsWith('..' + path.sep) || path.isAbsolute(relative)) {
    throw new Error(context + ': path escapes the repository: ' + raw);
  }
  if (mustExist && !fs.existsSync(resolved)) {
    throw new Error(context + ': file does not exist: ' + raw);
  }
  if (mustExist && !fs.statSync(resolved).isFile()) {
    throw new Error(context + ': expected a file: ' + raw);
  }
  return resolved;
}

export function readJsonFile(filePath, context) {
  try {
    return JSON.parse(fs.readFileSync(filePath, 'utf8'));
  } catch (error) {
    throw new Error(context + ': ' + error.message);
  }
}

export function loadBookManifest() {
  const manifest = readJsonFile(BOOK_MANIFEST_PATH, 'book/book.json');
  if (!manifest || manifest.version !== 1) {
    throw new Error('book/book.json: expected manifest version 1');
  }
  for (const field of [
    'id', 'title', 'subtitle', 'displayTitle', 'edition', 'editionVersion',
    'publicationDate', 'status',
  ]) {
    if (typeof manifest[field] !== 'string' || manifest[field].trim() === '') {
      throw new Error('book/book.json: ' + field + ' must be a non-empty string');
    }
  }
  if (!SAFE_ID.test(manifest.id)) {
    throw new Error('book/book.json: id must be an ASCII identifier');
  }
  if (!/^\d+\.\d+\.\d+(?:-[A-Za-z0-9.-]+)?$/.test(manifest.editionVersion)) {
    throw new Error('book/book.json: editionVersion must be a version identifier');
  }
  if (!/^\d{4}-\d{2}-\d{2}$/.test(manifest.publicationDate)) {
    throw new Error('book/book.json: publicationDate must be YYYY-MM-DD');
  }
  if (!Array.isArray(manifest.authors) || manifest.authors.length === 0 ||
      !manifest.authors.every((author) => typeof author === 'string' && author.trim() !== '')) {
    throw new Error('book/book.json: authors must be a non-empty array of names');
  }
  if (!manifest.license || manifest.license.spdx !== 'CC-BY-SA-3.0') {
    throw new Error('book/book.json: the book license must be CC-BY-SA-3.0');
  }
  resolveRepoPath(manifest.license.file, 'book/book.json:license.file');
  if (!manifest.provenance || typeof manifest.provenance !== 'object') {
    throw new Error('book/book.json: provenance must be an object');
  }
  resolveRepoPath(manifest.provenance.credits, 'book/book.json:provenance.credits');
  resolveRepoPath(
    manifest.provenance.thirdPartySources,
    'book/book.json:provenance.thirdPartySources'
  );
  if (!manifest.provenance.sourceRevisions ||
      typeof manifest.provenance.sourceRevisions !== 'object') {
    throw new Error('book/book.json: provenance.sourceRevisions must be an object');
  }
  resolveRepoPath(manifest.evidence, 'book/book.json:evidence');

  if (!manifest.renderer || typeof manifest.renderer !== 'object') {
    throw new Error('book/book.json: renderer must be an object');
  }
  if (!SAFE_ID.test(manifest.renderer.documentSlug)) {
    throw new Error('book/book.json: renderer.documentSlug must be an ASCII identifier');
  }
  const outputPath = resolveRepoPath(
    manifest.renderer.output,
    'book/book.json:renderer.output',
    { mustExist: false }
  );
  const expectedPublic = path.join(REPO_ROOT, 'print', 'public') + path.sep;
  if (!outputPath.startsWith(expectedPublic) || !/^[\x00-\x7F]+$/.test(path.basename(outputPath))) {
    throw new Error('book/book.json: renderer output must be an ASCII file in print/public');
  }
  if (!['single-column', 'two-column'].includes(manifest.renderer.layout)) {
    throw new Error('book/book.json: renderer.layout is invalid');
  }
  if (!manifest.artifacts || typeof manifest.artifacts !== 'object') {
    throw new Error('book/book.json: artifacts must be an object');
  }
  const pdfPath = resolveRepoPath(
    manifest.artifacts.pdf,
    'book/book.json:artifacts.pdf',
    { mustExist: false }
  );
  const expectedPdf = path.join(REPO_ROOT, 'output', 'pdf') + path.sep;
  if (!pdfPath.startsWith(expectedPdf) || path.extname(pdfPath) !== '.pdf' ||
      !/^[\x00-\x7F]+$/.test(path.basename(pdfPath))) {
    throw new Error('book/book.json: PDF artifact must be an ASCII .pdf in output/pdf');
  }

  if (!Array.isArray(manifest.sources) || manifest.sources.length === 0) {
    throw new Error('book/book.json: sources must be a non-empty array');
  }
  const sourceIds = new Set();
  const sourcePaths = new Set();
  for (const [index, source] of manifest.sources.entries()) {
    const context = 'book/book.json:sources[' + index + ']';
    if (!source || typeof source !== 'object') throw new Error(context + ': expected an object');
    if (typeof source.id !== 'string' || !SAFE_ID.test(source.id)) {
      throw new Error(context + ': id must be an ASCII identifier');
    }
    if (sourceIds.has(source.id)) throw new Error(context + ': duplicate id ' + source.id);
    sourceIds.add(source.id);
    if (!['frontmatter', 'chapter', 'appendix', 'backmatter'].includes(source.kind)) {
      throw new Error(context + ': invalid kind ' + source.kind);
    }
    const sourcePath = resolveRepoPath(source.path, context + '.path');
    if (sourcePaths.has(sourcePath)) throw new Error(context + ': duplicate source path ' + source.path);
    sourcePaths.add(sourcePath);
    source.absolutePath = sourcePath;
  }

  return {
    manifest,
    outputPath,
  };
}
