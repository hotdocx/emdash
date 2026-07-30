import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const REPO_ROOT = fileURLToPath(new URL('../', import.meta.url));
const MANIFEST_PATH = path.join(REPO_ROOT, 'emdash2', 'book', 'book.json');
const PDF_ROOT = path.join(REPO_ROOT, 'emdash2', 'output', 'pdf');
const PRINT_PUBLIC_ROOT = path.join(REPO_ROOT, 'emdash2', 'print', 'public');
const PDF_DESTINATION = path.join(REPO_ROOT, 'docs', 'emdash-book.pdf');
const MARKDOWN_DESTINATION = path.join(REPO_ROOT, 'docs', 'emdash-book.md');
const MINIMUM_PDF_BYTES = 100_000;
const MINIMUM_MARKDOWN_BYTES = 10_000;

function fail(message) {
  throw new Error(message);
}

function sha256(filePath) {
  return crypto
    .createHash('sha256')
    .update(fs.readFileSync(filePath))
    .digest('hex');
}

function readManifest() {
  try {
    return JSON.parse(fs.readFileSync(MANIFEST_PATH, 'utf8'));
  } catch (error) {
    fail('Could not read emdash2/book/book.json: ' + error.message);
  }
}

function resolveOwnedFile(raw, {
  context,
  root,
  extension,
  minimumBytes,
}) {
  if (typeof raw !== 'string' || raw.length === 0 || path.isAbsolute(raw)) {
    fail(context + ' must be a repository-relative path');
  }
  const source = path.resolve(REPO_ROOT, 'emdash2', raw);
  const relative = path.relative(root, source);
  if (
    relative === '' ||
    relative === '..' ||
    relative.startsWith('..' + path.sep) ||
    path.isAbsolute(relative) ||
    path.extname(source).toLowerCase() !== extension
  ) {
    fail(context + ' must be a ' + extension + ' file strictly under ' +
      path.relative(REPO_ROOT, root));
  }
  const stat = fs.lstatSync(source);
  if (!stat.isFile()) fail(context + ' is not a regular file: ' + relative);
  if (stat.size < minimumBytes) {
    fail(context + ' is unexpectedly small: ' + stat.size + ' bytes');
  }
  return { source, size: stat.size };
}

function resolveSources(manifest) {
  const raw = manifest?.artifacts?.pdf;
  const markdownRaw = manifest?.renderer?.output;
  return {
    pdf: resolveOwnedFile(raw, {
      context: 'book.json artifacts.pdf',
      root: PDF_ROOT,
      extension: '.pdf',
      minimumBytes: MINIMUM_PDF_BYTES,
    }),
    markdown: resolveOwnedFile(markdownRaw, {
      context: 'book.json renderer.output',
      root: PRINT_PUBLIC_ROOT,
      extension: '.md',
      minimumBytes: MINIMUM_MARKDOWN_BYTES,
    }),
  };
}

function atomicCopy(source, destination) {
  const temporary = path.join(
    path.dirname(destination),
    '.' + path.basename(destination) + '.' + crypto.randomUUID() + '.tmp'
  );
  try {
    fs.copyFileSync(source, temporary, fs.constants.COPYFILE_EXCL);
    const descriptor = fs.openSync(temporary, 'r');
    try {
      fs.fsyncSync(descriptor);
    } finally {
      fs.closeSync(descriptor);
    }
    fs.renameSync(temporary, destination);
  } finally {
    fs.rmSync(temporary, { force: true });
  }
}

function main() {
  const manifest = readManifest();
  const sources = resolveSources(manifest);
  const artifacts = [
    {
      kind: 'book PDF',
      ...sources.pdf,
      destination: PDF_DESTINATION,
    },
    {
      kind: 'book Markdown',
      ...sources.markdown,
      destination: MARKDOWN_DESTINATION,
    },
  ];

  for (const { kind, source, size, destination } of artifacts) {
    const sourceDigest = sha256(source);
    atomicCopy(source, destination);
    const destinationStat = fs.lstatSync(destination);
    if (!destinationStat.isFile() || destinationStat.size !== size) {
      fail('Promoted ' + kind + ' size differs: ' + path.relative(REPO_ROOT, destination));
    }
    if (sha256(destination) !== sourceDigest) {
      fail('Promoted ' + kind + ' digest differs: ' + path.relative(REPO_ROOT, destination));
    }
    console.log(kind + ' promoted');
    console.log('source: ' + path.relative(REPO_ROOT, source));
    console.log('destination: ' + path.relative(REPO_ROOT, destination));
    console.log('bytes: ' + size);
    console.log('sha256: ' + sourceDigest);
  }
}

try {
  main();
} catch (error) {
  console.error('book artifact promotion failed: ' + (error?.message || error));
  process.exitCode = 1;
}
