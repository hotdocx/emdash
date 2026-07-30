import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const REPO_ROOT = fileURLToPath(new URL('../', import.meta.url));
const MANIFEST_PATH = path.join(REPO_ROOT, 'emdash2', 'book', 'book.json');
const PDF_ROOT = path.join(REPO_ROOT, 'emdash2', 'output', 'pdf');
const DESTINATIONS = [
  path.join(REPO_ROOT, 'docs', 'emdash-book.pdf'),
  path.join(REPO_ROOT, 'docs', 'emdash3_2.pdf'),
];
const MINIMUM_PDF_BYTES = 100_000;

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

function resolveSource(manifest) {
  const raw = manifest?.artifacts?.pdf;
  if (typeof raw !== 'string' || raw.length === 0 || path.isAbsolute(raw)) {
    fail('book.json artifacts.pdf must be a repository-relative path');
  }
  const source = path.resolve(REPO_ROOT, 'emdash2', raw);
  const relative = path.relative(PDF_ROOT, source);
  if (
    relative === '' ||
    relative === '..' ||
    relative.startsWith('..' + path.sep) ||
    path.isAbsolute(relative) ||
    path.extname(source).toLowerCase() !== '.pdf'
  ) {
    fail('book.json artifacts.pdf must be a .pdf strictly under emdash2/output/pdf');
  }
  const stat = fs.lstatSync(source);
  if (!stat.isFile()) fail('Manifest PDF is not a regular file: ' + relative);
  if (stat.size < MINIMUM_PDF_BYTES) {
    fail('Manifest PDF is unexpectedly small: ' + stat.size + ' bytes');
  }
  return { source, size: stat.size };
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
  const { source, size } = resolveSource(manifest);
  const sourceDigest = sha256(source);

  for (const destination of DESTINATIONS) {
    atomicCopy(source, destination);
    const destinationStat = fs.lstatSync(destination);
    if (!destinationStat.isFile() || destinationStat.size !== size) {
      fail('Promoted PDF size differs: ' + path.relative(REPO_ROOT, destination));
    }
    if (sha256(destination) !== sourceDigest) {
      fail('Promoted PDF digest differs: ' + path.relative(REPO_ROOT, destination));
    }
  }

  console.log('book PDF promoted');
  console.log('source: ' + path.relative(REPO_ROOT, source));
  for (const destination of DESTINATIONS) {
    console.log('destination: ' + path.relative(REPO_ROOT, destination));
  }
  console.log('bytes: ' + size);
  console.log('sha256: ' + sourceDigest);
}

try {
  main();
} catch (error) {
  console.error('book PDF promotion failed: ' + (error?.message || error));
  process.exitCode = 1;
}
