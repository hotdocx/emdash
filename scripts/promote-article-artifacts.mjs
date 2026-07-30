import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import { selectArticle } from '../emdash2/print/scripts/article_manifest.mjs';

const REPO_ROOT = fileURLToPath(new URL('../', import.meta.url));
const ARTICLE_ID = process.argv[2] || 'emdash-v3-2-overview';

function fail(message) {
  throw new Error(message);
}

function sha256(filePath) {
  return crypto.createHash('sha256').update(fs.readFileSync(filePath)).digest('hex');
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

function checkedFile(source, minimumBytes, kind) {
  if (!fs.existsSync(source)) fail(kind + ' source is missing');
  const stat = fs.lstatSync(source);
  if (!stat.isFile()) fail(kind + ' source is not a regular file');
  if (stat.size < minimumBytes) {
    fail(kind + ' source is unexpectedly small: ' + stat.size + ' bytes');
  }
  return stat.size;
}

function promote(source, destination, minimumBytes, kind) {
  const size = checkedFile(source, minimumBytes, kind);
  const digest = sha256(source);
  atomicCopy(source, destination);
  if (
    fs.lstatSync(destination).size !== size ||
    sha256(destination) !== digest
  ) {
    fail(kind + ' promotion differs at ' + path.relative(REPO_ROOT, destination));
  }
  console.log(kind + ' promoted');
  console.log('source: ' + path.relative(REPO_ROOT, source));
  console.log('destination: ' + path.relative(REPO_ROOT, destination));
  console.log('bytes: ' + size);
  console.log('sha256: ' + digest);
}

try {
  if (process.argv.length > 3) {
    fail('usage: promote-article-artifacts.mjs [article-id]');
  }
  const article = selectArticle(ARTICLE_ID);
  promote(
    article.sourcePath,
    article.distributionPaths.markdown,
    10_000,
    'article Markdown'
  );
  promote(
    article.artifactPath,
    article.distributionPaths.pdf,
    100_000,
    'article PDF'
  );
} catch (error) {
  console.error('article artifact promotion failed: ' + (error?.message || error));
  process.exitCode = 1;
}
