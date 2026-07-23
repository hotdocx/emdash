import fs from 'node:fs';
import path from 'node:path';
import { pathToFileURL } from 'node:url';
import {
  loadBookManifest,
  readJsonFile,
  resolveRepoPath,
} from './book_manifest.mjs';

const EVIDENCE_TABLE_MARKER = '<!-- generated:book-evidence-table -->';
const CONTENTS_MARKER = '<!-- generated:book-contents -->';

function yamlString(value) {
  return JSON.stringify(String(value));
}

function escapeTableCell(value) {
  return String(value)
    .replaceAll('\\', '\\\\')
    .replaceAll('|', '\\|')
    .replace(/\r?\n/g, ' ')
    .trim();
}

function code(value) {
  return '`' + String(value).replaceAll('`', '\\`') + '`';
}

function renderReferences(references) {
  if (!Array.isArray(references) || references.length === 0) return '—';
  return references.map((reference) => {
    const locator = reference.symbol
      ? code(reference.symbol)
      : 'text ' + code(reference.contains);
    return locator + '<br><small>' + code(reference.file) + '</small>';
  }).join('<br>');
}

export function renderEvidenceTable(evidence) {
  if (!evidence || evidence.version !== 1 ||
      !evidence.claims || typeof evidence.claims !== 'object' ||
      Array.isArray(evidence.claims)) {
    throw new Error('book/evidence.json: expected evidence version 1 with a claims object');
  }

  const rows = [
    '| Evidence | Status | Claim | Owners | Reviewer/check evidence |',
    '| --- | --- | --- | --- | --- |',
  ];
  for (const [claimId, claim] of Object.entries(evidence.claims)) {
    rows.push([
      '| ' + code(claimId),
      escapeTableCell(claim.status),
      escapeTableCell(claim.statement),
      renderReferences(claim.owners),
      renderReferences(claim.reviewers) + ' |',
    ].join(' | '));
  }
  return rows.join('\n');
}

function firstAnchorAndHeading(source) {
  const text = fs.readFileSync(source.absolutePath, 'utf8');
  const anchor = text.match(/<a\s+id=["']([A-Za-z0-9][A-Za-z0-9_.:-]*)["']\s*><\/a>/)?.[1];
  const heading = text.match(/^#\s+(.+)$/m)?.[1]?.trim();
  return anchor && heading ? { anchor, heading } : null;
}

export function renderContents(manifest) {
  const groups = [
    ['Front matter', 'frontmatter'],
    ['Main text', 'chapter'],
    ['Appendices', 'appendix'],
    ['Back matter', 'backmatter'],
  ];
  const lines = [];
  for (const [label, kind] of groups) {
    const entries = manifest.sources
      .filter((source) => source.kind === kind && source.id !== 'contents')
      .map((source) => firstAnchorAndHeading(source))
      .filter(Boolean);
    if (entries.length === 0) continue;
    lines.push('## ' + label, '');
    for (const entry of entries) {
      lines.push('- [' + entry.heading + '](#' + entry.anchor + ')');
    }
    lines.push('');
  }
  return lines.join('\n').trimEnd();
}

function renderSourceBody(source, manifest, evidenceTable, contents) {
  const body = fs.readFileSync(source.absolutePath, 'utf8').trimEnd();
  const evidenceMarkerCount = body.split(EVIDENCE_TABLE_MARKER).length - 1;
  const contentsMarkerCount = body.split(CONTENTS_MARKER).length - 1;
  if (source.id === 'appendix-evidence') {
    if (evidenceMarkerCount !== 1) {
      throw new Error(
        source.path + ': expected exactly one ' + EVIDENCE_TABLE_MARKER + ' marker'
      );
    }
  } else if (evidenceMarkerCount !== 0) {
    throw new Error(source.path + ': evidence table marker belongs only in appendix-evidence');
  }

  if (source.id === 'contents') {
    if (contentsMarkerCount !== 1) {
      throw new Error(
        source.path + ': expected exactly one ' + CONTENTS_MARKER + ' marker'
      );
    }
  } else if (contentsMarkerCount !== 0) {
    throw new Error(source.path + ': contents marker belongs only in contents');
  }

  return body
    .replace(EVIDENCE_TABLE_MARKER, evidenceTable)
    .replace(CONTENTS_MARKER, contents);
}

export function assembleBookText(manifest) {
  const evidencePath = resolveRepoPath(
    manifest.evidence,
    'book/book.json:evidence'
  );
  const evidence = readJsonFile(evidencePath, manifest.evidence);
  const evidenceTable = renderEvidenceTable(evidence);
  const contents = renderContents(manifest);
  const frontmatter = [
    '---',
    'title: ' + yamlString(manifest.displayTitle),
    'authors: ' + yamlString(manifest.authors.join(', ')),
    'edition: ' + yamlString(manifest.edition),
    'editionVersion: ' + yamlString(manifest.editionVersion),
    'publicationDate: ' + yamlString(manifest.publicationDate),
    'status: ' + yamlString(manifest.status),
    'license: ' + yamlString(manifest.license.spdx),
    '---',
    '',
  ].join('\n');

  const sections = manifest.sources.map((source) => {
    const body = renderSourceBody(source, manifest, evidenceTable, contents);
    return [
      '<!-- book-source:' + source.id + ' ' + source.path + ' -->',
      body,
      '<!-- /book-source:' + source.id + ' -->',
      '<div class="book-source-end" aria-hidden="true"></div>',
    ].join('\n');
  });

  return frontmatter + sections.join('\n\n') + '\n';
}

export function runAssembler(argv) {
  const allowed = new Set(['--check']);
  for (const argument of argv) {
    if (!allowed.has(argument)) throw new Error('unknown argument ' + argument);
  }
  const checkOnly = argv.includes('--check');
  const { manifest, outputPath } = loadBookManifest();
  const assembled = assembleBookText(manifest);
  const relativeOutput = path.relative(process.cwd(), outputPath);

  if (checkOnly) {
    if (!fs.existsSync(outputPath)) {
      throw new Error(
        relativeOutput +
          ' is missing; run ./scripts/pnpmw run book:assemble from the Git root',
      );
    }
    const current = fs.readFileSync(outputPath, 'utf8');
    if (current !== assembled) {
      throw new Error(
        relativeOutput +
          ' is stale; run ./scripts/pnpmw run book:assemble from the Git root',
      );
    }
    console.log('book assembly check passed: ' + relativeOutput);
    return;
  }

  fs.mkdirSync(path.dirname(outputPath), { recursive: true });
  fs.writeFileSync(outputPath, assembled, 'utf8');
  console.log(
    'assembled ' + manifest.sources.length + ' source file(s) into ' + relativeOutput
  );
}

const isMain = process.argv[1] &&
  pathToFileURL(path.resolve(process.argv[1])).href === import.meta.url;
if (isMain) {
  try {
    runAssembler(process.argv.slice(2));
  } catch (error) {
    console.error('book assembly failed: ' + error.message);
    process.exitCode = 1;
  }
}
