import fs from 'node:fs';
import path from 'node:path';
import { assembleBookText } from './assemble_book.mjs';
import {
  REPO_ROOT,
  loadBookManifest,
  readJsonFile,
  resolveRepoPath,
} from './book_manifest.mjs';
import { loadDocumentRegistry } from './document_registry.mjs';

const ANCHOR_RE = /<a\s+id=["']([A-Za-z0-9][A-Za-z0-9_.:-]*)["']\s*><\/a>/g;
const LINK_RE = /\[[^\]]*\]\(([^)\s]+)(?:\s+["'][^"']*["'])?\)/g;
const STATUS_RE = /\*\*Formal status\s+—\s+(checked|formal consequence|mathematical development|research boundary)\.\*\*/gi;
const EXPECTED_STATUSES = new Set([
  'checked',
  'formal consequence',
  'mathematical development',
  'research boundary',
]);
const EXPANSION_STATUSES = new Set([
  'checked',
  'formal-consequence',
  'mathematical-development',
  'research-boundary',
]);
const SAFE_PROVENANCE_ID = /^[A-Z][A-Z0-9-]*$/;
const SAFE_REMOTE_PATH = /^(?!\/)(?!.*(?:^|\/)\.\.(?:\/|$))[A-Za-z0-9_.\/-]+$/;
const MARKDOWN_IMAGE_RE = /!\[([^\]]*)\]\(([^)\r\n]+)\)/g;
const HTML_IMAGE_RE = /<img\b[^>]*>/gi;
const DIAGRAM_RE = /<div\s+class=["'](?:arrowgram|mermaid|vega-lite)["']([^>]*)>/gi;

function issue(issues, message) {
  issues.push(message);
}

function collectAnchors(text) {
  return [...text.matchAll(ANCHOR_RE)].map((match) => match[1]);
}

function splitTarget(raw) {
  const hashIndex = raw.indexOf('#');
  if (hashIndex < 0) return { file: raw, anchor: '' };
  return {
    file: raw.slice(0, hashIndex),
    anchor: decodeURIComponent(raw.slice(hashIndex + 1)),
  };
}

function stripCodeAndMath(text) {
  return text
    .replace(/```[\s\S]*?```/g, '')
    .replace(/~~~[\s\S]*?~~~/g, '')
    .replace(/\$\$[\s\S]*?\$\$/g, '')
    .replace(/\\\[[\s\S]*?\\\]/g, '')
    .replace(/\\\([\s\S]*?\\\)/g, '')
    .replace(/`[^`\r\n]*`/g, '')
    .replace(/(^|[^\\])\$(?:\\.|[^$\r\n])*?\$/g, '$1');
}

function checkSourceAccessibility(text, relative, issues) {
  const prose = stripCodeAndMath(text);
  for (const match of prose.matchAll(MARKDOWN_IMAGE_RE)) {
    if (match[1].trim() === '') {
      issue(issues, relative + ': Markdown image must have non-empty alt text');
    }
  }
  for (const match of prose.matchAll(HTML_IMAGE_RE)) {
    const element = match[0];
    const alt = element.match(/\balt\s*=\s*["']([^"']*)["']/i)?.[1] ?? '';
    if (alt.trim() === '') {
      issue(issues, relative + ': HTML image must have non-empty alt text');
    }
  }
  for (const match of prose.matchAll(DIAGRAM_RE)) {
    const attributes = match[1];
    if (!/\brole\s*=\s*["']img["']/i.test(attributes)) {
      issue(issues, relative + ': diagram must declare role="img"');
    }
    const label = attributes.match(/\baria-label\s*=\s*["']([^"']*)["']/i)?.[1] ?? '';
    if (label.trim() === '') {
      issue(issues, relative + ': diagram must have a non-empty aria-label');
    }
  }
}

function checkHeadingStructure(source, text, relative, issues) {
  const headings = [...text.matchAll(/^(#{1,6})\s+(.+)$/gm)].map((match) => ({
    level: match[1].length,
    title: match[2].trim(),
  }));
  if (headings.length === 0 && source.id !== 'edition-notice') {
    issue(issues, relative + ': source has no Markdown heading');
    return;
  }
  for (let index = 1; index < headings.length; index += 1) {
    if (headings[index].level > headings[index - 1].level + 1) {
      issue(
        issues,
        relative + ': heading level jumps from H' + headings[index - 1].level +
        ' to H' + headings[index].level + ' at ' + headings[index].title
      );
    }
  }
  const chapterNumber = source.id.match(/^chapter-(\d+)$/)?.[1];
  if (chapterNumber && headings[0]?.title &&
      !headings[0].title.startsWith(chapterNumber + '. ')) {
    issue(issues, relative + ': first heading must begin "' + chapterNumber + '. "');
  }
}

function checkSources(manifest, issues) {
  const sourceData = new Map();
  const globalAnchors = new Map();

  for (const source of manifest.sources) {
    const text = fs.readFileSync(source.absolutePath, 'utf8');
    const relative = path.relative(REPO_ROOT, source.absolutePath);
    if (/^\s*---\s*$/m.test(text.split('\n').slice(0, 2).join('\n'))) {
      issue(issues, relative + ': source files must not contain YAML frontmatter');
    }
    const firstNonblank = text.split(/\r?\n/).find((line) => line.trim() !== '') || '';
    if (!/^<a\s+id=/.test(firstNonblank)) {
      issue(issues, relative + ': first nonblank line must be a stable HTML anchor');
    }
    const anchors = collectAnchors(text);
    if (anchors.length === 0) issue(issues, relative + ': no stable HTML anchor found');
    for (const anchor of anchors) {
      const prior = globalAnchors.get(anchor);
      if (prior) issue(issues, relative + ': duplicate anchor #' + anchor + ' also occurs in ' + prior);
      globalAnchors.set(anchor, relative);
    }
    const statusMatches = [...text.matchAll(STATUS_RE)];
    for (const match of statusMatches) {
      if (!EXPECTED_STATUSES.has(match[1].toLowerCase())) {
        issue(issues, relative + ': unknown formal status ' + match[1]);
      }
    }
    if (/^chapter-(?:\d+)$/.test(source.id) && statusMatches.length === 0) {
      issue(issues, relative + ': every numbered chapter needs a formal-status note');
    }
    if (/^chapter-(?:\d+)$/.test(source.id) &&
        !/<!--\s*evidence:[A-Z][A-Z0-9-]*\s*-->/.test(text)) {
      issue(issues, relative + ': every numbered chapter needs an evidence marker');
    }
    checkSourceAccessibility(text, relative, issues);
    checkHeadingStructure(source, text, relative, issues);
    sourceData.set(source.absolutePath, { text, relative, anchors: new Set(anchors) });
  }

  for (const source of manifest.sources) {
    const data = sourceData.get(source.absolutePath);
    for (const match of stripCodeAndMath(data.text).matchAll(LINK_RE)) {
      const raw = match[1];
      if (/^(?:https?:|mailto:)/i.test(raw)) continue;
      const target = splitTarget(raw);
      if (target.file === '') {
        if (target.anchor && !globalAnchors.has(target.anchor)) {
          issue(issues, data.relative + ': unresolved book anchor #' + target.anchor);
        }
        continue;
      }
      const decodedFile = decodeURIComponent(target.file);
      const resolved = path.resolve(path.dirname(source.absolutePath), decodedFile);
      const relativeTarget = path.relative(REPO_ROOT, resolved);
      if (relativeTarget === '..' || relativeTarget.startsWith('..' + path.sep)) {
        issue(issues, data.relative + ': link escapes repository: ' + raw);
        continue;
      }
      if (!fs.existsSync(resolved)) {
        issue(issues, data.relative + ': missing link target ' + raw);
        continue;
      }
      if (target.anchor) {
        const targetText = fs.readFileSync(resolved, 'utf8');
        if (!collectAnchors(targetText).includes(target.anchor)) {
          issue(issues, data.relative + ': missing target anchor ' + raw);
        }
      }
    }
  }
}

function checkProvenance(manifest, issues) {
  const sourcePath = resolveRepoPath(
    manifest.provenance.thirdPartySources,
    'book/book.json:provenance.thirdPartySources'
  );
  const thirdParty = readJsonFile(sourcePath, manifest.provenance.thirdPartySources);
  const hott = thirdParty.sources?.find((source) => source.id === 'hott-book');
  const pinned = manifest.provenance.sourceRevisions['hott-book'];
  if (!hott) {
    issue(issues, 'third-party source map has no hott-book entry');
    return;
  }
  if (typeof pinned !== 'string' || pinned !== hott.revision) {
    issue(issues, 'HoTT revision differs between book.json and third-party-sources.json');
  }
  if (hott.license?.spdx !== manifest.license.spdx) {
    issue(issues, 'HoTT and book ShareAlike license declarations disagree');
  }
  if (!Array.isArray(hott.adaptations)) {
    issue(issues, 'HoTT provenance adaptations must be an array');
    return;
  }
  if (!Array.isArray(hott.sourceMap) || hott.sourceMap.length === 0) {
    issue(issues, 'HoTT provenance sourceMap must be a non-empty array');
    return;
  }

  const mappedSources = new Map();
  for (const [index, source] of hott.sourceMap.entries()) {
    const context = 'HoTT sourceMap[' + index + ']';
    if (!source || typeof source !== 'object') {
      issue(issues, context + ': expected an object');
      continue;
    }
    if (typeof source.path !== 'string' || !SAFE_REMOTE_PATH.test(source.path)) {
      issue(issues, context + ': invalid repository-relative source path');
      continue;
    }
    if (mappedSources.has(source.path)) {
      issue(issues, context + ': duplicate source path ' + source.path);
      continue;
    }
    if (typeof source.use !== 'string' || source.use.trim() === '') {
      issue(issues, context + ': use must be a non-empty string');
    }
    const labels = source.labels ?? [];
    if (!Array.isArray(labels) ||
        !labels.every((label) => typeof label === 'string' && label.trim() !== '') ||
        new Set(labels).size !== labels.length) {
      issue(issues, context + ': labels must be a unique array of non-empty strings');
    }
    mappedSources.set(source.path, new Set(Array.isArray(labels) ? labels : []));
  }

  const manifestPaths = new Set(manifest.sources.map((source) => source.path));
  const adaptationIds = new Set();
  for (const [index, adaptation] of hott.adaptations.entries()) {
    const context = 'HoTT adaptations[' + index + ']';
    if (!adaptation || typeof adaptation !== 'object') {
      issue(issues, context + ': expected an object');
      continue;
    }
    if (typeof adaptation.id !== 'string' ||
        !SAFE_PROVENANCE_ID.test(adaptation.id)) {
      issue(issues, context + ': invalid adaptation id');
    } else if (adaptationIds.has(adaptation.id)) {
      issue(issues, context + ': duplicate adaptation id ' + adaptation.id);
    } else {
      adaptationIds.add(adaptation.id);
    }
    if (typeof adaptation.target !== 'string' ||
        !manifestPaths.has(adaptation.target)) {
      issue(issues, context + ': target must be an assembled book source');
    } else {
      try {
        resolveRepoPath(adaptation.target, context + '.target');
      } catch (error) {
        issue(issues, error.message);
      }
    }
    if (typeof adaptation.sourcePath !== 'string' ||
        !mappedSources.has(adaptation.sourcePath)) {
      issue(issues, context + ': sourcePath is absent from the HoTT sourceMap');
    }
    if (typeof adaptation.adaptationType !== 'string' ||
        !/^[a-z][a-z-]*$/.test(adaptation.adaptationType)) {
      issue(issues, context + ': adaptationType must be a lowercase type token');
    }
    if (typeof adaptation.description !== 'string' ||
        adaptation.description.trim() === '') {
      issue(issues, context + ': description must be a non-empty string');
    }
    if (!Array.isArray(adaptation.sourceLabels) ||
        adaptation.sourceLabels.length === 0 ||
        !adaptation.sourceLabels.every(
          (label) => typeof label === 'string' && label.trim() !== ''
        ) || new Set(adaptation.sourceLabels).size !== adaptation.sourceLabels.length) {
      issue(issues, context + ': sourceLabels must be a unique non-empty string array');
    } else if (mappedSources.has(adaptation.sourcePath)) {
      const labels = mappedSources.get(adaptation.sourcePath);
      for (const label of adaptation.sourceLabels) {
        if (!labels.has(label)) {
          issue(issues, context + ': unmapped source label ' + label);
        }
      }
    }
  }
}

function checkExpansionContract(manifest, issues) {
  const contractPath = resolveRepoPath(
    manifest.architecture,
    'book/book.json:architecture'
  );
  const contract = readJsonFile(contractPath, manifest.architecture);
  const evidencePath = resolveRepoPath(manifest.evidence, 'book/book.json:evidence');
  const evidence = readJsonFile(evidencePath, manifest.evidence);
  const thirdPartyPath = resolveRepoPath(
    manifest.provenance.thirdPartySources,
    'book/book.json:provenance.thirdPartySources'
  );
  const thirdParty = readJsonFile(
    thirdPartyPath,
    manifest.provenance.thirdPartySources
  );
  const nonempty = (value) => typeof value === 'string' && value.trim() !== '';

  if (!contract || contract.version !== 1) {
    issue(issues, manifest.architecture + ': expected expansion contract version 1');
    return;
  }
  if (!nonempty(contract.planId)) {
    issue(issues, manifest.architecture + ': planId must be non-empty');
  }
  if (!Array.isArray(contract.retainedChapterRange) ||
      contract.retainedChapterRange.length !== 2 ||
      contract.retainedChapterRange[0] !== 1 ||
      contract.retainedChapterRange[1] !== 8) {
    issue(issues, manifest.architecture + ': retainedChapterRange must be [1, 8]');
  }

  const numberedSources = manifest.sources.filter((source) => /^chapter-\d+$/.test(source.id));
  const expectedIds = Array.from({ length: 17 }, (_, index) => 'chapter-' + (index + 1));
  const actualIds = numberedSources.map((source) => source.id);
  if (actualIds.join('\n') !== expectedIds.join('\n')) {
    issue(issues, 'book manifest numbered chapters must be contiguous chapter-1 through chapter-17');
  }
  const manifestById = new Map(manifest.sources.map((source) => [source.id, source]));
  const manifestByPath = new Map(manifest.sources.map((source) => [source.path, source]));
  const claims = evidence.claims && typeof evidence.claims === 'object'
    ? evidence.claims
    : {};

  const retainedTheorems = contract.retainedChapterCentralTheorems;
  if (!Array.isArray(retainedTheorems) || retainedTheorems.length !== 8) {
    issue(issues, manifest.architecture + ': retainedChapterCentralTheorems must cover Chapters 1-8');
  } else {
    for (const [index, theorem] of retainedTheorems.entries()) {
      const number = index + 1;
      const context = manifest.architecture + ':retainedChapterCentralTheorems[' + index + ']';
      const source = manifestById.get('chapter-' + number);
      const claim = theorem && claims[theorem.evidence];
      if (!theorem || theorem.id !== 'chapter-' + number || theorem.number !== number ||
          !nonempty(theorem.claim) || theorem.status !== 'checked' ||
          !nonempty(theorem.evidence) || !claim || claim.status !== theorem.status ||
          !source) {
        issue(issues, context + ': invalid retained-chapter central theorem');
        continue;
      }
      const text = fs.readFileSync(source.absolutePath, 'utf8');
      if (!text.includes('<!-- evidence:' + theorem.evidence + ' -->')) {
        issue(issues, context + ': central theorem evidence is not cited in its chapter');
      }
    }
  }

  if (!Array.isArray(contract.chapters) || contract.chapters.length !== 9) {
    issue(issues, manifest.architecture + ': chapters must contain exactly Chapters 9-17');
  } else {
    const owners = new Set();
    for (const [index, chapter] of contract.chapters.entries()) {
      const number = index + 9;
      const context = manifest.architecture + ':chapters[' + index + ']';
      if (!chapter || typeof chapter !== 'object') {
        issue(issues, context + ': expected an object');
        continue;
      }
      if (chapter.id !== 'chapter-' + number || chapter.number !== number) {
        issue(issues, context + ': id and number must identify Chapter ' + number);
      }
      const source = manifestById.get(chapter.id);
      if (!source || source.path !== chapter.path) {
        issue(issues, context + ': path must match the assembled manifest source');
      } else if (nonempty(chapter.title)) {
        const text = fs.readFileSync(source.absolutePath, 'utf8');
        if (!text.includes('# ' + number + '. ' + chapter.title)) {
          issue(issues, context + ': title does not match the chapter H1');
        }
      } else {
        issue(issues, context + ': title must be non-empty');
      }
      if (!nonempty(chapter.conceptualOwner)) {
        issue(issues, context + ': conceptualOwner must be non-empty');
      } else if (owners.has(chapter.conceptualOwner)) {
        issue(issues, context + ': conceptualOwner duplicates another chapter');
      } else {
        owners.add(chapter.conceptualOwner);
      }
      if (!Array.isArray(chapter.spiralFrom) || chapter.spiralFrom.length === 0) {
        issue(issues, context + ': spiralFrom must name prior chapters');
      } else {
        for (const prior of chapter.spiralFrom) {
          const priorNumber = Number(String(prior).match(/^chapter-(\d+)$/)?.[1]);
          if (!manifestById.has(prior) || !Number.isInteger(priorNumber) ||
              priorNumber >= number) {
            issue(issues, context + ': invalid prior spiral chapter ' + prior);
          }
        }
      }
      const theorem = chapter.centralTheorem;
      if (!theorem || typeof theorem !== 'object' ||
          !EXPANSION_STATUSES.has(theorem.status)) {
        issue(issues, context + ': centralTheorem has an invalid status');
      } else if (['checked', 'formal-consequence'].includes(theorem.status)) {
        const claim = claims[theorem.evidence];
        if (!nonempty(theorem.evidence) || !claim || claim.status !== theorem.status) {
          issue(issues, context + ': central theorem evidence is missing or status-mismatched');
        }
      } else if (!nonempty(theorem.missingInfrastructure)) {
        issue(issues, context + ': non-checked central theorem must name missing infrastructure');
      }
      if (theorem && nonempty(theorem.evidence)) {
        const claim = claims[theorem.evidence];
        if (!claim || claim.status !== theorem.status) {
          issue(issues, context + ': central theorem evidence is unknown or status-mismatched');
        } else if (source) {
          const text = fs.readFileSync(source.absolutePath, 'utf8');
          if (!text.includes('<!-- evidence:' + theorem.evidence + ' -->')) {
            issue(issues, context + ': central theorem evidence is not cited in its chapter');
          }
        }
      }
      for (const evidenceId of chapter.secondaryEvidence ?? []) {
        if (!claims[evidenceId] || claims[evidenceId].status !== 'checked') {
          issue(issues, context + ': unknown checked secondary evidence ' + evidenceId);
        }
      }
      if (!nonempty(chapter.boundary)) {
        issue(issues, context + ': boundary must be non-empty');
      }
    }
  }

  const appendix = contract.appendix;
  const appendixSource = appendix && manifestById.get(appendix.id);
  if (!appendix || appendix.letter !== 'G' || !appendixSource ||
      appendixSource.path !== appendix.path || !nonempty(appendix.title) ||
      !Array.isArray(appendix.sections) || appendix.sections.length !== 7) {
    issue(issues, manifest.architecture + ': Appendix G contract is incomplete or off-manifest');
  }

  const requiredCategoryTerms = new Set([
    'native Cat',
    'equality-local category',
    'finite NCat or OneCat evidence',
    'HoTT precategory',
    'HoTT category',
    'HoTT strict category',
  ]);
  const categoryTerms = new Set();
  for (const entry of contract.categoryTranslation ?? []) {
    if (!entry || !nonempty(entry.term) || !nonempty(entry.meaning) ||
        !EXPANSION_STATUSES.has(entry.status) || !nonempty(entry.boundary)) {
      issue(issues, manifest.architecture + ': invalid categoryTranslation entry');
      continue;
    }
    categoryTerms.add(entry.term);
  }
  for (const term of requiredCategoryTerms) {
    if (!categoryTerms.has(term)) {
      issue(issues, manifest.architecture + ': missing category translation for ' + term);
    }
  }

  const requiredTerminology = new Set([
    'strict category', 'strict transfor', 'lax', 'equivalence', 'isomorphism',
    'univalence', 'saturation', 'dagger', 'opposite', 'duality',
  ]);
  const terminology = new Set();
  for (const entry of contract.terminology ?? []) {
    if (!entry || !nonempty(entry.term) || !nonempty(entry.meaning) ||
        !Array.isArray(entry.notEquivalentTo) || entry.notEquivalentTo.length === 0 ||
        !entry.notEquivalentTo.every(nonempty)) {
      issue(issues, manifest.architecture + ': invalid terminology entry');
      continue;
    }
    terminology.add(entry.term);
  }
  for (const term of requiredTerminology) {
    if (!terminology.has(term)) {
      issue(issues, manifest.architecture + ': missing terminology decision for ' + term);
    }
  }

  const expectedLayers = [
    'computational categorical kernel',
    'canonical mathematical surface',
    'optional future elaborator',
    'external semantic models',
  ];
  if (!Array.isArray(contract.formalLayers) ||
      contract.formalLayers.join('\n') !== expectedLayers.join('\n')) {
    issue(issues, manifest.architecture + ': formalLayers must retain the selected four-layer order');
  }

  const adaptations = thirdParty.sources?.find((source) => source.id === 'hott-book')
    ?.adaptations ?? [];
  const adaptationIds = new Set(adaptations.map((adaptation) => adaptation.id));
  if (!Array.isArray(contract.requiredProvenanceAdaptations) ||
      contract.requiredProvenanceAdaptations.length !== 13 ||
      new Set(contract.requiredProvenanceAdaptations).size !== 13) {
    issue(issues, manifest.architecture + ': requiredProvenanceAdaptations must contain 13 unique entries');
  } else {
    for (const adaptationId of contract.requiredProvenanceAdaptations) {
      if (!adaptationIds.has(adaptationId)) {
        issue(issues, manifest.architecture + ': missing provenance adaptation ' + adaptationId);
      }
    }
  }

  if (!Array.isArray(contract.migration) || contract.migration.length !== 2) {
    issue(issues, manifest.architecture + ': migration must record the two existing chapter moves');
  } else {
    for (const [index, move] of contract.migration.entries()) {
      const context = manifest.architecture + ':migration[' + index + ']';
      if (!move || !nonempty(move.from) || !nonempty(move.to) ||
          manifestByPath.has(move.from) || !manifestByPath.has(move.to) ||
          !nonempty(move.oldAnchor) || !nonempty(move.newAnchor) ||
          !nonempty(move.disposition)) {
        issue(issues, context + ': invalid or incomplete migration record');
      }
    }
  }
}

function checkRegistry(manifest, issues) {
  const registry = loadDocumentRegistry();
  const document = registry.documents.find(
    (candidate) => candidate.slug === manifest.renderer.documentSlug
  );
  if (!document) {
    issue(issues, 'print document registry has no entry for ' + manifest.renderer.documentSlug);
    return;
  }
  if (document.source.mode !== 'generated' || document.kind !== 'book') {
    issue(issues, 'registered book document must have generated source mode and kind=book');
  }
  if (document.file !== path.basename(manifest.renderer.output)) {
    issue(issues, 'book output filename differs between manifest and document registry');
  }
  if (document.layout !== manifest.renderer.layout) {
    issue(issues, 'book layout differs between manifest and document registry');
  }
}

function checkOutput(manifest, outputPath, issues) {
  if (!fs.existsSync(outputPath)) {
    issue(issues, path.relative(REPO_ROOT, outputPath) + ': assembled output is missing');
    return;
  }
  const output = fs.readFileSync(outputPath, 'utf8');
  const expected = assembleBookText(manifest);
  if (output !== expected) {
    issue(issues, path.relative(REPO_ROOT, outputPath) + ': assembled output is stale');
  }
  if (/\/home\/|[A-Za-z]:\\Users\\/.test(output)) {
    issue(issues, 'assembled output contains an absolute host path');
  }
  if (/generated(?:\s+at|\s+on)\s*:/i.test(output)) {
    issue(issues, 'assembled output contains generated timestamp metadata');
  }
  const sourceBreakCount = output.match(
    /<div class="book-source-end" aria-hidden="true"><\/div>/g
  )?.length ?? 0;
  if (sourceBreakCount !== manifest.sources.length) {
    issue(
      issues,
      'assembled output has ' + sourceBreakCount + ' source page ends for ' +
      manifest.sources.length + ' sources'
    );
  }
}

function checkCriticalOrder(manifest, issues) {
  const chapter = manifest.sources.find((source) => source.id === 'chapter-8');
  if (!chapter) {
    issue(issues, 'book manifest has no chapter-8 source');
    return;
  }
  const text = fs.readFileSync(chapter.absolutePath, 'utf8');
  const cell = text.indexOf('<!-- evidence:WE-NORMALIZATION-CELL -->');
  const equality = text.indexOf('<!-- evidence:WE-NORMALIZATION-PATH -->');
  if (cell < 0 || equality < 0 || cell >= equality) {
    issue(issues, 'Chapter 8 must cite the directed normalization cell before equality extraction');
  }
  const bnatSection = text.indexOf('### 8.1.2');
  const bnatEnd = text.indexOf('### 8.1.3', bnatSection + 1);
  const bnatText = bnatSection < 0
    ? ''
    : text.slice(bnatSection, bnatEnd < 0 ? text.length : bnatEnd);
  const statesSeparation = /\b(?:is|remains|kept)\s+separate\b/i.test(bnatText);
  const deniesDefinitionalCollapse =
    /\bdoes\s+not\b[\s\S]{0,180}\bdefinition(?:al|ally)?\b/i.test(bnatText) ||
    /\bnot\s+definitionally\b/i.test(bnatText);
  if (!/\bBNat\b/.test(bnatText) || !statesSeparation || !deniesDefinitionalCollapse) {
    issue(issues, 'Chapter 8 must keep BNat explicitly separate from opaque WalkingEnd');
  }
}

function main() {
  const issues = [];
  const { manifest, outputPath } = loadBookManifest();
  checkSources(manifest, issues);
  checkProvenance(manifest, issues);
  checkExpansionContract(manifest, issues);
  checkRegistry(manifest, issues);
  checkOutput(manifest, outputPath, issues);
  checkCriticalOrder(manifest, issues);

  if (issues.length > 0) {
    for (const message of issues) console.error(message);
    process.exitCode = 1;
    return;
  }
  console.log(
    'book source check passed: ' + manifest.sources.length + ' source file(s), ' +
    manifest.provenance.sourceRevisions['hott-book']
  );
}

try {
  main();
} catch (error) {
  console.error('book source check failed: ' + error.message);
  process.exitCode = 1;
}
