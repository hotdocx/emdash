import fs from 'node:fs';

const REGISTRY_URL = new URL('../documents.json', import.meta.url);
const SAFE_NAME = /^[A-Za-z0-9][A-Za-z0-9_.-]*$/;
const SAFE_FILE = /^[A-Za-z0-9][A-Za-z0-9_.-]*\.md$/;
const ALLOWED_LAYOUTS = new Set(['single-column', 'two-column']);
const ALLOWED_KINDS = new Set(['article', 'book']);
const ALLOWED_CHECKS = new Set(['validate', 'render']);

function fail(context, message) {
  throw new Error(context + ': ' + message);
}

function loadRegistryJson() {
  try {
    return JSON.parse(fs.readFileSync(REGISTRY_URL, 'utf8'));
  } catch (error) {
    fail('print/documents.json', error.message);
  }
}

export function loadDocumentRegistry() {
  const registry = loadRegistryJson();
  if (!registry || registry.version !== 1 || !Array.isArray(registry.documents)) {
    fail('print/documents.json', 'expected version 1 and a documents array');
  }
  if (registry.documents.length === 0) {
    fail('print/documents.json', 'documents must not be empty');
  }

  const ids = new Set();
  const selectors = new Map();
  let defaultCount = 0;

  for (const [index, document] of registry.documents.entries()) {
    const context = 'print/documents.json:documents[' + index + ']';
    if (!document || typeof document !== 'object' || Array.isArray(document)) {
      fail(context, 'document must be an object');
    }
    for (const field of ['id', 'slug']) {
      if (typeof document[field] !== 'string' || !SAFE_NAME.test(document[field])) {
        fail(context, field + ' must be an ASCII identifier');
      }
    }
    if (ids.has(document.id)) fail(context, 'duplicate id ' + document.id);
    ids.add(document.id);
    if (typeof document.file !== 'string' || !SAFE_FILE.test(document.file)) {
      fail(context, 'file must be a safe ASCII Markdown filename');
    }
    if (typeof document.title !== 'string' || document.title.trim() === '') {
      fail(context, 'title must be non-empty');
    }
    if (!ALLOWED_KINDS.has(document.kind)) {
      fail(context, 'kind must be article or book');
    }
    if (typeof document.default !== 'boolean' || typeof document.generated !== 'boolean') {
      fail(context, 'default and generated must be booleans');
    }
    if (document.default) defaultCount += 1;
    if (!Array.isArray(document.aliases) || !document.aliases.every((value) => typeof value === 'string')) {
      fail(context, 'aliases must be an array of strings');
    }
    if (!Array.isArray(document.groups) || document.groups.length === 0) {
      fail(context, 'groups must be a non-empty array');
    }
    for (const group of document.groups) {
      if (typeof group !== 'string' || !SAFE_NAME.test(group)) {
        fail(context, 'group names must be ASCII identifiers');
      }
    }
    if (!ALLOWED_LAYOUTS.has(document.layout)) {
      fail(context, 'layout must be single-column or two-column');
    }
    if (!document.checks || typeof document.checks !== 'object') {
      fail(context, 'checks must be an object');
    }
    for (const check of ALLOWED_CHECKS) {
      if (typeof document.checks[check] !== 'boolean') {
        fail(context, 'checks.' + check + ' must be a boolean');
      }
    }
    if (!Number.isSafeInteger(document.timeoutMs) || document.timeoutMs < 1000) {
      fail(context, 'timeoutMs must be an integer of at least 1000');
    }

    const localSelectors = new Set([
      document.id,
      document.slug,
      document.file,
      ...document.aliases,
    ]);
    for (const selector of localSelectors) {
      const prior = selectors.get(selector);
      if (prior && prior !== document.id) {
        fail(context, 'selector ' + JSON.stringify(selector) + ' is also owned by ' + prior);
      }
      selectors.set(selector, document.id);
    }
  }

  if (defaultCount !== 1) {
    fail('print/documents.json', 'exactly one document must be the default');
  }
  return registry;
}

export function parseDocumentSelection(argv) {
  const selection = { document: null, group: null };
  for (let index = 0; index < argv.length; index += 1) {
    const argument = argv[index];
    if (argument.startsWith('--document=')) {
      selection.document = argument.slice('--document='.length);
    } else if (argument === '--document') {
      index += 1;
      if (index >= argv.length) fail('arguments', '--document requires a value');
      selection.document = argv[index];
    } else if (argument.startsWith('--group=')) {
      selection.group = argument.slice('--group='.length);
    } else if (argument === '--group') {
      index += 1;
      if (index >= argv.length) fail('arguments', '--group requires a value');
      selection.group = argv[index];
    } else {
      fail('arguments', 'unknown argument ' + argument);
    }
  }
  if (selection.document !== null && selection.group !== null) {
    fail('arguments', '--document and --group are mutually exclusive');
  }
  return selection;
}

export function selectDocuments(argv, check) {
  if (!ALLOWED_CHECKS.has(check)) fail('selection', 'unknown check ' + check);
  const registry = loadDocumentRegistry();
  const selection = parseDocumentSelection(argv);
  let documents = registry.documents;

  if (selection.document !== null) {
    const needle = selection.document;
    documents = documents.filter((document) =>
      new Set([document.id, document.slug, document.file, ...document.aliases]).has(needle)
    );
    if (documents.length === 0) {
      fail('selection', 'unknown document ' + JSON.stringify(needle));
    }
  } else if (selection.group !== null) {
    documents = documents.filter((document) => document.groups.includes(selection.group));
    if (documents.length === 0) {
      fail('selection', 'unknown or empty group ' + JSON.stringify(selection.group));
    }
  }

  documents = documents.filter((document) => document.checks[check]);
  if (documents.length === 0) {
    fail('selection', 'no selected documents participate in ' + check);
  }
  return documents;
}

export function documentQuery(document) {
  return document.default ? '' : '?paper=' + encodeURIComponent(document.slug);
}
