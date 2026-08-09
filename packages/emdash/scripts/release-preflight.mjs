import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

export const EMDASH_NPM_RELEASE_PREFLIGHT_REVISION =
  'emdash-npm-release-preflight-v1';

const EXPECTED_NAME = '@hotdocx/emdash';
const EXPECTED_REPOSITORY = 'hotdocx/emdash';
const EXPECTED_REPOSITORY_URL =
  'git+https://github.com/hotdocx/emdash.git';
const EXPECTED_REPOSITORY_MANIFEST = Object.freeze({
  type: 'git',
  url: EXPECTED_REPOSITORY_URL,
  directory: 'packages/emdash',
});
const EXPECTED_PUBLISH_CONFIG = Object.freeze({
  access: 'public',
  provenance: true,
});
const EXPECTED_ENGINES = Object.freeze({ node: '>=20' });
const EXPECTED_EXPORTS = Object.freeze({
  '.': {
    types: './dist/types/package_core.d.ts',
    import: './dist/index.js',
    require: './dist/index.cjs',
    default: './dist/index.js',
  },
  './authoring': {
    types: './dist/types/package_authoring.d.ts',
    import: './dist/authoring.js',
    require: './dist/authoring.cjs',
    default: './dist/authoring.js',
  },
  './workspace': {
    types: './dist/types/package_workspace.d.ts',
    import: './dist/workspace.js',
    require: './dist/workspace.cjs',
    default: './dist/workspace.js',
  },
  './package.json': './package.json',
});
const EXPECTED_FILES = Object.freeze(['dist', 'README.md', 'LICENSE']);
const FORBIDDEN_PUBLISHED_FIELDS = Object.freeze([
  'bin',
  'browser',
  'bundleDependencies',
  'bundledDependencies',
  'cpu',
  'dependencies',
  'imports',
  'libc',
  'man',
  'optionalDependencies',
  'os',
  'peerDependencies',
  'peerDependenciesMeta',
  'scripts',
  'typesVersions',
  'workspaces',
]);
const SEMVER_CORE =
  /^(?:0|[1-9][0-9]*)\.(?:0|[1-9][0-9]*)\.(?:0|[1-9][0-9]*)$/u;
const SEMVER_PRERELEASE_IDENTIFIER = /^[0-9A-Za-z-]+$/u;
const SEMVER_NUMERIC_IDENTIFIER = /^[0-9]+$/u;

export class EmdashNpmReleasePreflightError extends Error {
  constructor(code, path_, message) {
    super(`${message} (${path_})`);
    this.name = 'EmdashNpmReleasePreflightError';
    this.code = code;
    this.path = path_;
  }
}

const fail = (code, path_, message) => {
  throw new EmdashNpmReleasePreflightError(code, path_, message);
};

const exactArray = (actual, expected, path_) => {
  if (
    !Array.isArray(actual) ||
    actual.length !== expected.length ||
    actual.some((value, index) => value !== expected[index])
  ) {
    fail('INVALID_MANIFEST', path_, `Expected ${expected.join(', ')}`);
  }
};

const exactJson = (actual, expected, path_) => {
  if (JSON.stringify(actual) !== JSON.stringify(expected)) {
    fail('INVALID_MANIFEST', path_, 'Expected the exact reviewed value');
  }
};

const isExactSemver = (value) => {
  const separator = value.indexOf('-');
  const core = separator === -1 ? value : value.slice(0, separator);
  if (!SEMVER_CORE.test(core)) return false;
  if (separator === -1) return true;
  const prerelease = value.slice(separator + 1);
  return prerelease.length > 0 && prerelease.split('.').every((identifier) =>
    SEMVER_PRERELEASE_IDENTIFIER.test(identifier) &&
    (!SEMVER_NUMERIC_IDENTIFIER.test(identifier) ||
      identifier === '0' || identifier[0] !== '0'));
};

export function validateEmdashNpmReleasePreflight(input) {
  const { manifest, repository, tag } = input ?? {};
  if (!manifest || typeof manifest !== 'object' || Array.isArray(manifest)) {
    fail('INVALID_MANIFEST', 'manifest', 'Expected a package manifest');
  }
  if (manifest.name !== EXPECTED_NAME) {
    fail('INVALID_MANIFEST', 'manifest.name', `Expected ${EXPECTED_NAME}`);
  }
  if (
    typeof manifest.version !== 'string' ||
    !isExactSemver(manifest.version)
  ) {
    fail('INVALID_MANIFEST', 'manifest.version', 'Expected exact semver');
  }
  const expectedTag = `emdash-v${manifest.version}`;
  if (tag !== expectedTag) {
    fail('INVALID_TAG', 'tag', `Expected ${expectedTag}`);
  }
  if (repository !== EXPECTED_REPOSITORY) {
    fail(
      'INVALID_REPOSITORY',
      'repository',
      `Expected ${EXPECTED_REPOSITORY}`,
    );
  }
  exactJson(
    manifest.repository,
    EXPECTED_REPOSITORY_MANIFEST,
    'manifest.repository',
  );
  if (manifest.private !== undefined && manifest.private !== false) {
    fail('INVALID_MANIFEST', 'manifest.private', 'Package must be publishable');
  }
  if (manifest.license !== 'ISC' || manifest.sideEffects !== false) {
    fail(
      'INVALID_MANIFEST',
      'manifest.license',
      'Expected ISC and sideEffects=false',
    );
  }
  for (const field of FORBIDDEN_PUBLISHED_FIELDS) {
    if (manifest[field] !== undefined) {
      fail(
        'INVALID_MANIFEST',
        `manifest.${field}`,
        'Published package must have no CLI, install hooks, or runtime ' +
          'dependency surface',
      );
    }
  }
  exactJson(
    manifest.publishConfig,
    EXPECTED_PUBLISH_CONFIG,
    'manifest.publishConfig',
  );
  exactJson(manifest.engines, EXPECTED_ENGINES, 'manifest.engines');
  if (
    manifest.type !== 'module' ||
    manifest.main !== './dist/index.cjs' ||
    manifest.module !== './dist/index.js' ||
    manifest.types !== './dist/types/package_core.d.ts'
  ) {
    fail(
      'INVALID_MANIFEST',
      'manifest.main',
      'Expected the exact dual-runtime and declaration entries',
    );
  }
  exactJson(manifest.exports, EXPECTED_EXPORTS, 'manifest.exports');
  exactArray(manifest.files, EXPECTED_FILES, 'manifest.files');

  return Object.freeze({
    revision: EMDASH_NPM_RELEASE_PREFLIGHT_REVISION,
    packageName: EXPECTED_NAME,
    version: manifest.version,
    tag: expectedTag,
    repository: EXPECTED_REPOSITORY,
    artifactName: `emdash-npm-${manifest.version}`,
    tarballName: `hotdocx-emdash-${manifest.version}.tgz`,
    provenance: true,
  });
}

const packageRoot = path.resolve(
  path.dirname(fileURLToPath(import.meta.url)),
  '..',
);

const parseCli = (arguments_) => {
  const values = new Map();
  for (let index = 0; index < arguments_.length; index += 2) {
    const key = arguments_[index];
    const value = arguments_[index + 1];
    if (!['--tag', '--repository'].includes(key) || value === undefined) {
      throw new Error(
        'Usage: release-preflight.mjs --tag TAG --repository OWNER/REPO',
      );
    }
    if (values.has(key)) throw new Error(`Duplicate option ${key}`);
    values.set(key, value);
  }
  if (!values.has('--tag') || !values.has('--repository')) {
    throw new Error(
      'Usage: release-preflight.mjs --tag TAG --repository OWNER/REPO',
    );
  }
  return values;
};

const isMain = process.argv[1] &&
  pathToFileURL(path.resolve(process.argv[1])).href === import.meta.url;

if (isMain) {
  const options = parseCli(process.argv.slice(2));
  const manifest = JSON.parse(
    await readFile(path.join(packageRoot, 'package.json'), 'utf8'),
  );
  const report = validateEmdashNpmReleasePreflight({
    manifest,
    repository: options.get('--repository'),
    tag: options.get('--tag'),
  });
  process.stdout.write(`${JSON.stringify(report)}\n`);
}
