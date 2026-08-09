import assert from 'node:assert/strict';
import { existsSync, readFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = join(dirname(fileURLToPath(import.meta.url)), '..');
const expectedPackageManager = 'pnpm@11.16.0';

function readJson(relativePath) {
  return JSON.parse(readFileSync(join(root, relativePath), 'utf8'));
}

function assertNoNpmScripts(label, manifest) {
  for (const [name, command] of Object.entries(manifest.scripts ?? {})) {
    assert.doesNotMatch(
      command,
      /(^|[\s;&|])npm(?=\s|$)/,
      `${label} script ${name} must not bypass the pnpm workspace`,
    );
  }
}

const rootPackage = readJson('package.json');
const emdashPackage = readJson('packages/emdash/package.json');
const specPackage = readJson('emdash2/package.json');
const printPackage = readJson('emdash2/print/package.json');
const workspace = readFileSync(join(root, 'pnpm-workspace.yaml'), 'utf8');

assert.equal(rootPackage.private, true, 'the contributor workspace must be private');
assert.equal(
  rootPackage.packageManager,
  expectedPackageManager,
  'packageManager must pin the reviewed pnpm release',
);
assert.equal(rootPackage.workspaces, undefined, 'pnpm-workspace.yaml owns membership');
assert.equal(
  rootPackage.dependencies?.emdash,
  undefined,
  'the root package must not depend on or link to itself',
);

for (const entry of ['packages/emdash', 'emdash2', 'emdash2/print']) {
  assert.match(workspace, new RegExp(`^\\s*- ${entry.replace('/', '\\/')}$`, 'm'));
}
assert.doesNotMatch(
  workspace,
  /^\s*- emdash-template$/m,
  'the distributable template must remain outside the contributor workspace',
);
assert.match(
  workspace,
  /^enableGlobalVirtualStore: false$/m,
  'interactive and CI installs must use the same worktree-local virtual store',
);
assert.match(
  workspace,
  /^verifyDepsBeforeRun: error$/m,
  'script execution must report stale dependencies instead of auto-installing',
);

assert.equal(existsSync(join(root, 'package-lock.json')), false, 'remove the obsolete root npm lock');
assert.equal(
  existsSync(join(root, 'emdash2/print/package-lock.json')),
  false,
  'remove the obsolete print npm lock',
);
assert.equal(
  existsSync(join(root, 'packages/emdash/package-lock.json')),
  false,
  'the emdash distribution must use the shared pnpm lock',
);
assert.equal(existsSync(join(root, 'pnpm-lock.yaml')), true, 'commit the shared pnpm lock');
assert.equal(
  existsSync(join(root, 'emdash-template/package-lock.json')),
  true,
  'retain the standalone template npm lock',
);
assert.equal(existsSync(join(root, 'AGENTS.md')), true, 'Codex needs a canonical root AGENTS.md');
assert.equal(existsSync(join(root, '.AGENTS.md')), false, 'remove the undiscovered hidden instruction file');
assert.equal(
  existsSync(join(root, 'docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md')),
  true,
  'retain the v3.2 elaborator handoff',
);

assertNoNpmScripts('root', rootPackage);
assertNoNpmScripts('@hotdocx/emdash', emdashPackage);
assertNoNpmScripts('emdash2', specPackage);
assertNoNpmScripts('print', printPackage);

assert.equal(emdashPackage.name, '@hotdocx/emdash');
assert.equal(emdashPackage.version, '0.1.0');
assert.notEqual(
  emdashPackage.private,
  true,
  'the bounded emdash distribution must remain packable',
);
assert.equal(emdashPackage.license, rootPackage.license);
assert.equal(emdashPackage.sideEffects, false);
assert.equal(emdashPackage.engines?.node, '>=20');
assert.equal(
  emdashPackage.dependencies,
  undefined,
  'the browser-safe emdash core must have no runtime package dependency',
);
assert.deepEqual(
  emdashPackage.publishConfig,
  { access: 'public', provenance: true },
  'the public package must retain its exact reviewed publication policy',
);
assert.deepEqual(
  Object.keys(emdashPackage.exports),
  ['.', './authoring', './workspace', './package.json'],
  'the emdash package must expose only its reviewed entry points',
);

const [nodeMajor, nodeMinor] = process.versions.node.split('.').map(Number);
assert.equal(
  nodeMajor > 22 || (nodeMajor === 22 && nodeMinor >= 13),
  true,
  `Node ${process.versions.node} is too old; pnpm 11 requires Node >=22.13`,
);

console.log(
  `workspace contract passed: ${expectedPackageManager}; root + emdash + emdash2 + print; Node ${process.versions.node}`,
);
