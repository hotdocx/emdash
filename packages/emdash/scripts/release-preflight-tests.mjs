import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import test from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  EmdashNpmReleasePreflightError,
  validateEmdashNpmReleasePreflight,
} from './release-preflight.mjs';

const packageRoot = path.resolve(
  path.dirname(fileURLToPath(import.meta.url)),
  '..',
);
const repositoryRoot = path.resolve(packageRoot, '..', '..');
const manifest = JSON.parse(
  await readFile(path.join(packageRoot, 'package.json'), 'utf8'),
);

const validate = (overrides = {}) => validateEmdashNpmReleasePreflight({
  manifest,
  repository: 'hotdocx/emdash',
  tag: `emdash-v${manifest.version}`,
  ...overrides,
});

const clone = (value) => structuredClone(value);

test('accepts the exact immutable emdash release identity', () => {
  const report = validate();
  assert.deepEqual(report, {
    revision: 'emdash-npm-release-preflight-v1',
    packageName: '@hotdocx/emdash',
    version: '0.1.0',
    tag: 'emdash-v0.1.0',
    repository: 'hotdocx/emdash',
    artifactName: 'emdash-npm-0.1.0',
    tarballName: 'hotdocx-emdash-0.1.0.tgz',
    provenance: true,
  });
  assert.equal(Object.isFrozen(report), true);
});

test('rejects tag, repository, and public-manifest drift', () => {
  assert.throws(
    () => validate({ tag: 'v0.1.0' }),
    (error) => error instanceof EmdashNpmReleasePreflightError &&
      error.code === 'INVALID_TAG',
  );
  assert.throws(
    () => validate({ repository: 'fork/emdash' }),
    (error) => error instanceof EmdashNpmReleasePreflightError &&
      error.code === 'INVALID_REPOSITORY',
  );
  for (const changedManifest of [
    { ...clone(manifest), scripts: { publish: 'npm publish' } },
    { ...clone(manifest), dependencies: { surprise: '1.0.0' } },
    { ...clone(manifest), optionalDependencies: { surprise: '1.0.0' } },
    { ...clone(manifest), peerDependencies: { surprise: '1.0.0' } },
    { ...clone(manifest), bin: { emdash: './dist/cli.js' } },
    {
      ...clone(manifest),
      publishConfig: { access: 'public', provenance: false },
    },
    {
      ...clone(manifest),
      publishConfig: {
        access: 'public',
        provenance: true,
        registry: 'https://example.invalid',
      },
    },
    { ...clone(manifest), browser: './wrong-browser.js' },
    { ...clone(manifest), private: 'false' },
    { ...clone(manifest), version: '0.1.0-01' },
    { ...clone(manifest), version: '0.1.0-.' },
    {
      ...clone(manifest),
      exports: { ...clone(manifest.exports), './private': './private.js' },
    },
    {
      ...clone(manifest),
      exports: {
        ...clone(manifest.exports),
        '.': { ...clone(manifest.exports['.']), import: './wrong.js' },
      },
    },
  ]) {
    assert.throws(
      () => validate({ manifest: changedManifest }),
      (error) => error instanceof EmdashNpmReleasePreflightError &&
        error.code === 'INVALID_MANIFEST',
    );
  }
});

test('pins a version-locked first-publish bootstrap workflow', async () => {
  const workflow = await readFile(
    path.join(repositoryRoot, '.github', 'workflows', 'npm-publish.yml'),
    'utf8',
  );
  for (const required of [
    'release:',
    'types: [published]',
    "if: startsWith(github.event.release.tag_name, 'emdash-v')",
    'environment: npm-release',
    'id-token: write',
    'git merge-base --is-ancestor HEAD refs/remotes/origin/main',
    'node packages/emdash/scripts/release-preflight.mjs',
    'name: ${{ needs.build.outputs.artifact_name }}',
    'sha256sum "$tarball"',
    'npm install --global npm@11.19.0 --ignore-scripts',
    'npm publish "$tarball" --access public --provenance',
    "needs.build.outputs.version == '0.1.0' && " +
      "secrets.NPM_BOOTSTRAP_TOKEN || ''",
    'd23441a48e516b6c34aea4fa41551a30e30af803',
    '820762786026740c76f36085b0efc47a31fe5020',
    'ea165f8d65b6e75b540449e92b4886f43607fa02',
    '018cc2cf5baa6db3ef3c5f8a56943fffe632ef53',
  ]) {
    assert.match(workflow, new RegExp(required.replace(/[.*+?^${}()|[\]\\]/gu, '\\$&'), 'u'));
  }
  assert.equal((workflow.match(/secrets\./gu) ?? []).length, 1);
  assert.equal((workflow.match(/NODE_AUTH_TOKEN/gu) ?? []).length, 1);
  assert.doesNotMatch(workflow, /NPM_TOKEN/u);
  assert.doesNotMatch(workflow, /pull_request:|push:|workflow_dispatch:/u);
  assert.equal((workflow.match(/id-token: write/gu) ?? []).length, 1);
  const buildStart = workflow.indexOf('\n  build:\n');
  const publishStart = workflow.indexOf('\n  publish:\n');
  assert.notEqual(buildStart, -1);
  assert.notEqual(publishStart, -1);
  assert.equal(buildStart < publishStart, true);
  const buildJob = workflow.slice(buildStart, publishStart);
  const publishJob = workflow.slice(publishStart);
  assert.doesNotMatch(buildJob, /id-token:|secrets\.|NODE_AUTH_TOKEN/u);
  assert.match(
    publishJob,
    /\n    permissions:\n      contents: read\n      id-token: write\n/u,
  );
  assert.match(
    publishJob,
    /NODE_AUTH_TOKEN: \$\{\{ needs\.build\.outputs\.version == '0\.1\.0' && secrets\.NPM_BOOTSTRAP_TOKEN \|\| '' \}\}/u,
  );
  assert.match(
    workflow,
    /verify-packed-install\.mjs \\\n\s+--tarball "\$tarball"/u,
  );
});
