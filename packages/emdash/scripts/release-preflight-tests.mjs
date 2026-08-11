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
    version: '0.3.0',
    tag: 'emdash-v0.3.0',
    repository: 'hotdocx/emdash',
    artifactName: 'emdash-npm-0.3.0',
    tarballName: 'hotdocx-emdash-0.3.0.tgz',
    provenance: true,
  });
  assert.equal(Object.isFrozen(report), true);
  assert.deepEqual(
    Object.keys(manifest.exports),
    ['.', './authoring', './workspace', './benchmark', './package.json'],
  );
  assert.deepEqual(manifest.exports['./benchmark'], {
    types: './dist/types/package_benchmark.d.ts',
    import: './dist/benchmark.js',
    require: './dist/benchmark.cjs',
    default: './dist/benchmark.js',
  });
  assert.equal(manifest.bin, undefined);
  assert.equal(manifest.scripts, undefined);
  assert.equal(manifest.dependencies, undefined);
});

test('rejects tag, repository, and public-manifest drift', () => {
  assert.throws(
    () => validate({ tag: 'v0.3.0' }),
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
    { ...clone(manifest), version: '0.2.0-01' },
    { ...clone(manifest), version: '0.2.0-.' },
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
    {
      ...clone(manifest),
      exports: {
        ...clone(manifest.exports),
        './benchmark': {
          ...clone(manifest.exports['./benchmark']),
          import: './dist/index.js',
        },
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

test('pins a token-free, least-authority two-job workflow', async () => {
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
    '3d3c42e5aac5ba805825da76410c181273ba90b1',
    '820762786026740c76f36085b0efc47a31fe5020',
    '043fb46d1a93c77aae656e7c1c64a875d1fc6a0a',
    '3e5f45b2cfb9172054b4087a40e8e0b5a5461e7c',
    'persist-credentials: false',
  ]) {
    assert.match(workflow, new RegExp(required.replace(/[.*+?^${}()|[\]\\]/gu, '\\$&'), 'u'));
  }
  assert.doesNotMatch(workflow, /secrets\.|NODE_AUTH_TOKEN|NPM_TOKEN/u);
  assert.doesNotMatch(workflow, /pull_request:|push:|workflow_dispatch:/u);
  assert.equal((workflow.match(/id-token: write/gu) ?? []).length, 1);
  const buildStart = workflow.indexOf('\n  build:\n');
  const publishStart = workflow.indexOf('\n  publish:\n');
  assert.notEqual(buildStart, -1);
  assert.notEqual(publishStart, -1);
  assert.equal(buildStart < publishStart, true);
  const buildJob = workflow.slice(buildStart, publishStart);
  const publishJob = workflow.slice(publishStart);
  assert.doesNotMatch(buildJob, /id-token:/u);
  assert.match(
    publishJob,
    /\n    permissions:\n      contents: read\n      id-token: write\n/u,
  );
  assert.match(
    workflow,
    /verify-packed-install\.mjs \\\n\s+--tarball "\$tarball"/u,
  );
});
