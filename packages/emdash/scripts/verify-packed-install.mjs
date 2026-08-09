import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import {
  mkdir,
  mkdtemp,
  readFile,
  rm,
  writeFile,
} from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const packageRoot = path.resolve(
  path.dirname(fileURLToPath(import.meta.url)),
  '..',
);
const repositoryRoot = path.resolve(packageRoot, '..', '..');
const pnpmWrapper = path.join(repositoryRoot, 'scripts', 'pnpmw');

const run = (command, args, cwd, capture = false) => execFileSync(
  command,
  args,
  {
    cwd,
    encoding: 'utf8',
    stdio: capture ? ['ignore', 'pipe', 'inherit'] : 'inherit',
  },
);

const temporaryRoot = await mkdtemp(
  path.join(os.tmpdir(), 'emdash-packed-install-'),
);
const tarballDirectory = path.join(temporaryRoot, 'tarballs');
const consumerDirectory = path.join(temporaryRoot, 'consumer');

try {
  await mkdir(tarballDirectory);
  await mkdir(consumerDirectory);

  const packOutput = run(
    pnpmWrapper,
    [
      '--dir',
      packageRoot,
      'pack',
      '--json',
      '--pack-destination',
      tarballDirectory,
    ],
    repositoryRoot,
    true,
  );
  const packed = JSON.parse(packOutput);
  const packedRecord = Array.isArray(packed) ? packed[0] : packed;
  const packedFiles = new Set(
    packedRecord.files.map((file) => file.path),
  );
  for (const requiredFile of [
    'dist/index.js',
    'dist/index.cjs',
    'dist/authoring.js',
    'dist/authoring.cjs',
    'dist/workspace.js',
    'dist/workspace.cjs',
    'dist/types/package_core.d.ts',
    'dist/types/package_core.d.ts.map',
    'dist/types/package_authoring.d.ts',
    'dist/types/package_authoring.d.ts.map',
    'dist/types/package_workspace.d.ts',
    'dist/types/package_workspace.d.ts.map',
    'dist/types/package.json',
    'LICENSE',
    'README.md',
    'package.json',
  ]) {
    assert.equal(
      packedFiles.has(requiredFile),
      true,
      `packed package is missing ${requiredFile}`,
    );
  }
  const forbiddenDeclaration = new RegExp(
    '^dist/types/(?:surface|elaborator|lf_remote_workspace|' +
      'lf_transfer_acquisition|[^/]*_cli)\\.d\\.ts$',
    'u',
  );
  for (const file of packedFiles) {
    assert.equal(
      /^(?:scripts|src)\//u.test(file) || file.endsWith('package-lock.json'),
      false,
      `packed package leaked contributor input ${file}`,
    );
    assert.equal(
      forbiddenDeclaration.test(file),
      false,
      `packed package leaked forbidden declaration ${file}`,
    );
  }
  const tarball = path.resolve(
    tarballDirectory,
    packedRecord.filename ?? packedRecord.path,
  );

  await writeFile(
    path.join(consumerDirectory, 'package.json'),
    `${JSON.stringify({
      name: 'emdash-packed-install-smoke',
      private: true,
      type: 'module',
    }, null, 2)}\n`,
  );
  run(
    pnpmWrapper,
    [
      '--dir',
      consumerDirectory,
      'add',
      '--ignore-scripts',
      '--offline',
      tarball,
    ],
    repositoryRoot,
  );

  const installedRoot = path.join(
    consumerDirectory,
    'node_modules',
    '@hotdocx',
    'emdash',
  );
  const installedManifest = JSON.parse(
    await readFile(path.join(installedRoot, 'package.json'), 'utf8'),
  );
  assert.equal(installedManifest.name, '@hotdocx/emdash');
  assert.equal(installedManifest.version, '0.1.0');
  assert.equal(
    installedManifest.scripts,
    undefined,
    'published package must not retain contributor-only scripts',
  );
  assert.deepEqual(
    Object.keys(installedManifest.exports),
    ['.', './authoring', './workspace', './package.json'],
  );
  assert.equal(installedManifest.dependencies, undefined);
  assert.equal(
    JSON.parse(
      await readFile(
        path.join(installedRoot, 'dist', 'types', 'package.json'),
        'utf8',
      ),
    ).type,
    'commonjs',
  );

  await writeFile(
    path.join(consumerDirectory, 'consumer.mjs'),
    `import assert from 'node:assert/strict';
import { CoreChecker, CORE_MVP_MANIFEST } from '@hotdocx/emdash';
import {
  CORE_LF_INSTANCE_SCOPE_PROFILE,
  CoreLfScopedBuilder,
} from '@hotdocx/emdash/authoring';
import {
  CORE_LF_DECLARATION_WORKSPACE_PROFILE,
} from '@hotdocx/emdash/workspace';

assert.equal(typeof CoreChecker, 'function');
assert.equal(typeof CoreLfScopedBuilder, 'function');
assert.equal(CORE_MVP_MANIFEST.status, 'frozen-reviewed');
assert.equal(
  CORE_LF_INSTANCE_SCOPE_PROFILE.productionLambdapiDependency,
  false,
);
assert.equal(
  CORE_LF_DECLARATION_WORKSPACE_PROFILE.nodeBuiltinDependency,
  false,
);
`,
  );
  await writeFile(
    path.join(consumerDirectory, 'consumer.cjs'),
    `const assert = require('node:assert/strict');
const core = require('@hotdocx/emdash');
const authoring = require('@hotdocx/emdash/authoring');
const workspace = require('@hotdocx/emdash/workspace');

assert.equal(typeof core.CoreChecker, 'function');
assert.equal(typeof authoring.CoreLfScopedBuilder, 'function');
assert.equal(
  workspace.CORE_LF_DECLARATION_WORKSPACE_PROFILE.nodeBuiltinDependency,
  false,
);
`,
  );
  await writeFile(
    path.join(consumerDirectory, 'consumer.ts'),
    `import {
  CORE_MVP_MANIFEST,
  CoreChecker,
  type KernelExpression,
} from '@hotdocx/emdash';
import {
  CORE_LF_INSTANCE_SCOPE_PROFILE,
  CoreLfScopedBuilder,
} from '@hotdocx/emdash/authoring';
import {
  CORE_LF_DECLARATION_WORKSPACE_PROFILE,
} from '@hotdocx/emdash/workspace';

const checkerConstructor: typeof CoreChecker = CoreChecker;
const builder = new CoreLfScopedBuilder();
const maybeTerm: KernelExpression | undefined = undefined;
void checkerConstructor;
void builder;
void maybeTerm;
void CORE_MVP_MANIFEST;
void CORE_LF_INSTANCE_SCOPE_PROFILE;
void CORE_LF_DECLARATION_WORKSPACE_PROFILE;
`,
  );
  await writeFile(
    path.join(consumerDirectory, 'browser-entry.js'),
    `import { CoreChecker } from '@hotdocx/emdash';
import { CoreLfScopedBuilder } from '@hotdocx/emdash/authoring';
import {
  CORE_LF_DECLARATION_WORKSPACE_PROFILE,
} from '@hotdocx/emdash/workspace';

globalThis.emdashPackedSmoke = {
  CoreChecker,
  CoreLfScopedBuilder,
  workspaceRevision: CORE_LF_DECLARATION_WORKSPACE_PROFILE.revision,
};
`,
  );

  run(process.execPath, ['consumer.mjs'], consumerDirectory);
  run(process.execPath, ['consumer.cjs'], consumerDirectory);
  run(
    path.join(repositoryRoot, 'node_modules', '.bin', 'tsc'),
    [
      '--noEmit',
      '--strict',
      '--target',
      'ES2020',
      '--module',
      'NodeNext',
      '--moduleResolution',
      'NodeNext',
      'consumer.ts',
    ],
    consumerDirectory,
  );
  run(
    path.join(packageRoot, 'node_modules', '.bin', 'esbuild'),
    [
      'browser-entry.js',
      '--bundle',
      '--format=esm',
      '--platform=browser',
      '--target=es2020',
      '--outfile=browser-bundle.js',
    ],
    consumerDirectory,
  );

  console.log('Packed @hotdocx/emdash install verified.');
} finally {
  await rm(temporaryRoot, { recursive: true, force: true });
}
