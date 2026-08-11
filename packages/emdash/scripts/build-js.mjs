import { mkdir, rm, writeFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import { build } from 'esbuild';

const packageRoot = path.resolve(
  path.dirname(fileURLToPath(import.meta.url)),
  '..',
);
const repositoryRoot = path.resolve(packageRoot, '..', '..');
const distDirectory = path.resolve(packageRoot, 'dist');

if (path.relative(packageRoot, distDirectory) !== 'dist') {
  throw new Error(`Refusing to clean unexpected output path ${distDirectory}`);
}

const entryPoints = {
  index: path.join(repositoryRoot, 'src/v3_2/package_core.ts'),
  authoring: path.join(repositoryRoot, 'src/v3_2/package_authoring.ts'),
  workspace: path.join(repositoryRoot, 'src/v3_2/package_workspace.ts'),
  benchmark: path.join(repositoryRoot, 'src/v3_2/package_benchmark.ts'),
};

await rm(distDirectory, { recursive: true, force: true });

const shared = {
  absWorkingDir: repositoryRoot,
  bundle: true,
  entryPoints,
  logLevel: 'info',
  platform: 'browser',
  sourcemap: true,
  sourcesContent: true,
  target: 'es2020',
};

await build({
  ...shared,
  chunkNames: 'chunks/[name]-[hash]',
  entryNames: '[name]',
  format: 'esm',
  outdir: distDirectory,
  splitting: true,
});

await build({
  ...shared,
  entryNames: '[name]',
  format: 'cjs',
  outExtension: { '.js': '.cjs' },
  outdir: distDirectory,
  splitting: false,
});

const typeDirectory = path.join(distDirectory, 'types');
await mkdir(typeDirectory, { recursive: true });
// The canonical source graph uses extensionless CommonJS-shaped imports.
// Keep that complete declaration closure under a local module marker while
// the public runtime continues to offer both explicit ESM and CJS conditions.
await writeFile(
  path.join(typeDirectory, 'package.json'),
  `${JSON.stringify({ type: 'commonjs' }, null, 2)}\n`,
);
