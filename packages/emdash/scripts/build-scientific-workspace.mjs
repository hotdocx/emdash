import { build, version as esbuildVersion } from 'esbuild';
import ts from 'typescript';
import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { createHash } from 'node:crypto';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../../..');
const args = process.argv.slice(2);
let output = path.join(root, 'packages/emdash/dist-scientific-workspace');
let nodeVersion = 'v22.23.2';
for (let index = 0; index < args.length; index += 2) {
  if (args[index] === '--out' && args[index + 1]) output = path.resolve(args[index + 1]);
  else if (args[index] === '--node-version' && /^v(?:22|24)\.\d+\.\d+$/.test(args[index + 1] ?? '')) nodeVersion = args[index + 1];
  else throw new Error('Usage: build-scientific-workspace.mjs [--out DIRECTORY] [--node-version v22.x.y|v24.x.y]');
}
await fs.mkdir(output, { recursive: true });
if ((await fs.readdir(output)).length) throw new Error('Build into an empty artifact directory.');
const vendor = path.join(output, 'vendor');
await fs.mkdir(vendor);
const bundled = await build({
  absWorkingDir: root, entryPoints: ['src/v3_2/scientific_program.ts'], outfile: path.join(vendor, 'emdash.mjs'),
  bundle: true, platform: 'node', format: 'esm', target: 'node22', metafile: true, logLevel: 'info',
});
const base = ts.readConfigFile(path.join(root, 'tsconfig.json'), ts.sys.readFile);
if (base.error) throw new Error(ts.flattenDiagnosticMessageText(base.error.messageText, '\n'));
const parsed = ts.parseJsonConfigFileContent(base.config, ts.sys, root);
const program = ts.createProgram([path.join(root, 'src/v3_2/scientific_program.ts')], {
  ...parsed.options, noEmit: false, declaration: true, declarationMap: false,
  types: ['node'], typeRoots: [path.join(root, 'node_modules/@types')],
  emitDeclarationOnly: true, rootDir: path.join(root, 'src/v3_2'), outDir: path.join(vendor, 'types'),
});
const diagnostics = ts.getPreEmitDiagnostics(program);
if (diagnostics.length) throw new Error(ts.formatDiagnosticsWithColorAndContext(diagnostics, {
  getCanonicalFileName: p => p, getCurrentDirectory: () => root, getNewLine: () => '\n',
}));
if (program.emit().emitSkipped) throw new Error('Scientific declaration emit failed.');
await fs.writeFile(path.join(vendor, 'types/package.json'), '{"type":"commonjs"}\n');
await fs.writeFile(path.join(vendor, 'emdash.d.mts'), "export * from './types/scientific_program.js';\n");
const hash = bytes => createHash('sha256').update(bytes).digest('hex');
const inputs = {};
for (const filename of Object.keys(bundled.metafile.inputs).sort()) inputs[filename] = hash(await fs.readFile(path.join(root, filename)));
const receipt = { revision: 'emdash-scientific-runtime-v1',
  emdashVersion: JSON.parse(await fs.readFile(path.join(root, 'packages/emdash/package.json'), 'utf8')).version,
  toolchain: { esbuild: esbuildVersion, typescript: ts.version }, inputs,
  bundles: { 'emdash.mjs': hash(await fs.readFile(path.join(vendor, 'emdash.mjs'))) } };
await fs.writeFile(path.join(vendor, 'build.json'), JSON.stringify(receipt, null, 2) + '\n');
await fs.copyFile(path.join(root, 'packages/emdash/LICENSE'), path.join(vendor, 'LICENSE'));
for (const filename of ['compute.ts', 'reuse.ts', 'study.ts', 'run-local.mjs', 'replay.mjs', 'server.mjs', 'index.html', 'workbench.js', 'workbench.css', 'README.md']) {
  await fs.copyFile(path.join(root, 'packages/emdash/fixtures/scientific-workspace', filename), path.join(output, filename));
}
const library = await import(pathToFileURL(path.join(vendor, 'emdash.mjs')).href);
await fs.writeFile(path.join(output, 'package.json'), JSON.stringify({
  name: 'emdash-scientific-workspace', private: true, type: 'module', engines: { node: nodeVersion.slice(1) },
  scripts: { start: 'node server.mjs', compute: 'node run-local.mjs compute', reuse: 'node run-local.mjs reuse' },
}, null, 2) + '\n');
const source = { ...library.createAlgebraGoalExampleSource(), title: 'A polynomial relation' };
await fs.writeFile(path.join(output, 'input.json'), JSON.stringify(source, null, 2) + '\n');
await fs.writeFile(path.join(output, 'retained.json'), JSON.stringify(library.computeAlgebraGoal(source), null, 2) + '\n');
const manifest = { version: 1, runtime: { kind: 'node-strip-types', node: nodeVersion },
  files: ['package.json', 'compute.ts', 'reuse.ts', 'study.ts', 'input.json', 'retained.json', 'vendor/emdash.mjs', 'vendor/build.json'],
  tasks: { compute: { entrypoint: 'compute.ts' }, reuse: { entrypoint: 'reuse.ts' } } };
await fs.writeFile(path.join(output, 'workspace.program.json'), JSON.stringify(manifest, null, 2) + '\n');
console.log('Portable scientific workspace: ' + output);
