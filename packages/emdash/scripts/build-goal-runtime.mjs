import { build } from 'esbuild';
import ts from 'typescript';
import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { createHash } from 'node:crypto';
import { execFileSync } from 'node:child_process';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const repositoryRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../../..');
const args = process.argv.slice(2);
if (args.length && (args.length !== 2 || args[0] !== '--out')) throw new Error('Usage: build-goal-runtime.mjs [--out DIRECTORY]');
const output = args.length ? path.resolve(args[1]) : path.join(repositoryRoot, 'plugins/emdash/dist');
await mkdir(output, { recursive: true });
const bundled = await build({
  absWorkingDir: repositoryRoot,
  entryPoints: {
    'emdash-agent': 'examples/v3_2_algebra_goal_cli.ts',
    authoring: 'src/v3_2/algebra_goal_authoring.ts',
  },
  outdir: output, outExtension: { '.js': '.cjs' },
  bundle: true, platform: 'node', format: 'cjs', target: 'node20',
  metafile: true, logLevel: 'info',
});
const base = ts.readConfigFile(path.join(repositoryRoot, 'tsconfig.json'), ts.sys.readFile);
if (base.error) throw new Error(ts.flattenDiagnosticMessageText(base.error.messageText, '\n'));
const parsed = ts.parseJsonConfigFileContent(base.config, ts.sys, repositoryRoot);
const program = ts.createProgram([path.join(repositoryRoot, 'src/v3_2/algebra_goal_authoring.ts')], {
  ...parsed.options, noEmit: false, declaration: true, declarationMap: false,
  emitDeclarationOnly: true, rootDir: path.join(repositoryRoot, 'src/v3_2'), outDir: path.join(output, 'types'),
});
const diagnostics = ts.getPreEmitDiagnostics(program);
if (diagnostics.length) throw new Error(ts.formatDiagnosticsWithColorAndContext(diagnostics, {
  getCanonicalFileName: p => p, getCurrentDirectory: () => repositoryRoot, getNewLine: () => '\n',
}));
if (program.emit().emitSkipped) throw new Error('Authoring declaration emit failed');
await writeFile(path.join(output, 'types/package.json'), '{"type":"commonjs"}\n');
await writeFile(path.join(output, 'authoring.d.cts'), "export * from './types/algebra_goal_authoring';\n");
const sha256 = bytes => createHash('sha256').update(bytes).digest('hex');
const inputs = {};
for (const name of Object.keys(bundled.metafile.inputs).filter(n => n.startsWith('src/') || n.startsWith('examples/')).sort()) {
  inputs[name] = sha256(await readFile(path.join(repositoryRoot, name)));
}
const bundles = {};
for (const name of ['emdash-agent.cjs', 'authoring.cjs']) bundles[name] = sha256(await readFile(path.join(output, name)));
await writeFile(path.join(output, 'build.json'), JSON.stringify({
  revision: 'emdash-goal-runtime-build-v1',
  checkoutHead: execFileSync('git', ['rev-parse', 'HEAD'], { cwd: repositoryRoot, encoding: 'utf8' }).trim(),
  inputs, bundles,
}, null, 2) + '\n');
console.log(`Portable goal runtime: ${output}`);
