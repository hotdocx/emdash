import { build } from 'esbuild';
import { copyFile, mkdir, writeFile } from 'node:fs/promises';

await mkdir('dist', { recursive: true });
const browser = await build({
  entryPoints: ['main.ts'], outfile: 'dist/app.js', bundle: true,
  platform: 'browser', format: 'esm', target: 'es2020',
  sourcemap: true, metafile: true, logLevel: 'info',
});
await writeFile('dist/browser-meta.json', JSON.stringify(browser.metafile, null, 2) + '\n');
await copyFile('index.html', 'dist/index.html');
await build({
  entryPoints: ['model.ts', 'plot-slot.ts'], outdir: 'dist', outExtension: { '.js': '.mjs' },
  bundle: true, packages: 'external', platform: 'node', format: 'esm', target: 'es2020',
});
