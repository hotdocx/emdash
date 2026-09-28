import http from 'node:http';
import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const root = path.dirname(fileURLToPath(import.meta.url));
const assets = new Map([['/', ['index.html', 'text/html']], ['/workbench.js', ['workbench.js', 'text/javascript']], ['/workbench.css', ['workbench.css', 'text/css']], ['/replay.mjs', ['replay.mjs', 'text/javascript']]]);
const server = http.createServer(async (req, res) => {
  const url = new URL(req.url ?? '/', 'http://workspace');
  if (req.method !== 'GET') { res.writeHead(405); res.end(); return; }
  try {
    if (url.pathname === '/api/local-view' && process.env.EMDASH_LOCAL_VIEW === '1') {
      const source = JSON.parse(await fs.readFile(path.join(root, 'input.json'), 'utf8'));
      const result = await fs.readFile(path.join(root, 'results/result.json'), 'utf8').then(JSON.parse).catch(() => null);
      const plot = result?.view?.artifact === 'plot.svg'
        ? await fs.readFile(path.join(root, 'results/plot.svg'), 'utf8').catch(() => null) : null;
      res.writeHead(200, { 'Content-Type': 'application/json', 'Cache-Control': 'no-store' });
      res.end(JSON.stringify({ ok: true, source, result, plot })); return;
    }
    const asset = assets.get(url.pathname);
    if (!asset) { res.writeHead(404); res.end(); return; }
    res.writeHead(200, {
      'Content-Type': asset[1] + '; charset=utf-8', 'Cache-Control': 'no-store', 'X-Content-Type-Options': 'nosniff',
      'Content-Security-Policy': "default-src 'self'; script-src 'self'; style-src 'self' 'unsafe-inline'; img-src 'self' data: blob:; connect-src 'self'; base-uri 'none'",
    });
    res.end(await fs.readFile(path.join(root, asset[0])));
  } catch { res.writeHead(500); res.end('Workspace view unavailable.'); }
});
const port = Number(process.env.PORT ?? 4173);
server.listen(port, process.env.HOST ?? '127.0.0.1', () => console.log(`Emdash scientific view listening on ${port}`));
