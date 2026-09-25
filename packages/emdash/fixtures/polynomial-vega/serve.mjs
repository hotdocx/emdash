import { createServer } from 'node:http';
import { readFile } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';

const port = Number(process.argv[2] ?? 4178);
if (!Number.isInteger(port) || port < 0 || port > 65535) throw new Error('Invalid port');
const files = new Map([
  ['/', ['index.html', 'text/html; charset=utf-8']],
  ['/app.js', ['app.js', 'text/javascript; charset=utf-8']],
  ['/app.js.map', ['app.js.map', 'application/json']],
]);
const server = createServer(async (request, response) => {
  if (request.method !== 'GET') { response.writeHead(405); response.end(); return; }
  if (request.url === '/favicon.ico') { response.writeHead(204); response.end(); return; }
  const selected = files.get(request.url);
  if (!selected) { response.writeHead(404); response.end('Not found'); return; }
  try {
    const data = await readFile(fileURLToPath(new URL(`dist/${selected[0]}`, import.meta.url)));
    response.writeHead(200, { 'Content-Type': selected[1], 'Cache-Control': 'no-store' });
    response.end(data);
  } catch { response.writeHead(500); response.end('Build the example before serving it.'); }
});
server.listen(port, '127.0.0.1', () => console.log(`Polynomial explorer: http://127.0.0.1:${server.address().port}`));
process.on('SIGINT', () => server.close());
process.on('SIGTERM', () => server.close());
