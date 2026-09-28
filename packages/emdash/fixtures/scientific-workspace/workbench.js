const $ = id => document.getElementById(id);
const terminal = state => ['succeeded', 'failed', 'cancelled', 'interrupted'].includes(state);
const text = (id, value) => { $(id).textContent = value; };
const pretty = value => String(value).replaceAll(' + -', ' − ').replaceAll('*', '·').replace(/\^(\d+)/g, (_, n) => [...n].map(d => '⁰¹²³⁴⁵⁶⁷⁸⁹'[Number(d)]).join(''));
let context, inspection, current, result, plotUrl, busy = false, local = false, pollVersion = 0, followLatest = true;
const drafts = new Map();
let fileName = '', fileHash = '', fileOriginal = '', sourceSequence = 0, sourceLoading = false, sourceReady = false;
const encoder = new TextEncoder(); const decoder = new TextDecoder();
const storageKey = suffix => `emdash:${context?.session.postId}:${context?.viewer?.id ?? ''}:${suffix}`;
function notice(message = '', error = false) { text('notice', message); $('notice').hidden = !message; $('notice').classList.toggle('error', error); }
function controls() {
  $('run').disabled = local || busy || drafts.size > 0 || !inspection?.runtimeMatches;
  $('reuse').disabled = local || busy || drafts.size > 0 || !result?.exact?.member || !current || current.state !== 'succeeded';
  $('save').disabled = local || busy || sourceLoading || !sourceReady || !drafts.has(fileName);
  $('cancel').hidden = !busy || !current || terminal(current.state);
  $('export').disabled = local || !current || !terminal(current.state) || !current.result?.program;
}
async function rpc(operation, input = {}) {
  const response = await fetch('/__gp/workspace-executions', { method: 'POST', credentials: 'same-origin', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({ operation, ...input }) });
  const body = await response.json().catch(() => ({ error: 'The workspace connection did not return a result.' }));
  if (!response.ok || body.ok === false) { const error = new Error(body.error || 'Workspace request failed.'); error.status = response.status; throw error; }
  return body;
}
function join(parts) { const total = parts.reduce((sum, part) => sum + part.length, 0); const bytes = new Uint8Array(total); let offset = 0; for (const part of parts) { bytes.set(part, offset); offset += part.length; } return bytes; }
async function fileBytes(operation, input) {
  let offset = 0, digest, total; const parts = [];
  for (let chunk = 0; chunk < 33; chunk++) {
    const { file } = await rpc(operation, { ...input, offset, ...(operation === 'readFile' && digest ? { expectedHash: digest } : {}) });
    if (digest && file.sha256 !== digest) throw new Error('This file changed while it was being read. Refresh it before continuing.');
    digest = file.sha256; total = file.totalBytes;
    parts.push(Uint8Array.from(atob(file.contentBase64), c => c.charCodeAt(0)));
    if (file.nextOffset === null) {
      const bytes = join(parts);
      if (bytes.length !== total) throw new Error('Incomplete file transfer.');
      const actual = [...new Uint8Array(await crypto.subtle.digest('SHA-256', bytes))].map(n => n.toString(16).padStart(2, '0')).join('');
      if (actual !== digest) throw new Error('File integrity check failed.');
      return { bytes, hash: digest };
    }
    if (file.nextOffset <= offset) throw new Error('Invalid file cursor.'); offset = file.nextOffset;
  }
  throw new Error('File exceeded the bounded transfer size.');
}
async function artifact(name, executionId = current.executionId) { return (await fileBytes('executionFile', { executionId, area: 'artifacts', path: name })).bytes; }
function polynomial(value, variables) {
  return value.terms.map(term => {
    const monomial = variables.map((v, i) => term.exponents[i] === '0' ? '' : v + (term.exponents[i] === '1' ? '' : '^' + term.exponents[i])).filter(Boolean).join('*');
    return monomial ? `${term.coefficient}*${monomial}` : term.coefficient;
  }).join(' + ') || '0';
}
function inputView(source) {
  if (!source?.ring || !Array.isArray(source.generators)) return;
  text('title', source.title || 'A polynomial relation'); text('ring', `ℚ[${source.ring.variables.join(', ')}]`);
  $('equations').replaceChildren();
  for (const [index, value] of [...source.generators, source.query].entries()) {
    const row = document.createElement('div'); if (index === source.generators.length) row.className = 'query';
    const label = document.createElement('span'); label.className = 'symbol'; label.textContent = value.name;
    const equation = document.createElement('span'); equation.textContent = '= ' + pretty(polynomial(value, source.ring.variables)); row.append(label, equation); $('equations').append(row);
  }
}
function resultView(value, plot) {
  result = value; $('result-empty').hidden = Boolean(value); $('result-body').hidden = !value;
  $('plot').hidden = !plot; $('plot-empty').hidden = Boolean(plot);
  if (plotUrl) URL.revokeObjectURL(plotUrl);
  if (plot) { plotUrl = URL.createObjectURL(new Blob([plot], { type: 'image/svg+xml' })); $('plot').src = plotUrl; }
  if (!value) { controls(); return; }
  if (!value.exact) { text('membership', 'Program result'); text('relation', JSON.stringify(value)); text('complex', ''); text('column', ''); text('native-note', ''); }
  else {
    text('membership', value.exact.member ? '✓ The query belongs to the ideal' : 'The query is outside this ideal');
    text('relation', value.exact.member ? `${pretty(value.exact.query)} = ${value.exact.coefficients.map((c, i) => `(${pretty(c)}) · (${pretty(value.exact.generators[i])})`).join(' + ')}` : 'A nonzero remainder was retained with this run.');
    text('complex', value.native ? value.native.ranks.map(rank => rank === 1 ? 'R' : `R${[...String(rank)].map(d => '⁰¹²³⁴⁵⁶⁷⁸⁹'[Number(d)]).join('')}`).join('  ←  ') : 'No relation complex');
    text('column', value.native ? `s(1) = (${value.native.imageOfOne.map(pretty).join(', ')})` : '');
    text('native-note', value.native ? 'D ∘ s = 0, checked by exact arithmetic. This does not assert exactness of the complex.' : 'The exact remainder and curve view remain available.');
  }
  $('internal-result').hidden = !value.internal;
  if (value.internal) text('internal-result', `Core construction and action types checked with ${value.internal.adoptedEquationCount} explicit computed-equation assumption. ${value.internal.adoptionReason}`);
  controls();
}
function freshness() {
  const revision = current?.result?.program?.sourceRevision;
  text('freshness', revision ? revision === inspection?.revision ? 'Matches current source' : 'Earlier source · retained result' : 'No completed run selected');
}
async function inspect() {
  inspection = (await rpc('inspect')).program;
  const previousTask = $('task').value;
  $('task').replaceChildren(...Object.keys(inspection.manifest.tasks).map(name => { const option = document.createElement('option'); option.value = name; option.textContent = name; return option; }));
  if (Object.hasOwn(inspection.manifest.tasks, previousTask)) $('task').value = previousTask;
  const sources = ['workspace.program.json', ...inspection.manifest.files.filter(name => !name.startsWith('vendor/'))];
  const selected = sources.includes(fileName) ? fileName : sources.includes('input.json') ? 'input.json' : sources[0];
  $('source-file').replaceChildren(...sources.map(name => { const option = document.createElement('option'); option.value = name; option.textContent = name; return option; }));
  $('source-file').value = selected;
  try { inputView(JSON.parse(decoder.decode((await fileBytes('readFile', { path: 'input.json' })).bytes))); } catch { /* Custom projects can supply other inputs. */ }
  await loadSource(selected); freshness(); controls();
}
async function loadSource(name) {
  const sequence = ++sourceSequence;
  fileName = name; sourceLoading = true; sourceReady = false; $('source').disabled = true; text('source-state', 'Loading…'); controls();
  try {
    let draft = drafts.get(name);
    if (!draft) { const file = await fileBytes('readFile', { path: name }); draft = { hash: file.hash, original: decoder.decode(file.bytes), text: decoder.decode(file.bytes) }; }
    if (sequence !== sourceSequence) return;
    fileHash = draft.hash; fileOriginal = draft.original; $('source').value = draft.text; sourceReady = true;
    text('source-state', drafts.has(name) ? 'Unsaved changes' : 'Saved');
  } finally {
    if (sequence === sourceSequence) { sourceLoading = false; $('source').disabled = local || !sourceReady; if (!sourceReady) text('source-state', 'Unavailable'); controls(); }
  }
}
async function historyList() {
  const rows = (await rpc('list')).executions.filter(row => row.kind === 'program');
  $('history').replaceChildren();
  if (!rows.length) { const p = document.createElement('p'); p.className = 'muted'; p.textContent = 'No computations yet.'; $('history').append(p); }
  for (const row of rows) {
    const button = document.createElement('button'); button.setAttribute('aria-pressed', String(row.executionId === current?.executionId));
    button.textContent = `${row.task || 'Program'} · ${new Date(row.acceptedAt).toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' })}`;
    const small = document.createElement('small'); small.textContent = row.state; button.append(small);
    button.addEventListener('click', () => perform(() => { followLatest = false; return select(row.executionId); })); $('history').append(button);
  }
  return rows;
}
async function select(id) {
  const version = ++pollVersion;
  current = (await rpc('read', { executionId: id })).execution;
  localStorage.setItem(storageKey('selected'), id); history.replaceState(null, '', '#run=' + encodeURIComponent(id));
  await showExecution(); await historyList();
  if (!terminal(current.state)) void poll(id, version);
}
async function showExecution() {
  const execution = current, selectionVersion = pollVersion;
  busy = !terminal(current.state); text('state', current.state); $('state').classList.toggle('running', busy);
  text('details', JSON.stringify({ ...current, output: undefined, result: current.result ? { ...current.result, summary: undefined } : null }, null, 2));
  text('log', current.output.map(chunk => chunk.text).join(''));
  if (terminal(current.state)) {
    const files = current.result?.program?.artifacts ?? [];
    const value = files.some(file => file.path === 'result.json') ? JSON.parse(decoder.decode(await artifact('result.json', execution.executionId))) : null;
    const plot = files.some(file => file.path === 'plot.svg') ? decoder.decode(await artifact('plot.svg', execution.executionId)) : null;
    if (selectionVersion !== pollVersion) return;
    resultView(value, plot); freshness();
    if (current.state !== 'succeeded') notice(current.error?.message || `This run is ${current.state}. Its captured source remains available.`, current.state === 'failed');
  } else { resultView(null, null); text('freshness', 'Computing captured source…'); }
  controls();
}
async function poll(id, version) {
  while (version === pollVersion) {
    await new Promise(resolve => setTimeout(resolve, 600));
    try {
      const next = (await rpc('read', { executionId: id })).execution;
      if (version !== pollVersion) return; current = next; await showExecution();
      if (terminal(next.state)) { await inspect(); await historyList(); return; }
    } catch (error) { notice(error.message + ' The run remains identified; refresh to reconnect.', true); return; }
  }
}
async function start(task = $('task').value, pending) {
  followLatest = true;
  if (drafts.size) throw new Error('Save your source changes before running.');
  await inspect();
  const parameters = $('internal').checked ? { internal: true, adoptionReason: $('reason').value.trim() } : {};
  if (parameters.internal && !parameters.adoptionReason) throw new Error('Supply the explicit adoption reason.');
  const request = pending ?? { idempotencyKey: crypto.randomUUID(), input: { kind: 'program', manifestPath: inspection.manifestPath, task, parameters, expectedRevision: inspection.revision } };
  const pendingKey = storageKey('pending:' + context.session.sessionId);
  localStorage.setItem(pendingKey, JSON.stringify(request)); busy = true; controls(); notice('Starting the captured program…');
  try {
    const accepted = await rpc('start', request);
    localStorage.removeItem(pendingKey); notice(accepted.synchronized ? '' : 'The start is recorded. Waiting for controller confirmation.');
    await select(accepted.execution.executionId);
  } catch (error) {
    busy = false; controls();
    if (error.status >= 400 && error.status < 500 && ![408, 429].includes(error.status)) localStorage.removeItem(pendingKey);
    throw error;
  }
}
async function reuse() {
  const retained = decoder.decode(await artifact('retained.json'));
  const original = await fileBytes('readFile', { path: 'retained.json' });
  await rpc('writeFile', { path: 'retained.json', content: retained, expectedHash: original.hash });
  await start('reuse');
}
async function perform(action) { try { notice(); await action(); } catch (error) { notice(error.message, true); if (!inspection && !local) text('state', 'Unavailable'); } }
$('source').addEventListener('input', () => { if ($('source').value === fileOriginal) drafts.delete(fileName); else drafts.set(fileName, { hash: fileHash, original: fileOriginal, text: $('source').value }); text('source-state', drafts.has(fileName) ? 'Unsaved changes' : 'Saved'); controls(); });
$('source-file').addEventListener('change', () => perform(() => loadSource($('source-file').value)));
$('save').addEventListener('click', () => perform(async () => { const name = fileName, draft = drafts.get(name); await rpc('writeFile', { path: name, content: draft.text, expectedHash: draft.hash }); drafts.delete(name); await inspect(); notice('Source saved. Run the program to compute from this revision.'); }));
$('run').addEventListener('click', () => perform(() => start(undefined, JSON.parse(localStorage.getItem(storageKey('pending:' + context.session.sessionId)) || 'null'))));
$('reuse').addEventListener('click', () => perform(reuse));
$('cancel').addEventListener('click', () => perform(async () => { await rpc('cancel', { executionId: current.executionId }); await select(current.executionId); }));
$('refresh').addEventListener('click', () => perform(() => { followLatest = true; return boot(); }));
$('zoom').addEventListener('input', () => { $('plot').style.width = $('zoom').value + '%'; text('zoom-value', $('zoom').value + '%'); });

// A stored ZIP keeps the export dependency-free; every source/artifact was
// already checked against its gateway-provided SHA-256 before packaging.
function zip(files) {
  let offset = 0; const localParts = [], directory = [];
  const crc = bytes => { let value = -1; for (const byte of bytes) { value ^= byte; for (let bit = 0; bit < 8; bit++) value = (value >>> 1) ^ (0xedb88320 & -(value & 1)); } return (value ^ -1) >>> 0; };
  for (const [path, bytes] of files) {
    const name = encoder.encode(path), sum = crc(bytes); const head = new Uint8Array(30 + name.length), view = new DataView(head.buffer);
    view.setUint32(0, 0x04034b50, true); view.setUint16(4, 20, true); view.setUint16(6, 0x800, true); view.setUint16(12, 33, true); view.setUint32(14, sum, true); view.setUint32(18, bytes.length, true); view.setUint32(22, bytes.length, true); view.setUint16(26, name.length, true); head.set(name, 30);
    const entry = new Uint8Array(46 + name.length), e = new DataView(entry.buffer);
    e.setUint32(0, 0x02014b50, true); e.setUint16(4, 20, true); e.setUint16(6, 20, true); e.setUint16(8, 0x800, true); e.setUint16(14, 33, true); e.setUint32(16, sum, true); e.setUint32(20, bytes.length, true); e.setUint32(24, bytes.length, true); e.setUint16(28, name.length, true); e.setUint32(42, offset, true); entry.set(name, 46);
    localParts.push(head, bytes); directory.push(entry); offset += head.length + bytes.length;
  }
  const end = new Uint8Array(22), e = new DataView(end.buffer); e.setUint32(0, 0x06054b50, true); e.setUint16(8, files.length, true); e.setUint16(10, files.length, true); e.setUint32(12, directory.reduce((n, item) => n + item.length, 0), true); e.setUint32(16, offset, true);
  return new Blob([...localParts, ...directory, end], { type: 'application/zip' });
}
$('export').addEventListener('click', () => perform(async () => {
  const execution = current;
  const metadata = JSON.parse(decoder.decode((await fileBytes('executionFile', { executionId: execution.executionId, area: 'metadata', path: 'request.json' })).bytes));
  const files = [['request.json', encoder.encode(JSON.stringify({ input: metadata.input, nodeVersion: metadata.nodeVersion, files: metadata.files }, null, 2))]];
  for (const file of metadata.files) { notice(`Collecting source: ${file.path}`); files.push(['source/' + file.path, (await fileBytes('executionFile', { executionId: execution.executionId, area: 'source', path: file.path })).bytes]); }
  for (const file of execution.result.program.artifacts) { notice(`Collecting result: ${file.path}`); files.push(['artifacts/' + file.path, (await fileBytes('executionFile', { executionId: execution.executionId, area: 'artifacts', path: file.path })).bytes]); }
  files.push(['replay.mjs', encoder.encode(await (await fetch('/replay.mjs')).text())]);
  files.push(['README.txt', encoder.encode(`Emdash captured scientific run\n\nUse Node ${metadata.nodeVersion}, then run: node replay.mjs\nSource and parameters are captured; artifacts/ contains the earlier result.\nExternal inputs are outside this declared snapshot.\n`)]);
  const url = URL.createObjectURL(zip(files)); const link = document.createElement('a'); link.href = url; link.download = 'emdash-scientific-run.zip'; link.click(); setTimeout(() => URL.revokeObjectURL(url), 10000); notice('Exported captured source, parameters, runtime pins and results.');
}));

async function boot() {
  ++pollVersion;
  const response = await fetch('/__gp/context');
  if (!response.ok) {
    const localResponse = await fetch('/api/local-view');
    if (!localResponse.ok) throw new Error('Open this view from an authenticated workspace preview.');
    const view = await localResponse.json(); local = true; inputView(view.source); resultView(view.result, view.plot);
    text('connection', 'Local result view'); text('state', 'Local'); text('freshness', 'Retained local result'); notice('Use the local Emdash program to compute, then refresh this view.'); controls(); return;
  }
  context = await response.json(); local = false; text('connection', 'Cloud workspace');
  await inspect(); const rows = await historyList();
  const selected = new URLSearchParams(location.hash.slice(1)).get('run') || localStorage.getItem(storageKey('selected')) || rows[0]?.executionId;
  if (selected) await select(selected); else { current = null; busy = false; text('state', 'Ready'); controls(); }
  if (localStorage.getItem(storageKey('pending:' + context.session.sessionId))) notice('A previous start needs reconciliation. Run again to retry that same request.');
}
void perform(boot);
let refreshing = false;
setInterval(async () => {
  if (!context || local || busy || drafts.size || refreshing) return;
  refreshing = true;
  try { const rows = await historyList(); if (followLatest && rows[0] && rows[0].executionId !== current?.executionId) await select(rows[0].executionId); }
  catch { /* An explicit refresh reports connection errors without repeating notices. */ }
  finally { refreshing = false; }
}, 3000);
