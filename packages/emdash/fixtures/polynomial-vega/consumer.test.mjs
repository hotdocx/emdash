import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import test from 'node:test';
import { View, parse } from 'vega';
import { compile } from 'vega-lite';
import { calculateFamily, sampleFamily, curveSpec, viewports } from './dist/model.mjs';
import { createPlotSlot } from './dist/plot-slot.mjs';

test('the packed mathematical source supplies exact arithmetic and actual Vega-Lite rows', async () => {
  const calculation = calculateFamily('2/4');
  assert.equal(calculation.parameter, '1/2');
  const samples = sampleFamily(calculation, viewports.standard);
  const spec = curveSpec(samples, 600);
  assert.equal(spec.usermeta.source, calculation.source);
  assert.equal(samples.source, calculation.checked.source);
  assert.equal(spec.data.values.length, samples.curves.reduce((n, c) => n + c.segments.length, 0));
  const [a, b] = samples.curves[0].segments[0];
  assert.deepEqual(spec.data.values[0], { curve: samples.curves[0].label, x: a[0], y: a[1], x2: b[0], y2: b[1] });
  const view = new View(parse(compile(spec).spec), { renderer: 'none' });
  try {
    const svg = await view.toSVG();
    assert.match(svg, /<svg/u);
    assert.match(svg, /mark-rule/u);
    assert.match(svg, /#21645e/u);
    assert.match(svg, /#be653b/u);
  } finally { view.finalize(); }
});

test('source edits, viewport changes and unsupported numeric interpretations stay distinct', () => {
  const first = calculateFamily('1'), second = calculateFamily('-1');
  assert.notEqual(first.source, second.source);
  assert.notEqual(first.identity, second.identity);
  const near = sampleFamily(first, viewports.standard), wide = sampleFamily(first, viewports.wide);
  assert.equal(near.source, wide.source);
  assert.notDeepEqual(near.curves[0].segments, wide.curves[0].segments);
  assert.throws(() => sampleFamily({ ...first, input: second.input }, viewports.standard), /different/u);
  assert.throws(() => calculateFamily('1/0'));
  assert.throws(() => calculateFamily('0.5'));
  assert.throws(() => calculateFamily('1'.repeat(513)), /512/u);
  const huge = calculateFamily('1' + '0'.repeat(400));
  assert.equal(huge.checked.authority, 'exact-polynomial-arithmetic');
  assert.throws(() => sampleFamily(huge, viewports.standard), /numerical interpretation/u);
});

test('a late render is disposed and cannot replace the current source', async () => {
  const slot = createPlotSlot(), events = [];
  const plot = name => ({ mount() { events.push(`mount:${name}`); }, dispose() { events.push(`dispose:${name}`); } });
  let finishFirst;
  const first = slot.show(slot.invalidate(), () => new Promise(resolve => { finishFirst = resolve; }));
  const current = slot.invalidate();
  assert.equal(await slot.show(current, async () => plot('current')), true);
  finishFirst(plot('old'));
  assert.equal(await first, false);
  assert.deepEqual(events, ['mount:current', 'dispose:old']);
  slot.invalidate();
  assert.deepEqual(events, ['mount:current', 'dispose:old', 'dispose:current']);
  let called = false;
  assert.equal(await slot.show(current, async () => { called = true; return plot('invalid'); }), false);
  assert.equal(called, false);
});

test('an invalidating input or failed mount leaves no retained plot', async () => {
  const slot = createPlotSlot();
  let complete, disposed = 0;
  const pending = slot.show(slot.invalidate(), () => new Promise(resolve => { complete = resolve; }));
  slot.invalidate();
  complete({ mount() { assert.fail('invalid input must prevent mounting'); }, dispose() { disposed++; } });
  assert.equal(await pending, false);
  await assert.rejects(slot.show(slot.invalidate(), async () => ({
    mount() { throw new Error('mount failure'); }, dispose() { disposed++; },
  })), /mount failure/u);
  assert.equal(disposed, 2);
});

test('the browser bundle resolves the installed package and normal ecosystem dependencies only', async () => {
  const meta = JSON.parse(await readFile('dist/browser-meta.json', 'utf8'));
  const inputs = Object.keys(meta.inputs);
  assert.ok(inputs.some(name => name.endsWith('/@hotdocx/emdash/dist/algebra.js')));
  assert.ok(inputs.some(name => name.includes('/vega-lite/')));
  assert.ok(inputs.some(name => name.includes('/vega/')));
  for (const name of inputs) {
    assert.ok(['main.ts', 'model.ts', 'plot-slot.ts'].includes(name) || name.startsWith('node_modules/') || name.startsWith('(disabled):'), name);
    assert.doesNotMatch(name, /emdash.*dist\/(?:index|workspace|authoring|benchmark)\.js$/u);
  }
  const bundle = await readFile('dist/app.js', 'utf8');
  assert.doesNotMatch(bundle, /CoreChecker|comm_ring_|computeSingularIdealWitness/u);
});
