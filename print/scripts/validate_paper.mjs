import fs from 'fs';
import { z } from 'zod';

const NodeSchema = z.object({
  name: z.string(),
  label: z.string().optional(),
  left: z.number(),
  top: z.number(),
});

const ArrowStyleSchema = z.object({
  mode: z.enum(['arrow', 'adjunction', 'corner', 'corner_inverse']).optional(),
  head: z.object({
    name: z.enum(['normal', 'none', 'epi', 'hook', 'maps_to', 'harpoon']).optional(),
    side: z.enum(['top', 'bottom']).optional(),
  }).optional(),
  tail: z.object({
    name: z.enum(['normal', 'none', 'mono', 'hook', 'maps_to']).optional(),
    side: z.enum(['top', 'bottom']).optional(),
  }).optional(),
  body: z.object({
    name: z.enum(['solid', 'dashed', 'dotted', 'squiggly', 'wavy', 'barred', 'double_barred', 'bullet_solid', 'bullet_hollow']).optional(),
  }).optional(),
  level: z.number().int().optional(),
});

const ArrowSchema = z.object({
  from: z.string(),
  to: z.string(),
  name: z.string().optional(),
  label: z.string().optional(),
  curve: z.number().optional(),
  shift: z.number().optional(),
  radius: z.number().optional(),
  angle: z.number().optional(),
  label_alignment: z.enum(['over', 'left', 'right']).optional(),
  style: ArrowStyleSchema.optional(),
});

const DiagramSpecSchema = z.object({
  version: z.number().int().optional(),
  nodes: z.array(NodeSchema),
  arrows: z.array(ArrowSchema).optional(),
});

function extractBlocks(markdown, klass) {
  const re = new RegExp(`<div class=\\"${klass}\\"[^>]*>([\\s\\S]*?)<\\/div>`, 'g');
  return [...markdown.matchAll(re)].map(m => m[1].trim()).filter(Boolean);
}

const mdPath = new URL('../public/index.md', import.meta.url);
const md = fs.readFileSync(mdPath, 'utf8');

let ok = true;

const arrowgrams = extractBlocks(md, 'arrowgram');
arrowgrams.forEach((raw, i) => {
  let parsed;
  try {
    parsed = JSON.parse(raw);
  } catch (e) {
    console.error(`Arrowgram #${i + 1}: JSON parse error: ${e.message}`);
    ok = false;
    return;
  }

  const res = DiagramSpecSchema.safeParse(parsed);
  if (!res.success) {
    console.error(`Arrowgram #${i + 1}: schema error`);
    console.error(res.error.issues);
    ok = false;
  }
});

const vegas = extractBlocks(md, 'vega-lite');
vegas.forEach((raw, i) => {
  try {
    JSON.parse(raw);
  } catch (e) {
    console.error(`Vega-Lite #${i + 1}: JSON parse error: ${e.message}`);
    ok = false;
  }
});

console.log(`validate_paper: arrowgram blocks=${arrowgrams.length}, vega-lite blocks=${vegas.length}, status=${ok ? 'OK' : 'FAIL'}`);
process.exit(ok ? 0 : 1);
