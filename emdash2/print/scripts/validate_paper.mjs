import fs from 'node:fs';
import { DiagramSpecSchema } from '@hotdocx/arrowgram';
import { selectDocuments } from './document_registry.mjs';

function extractBlocks(markdown, klass) {
  const re = new RegExp('<div class="' + klass + '"[^>]*>([\\s\\S]*?)<\\/div>', 'g');
  return [...markdown.matchAll(re)].map((match) => match[1].trim()).filter(Boolean);
}

function main() {
  const documents = selectDocuments(process.argv.slice(2), 'validate');
  let okAll = true;

  for (const document of documents) {
    const markdownUrl = new URL('../public/' + document.file, import.meta.url);
    if (!fs.existsSync(markdownUrl)) {
      console.error(document.file + ': registered document is missing');
      okAll = false;
      continue;
    }
    const markdown = fs.readFileSync(markdownUrl, 'utf8');
    let ok = true;

    const arrowgrams = extractBlocks(markdown, 'arrowgram');
    arrowgrams.forEach((raw, index) => {
      let parsed;
      try {
        parsed = JSON.parse(raw);
      } catch (error) {
        console.error(
          document.file + ': Arrowgram #' + (index + 1) +
          ': JSON parse error: ' + error.message
        );
        ok = false;
        return;
      }

      const result = DiagramSpecSchema.safeParse(parsed);
      if (!result.success) {
        console.error(document.file + ': Arrowgram #' + (index + 1) + ': schema error');
        console.error(result.error.issues);
        ok = false;
      }
    });

    const vegas = extractBlocks(markdown, 'vega-lite');
    vegas.forEach((raw, index) => {
      try {
        JSON.parse(raw);
      } catch (error) {
        console.error(
          document.file + ': Vega-Lite #' + (index + 1) +
          ': JSON parse error: ' + error.message
        );
        ok = false;
      }
    });

    console.log(
      'validate_paper: file=' + document.file +
      ', arrowgram blocks=' + arrowgrams.length +
      ', vega-lite blocks=' + vegas.length +
      ', status=' + (ok ? 'OK' : 'FAIL')
    );
    okAll = okAll && ok;
  }

  process.exitCode = okAll ? 0 : 1;
}

try {
  main();
} catch (error) {
  console.error('validate_paper failed: ' + error.message);
  process.exitCode = 1;
}
