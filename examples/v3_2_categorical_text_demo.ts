/**
 * Run with:
 *   ./scripts/pnpmw run demo:categorical-text
 */

import {
    CoreCategoricalProgram,
    CoreCategoricalTextBinding,
    CoreCategoricalTextError,
    elaborateCoreCategoricalText
} from '../src/v3_2';

const program = new CoreCategoricalProgram({
    sourceFile: 'examples/v3_2_categorical_text_demo.ts'
});
const A = program.category('text_demo_A', { line: 15 });
const B = program.category('text_demo_B', { line: 16 });
const C = program.category('text_demo_C', { line: 17 });
const functorsBC = program.functorCategory(B, C, { line: 18 });
const H = program.functor('text_demo_H', A, functorsBC, { line: 19 });
const K = program.functor('text_demo_K', A, B, { line: 20 });
const F = program.functor('text_demo_F', A, functorsBC, { line: 21 });
const G = program.functor('text_demo_G', A, B, { line: 22 });
const y0 = program.object('text_demo_y0', B, { line: 23 });
const x0 = program.object('text_demo_x0', A, { line: 24 });
const x1 = program.object('text_demo_x1', A, { line: 25 });
const p = program.homBoundary(A, x0, x1, { line: 26 });

const environment: readonly CoreCategoricalTextBinding[] = Object.freeze([
    { name: 'A', kind: 'category', value: A },
    { name: 'B', kind: 'category', value: B },
    { name: 'C', kind: 'category', value: C },
    { name: 'H', kind: 'term', value: H },
    { name: 'K', kind: 'term', value: K },
    { name: 'F', kind: 'term', value: F },
    { name: 'G', kind: 'term', value: G },
    { name: 'y0', kind: 'term', value: y0 },
    { name: 'p', kind: 'hom-boundary', value: p }
]);

const pointwiseInput = 'λ^f x. (H x) (K x)';
const pointwise = elaborateCoreCategoricalText(program, {
    source: pointwiseInput,
    sourceFile: '<categorical-text-demo:pointwise>',
    environment,
    expected: {
        kind: 'ordinary-functor',
        source: A,
        target: C
    }
});
const pointwiseDirect = program.lambda(
    'x',
    A,
    C,
    x => program.apply(
        program.apply(H, x),
        program.apply(K, x)
    )
);

const fixedInput = 'λ^f x : A. F x y0';
const fixed = elaborateCoreCategoricalText(program, {
    source: fixedInput,
    sourceFile: '<categorical-text-demo:fixed>',
    environment,
    expected: {
        kind: 'ordinary-functor',
        source: A,
        target: C
    }
});
const fixedDirect = program.lambda(
    'x',
    A,
    C,
    x => program.apply(program.apply(F, x), y0)
);

const homInput = 'G p';
const hom = elaborateCoreCategoricalText(program, {
    source: homInput,
    sourceFile: '<categorical-text-demo:hom>',
    environment,
    expected: {
        kind: 'term',
        applicationShape: 'whole-hom-action'
    }
});
const homDirect = program.apply(G, p, {
    expectedShape: 'whole-hom-action'
});

const rows = [
    {
        name: 'recursive open/open application',
        input: pointwiseInput,
        parsed: pointwise,
        direct: pointwiseDirect
    },
    {
        name: 'recursive open/closed evaluation',
        input: fixedInput,
        parsed: fixed,
        direct: fixedDirect
    },
    {
        name: 'type-directed whole-Hom action',
        input: homInput,
        parsed: hom,
        direct: homDirect
    }
] as const;

const output: string[] = [
    'emdash v3.2 categorical text demo',
    '==================================='
];
for (const row of rows) {
    const compilation = program.compile(row.parsed);
    output.push(
        '',
        row.name,
        `input: ${row.input}`,
        `explicit Core: ${compilation.explicitCore}`,
        `inferred type: ${compilation.explicitInferredType}`,
        `structural lowering: ${
            compilation.structuralPrerequisites.join(', ') || '(none)'
        }`,
        `direct TypeScript comparison: ${
            program.compare(row.parsed, row.direct).status
        }`
    );
}

try {
    elaborateCoreCategoricalText(program, {
        source: 'λ^f x. F x missing',
        sourceFile: '<categorical-text-demo:negative>',
        environment,
        expected: {
            kind: 'ordinary-functor',
            source: A,
            target: C
        }
    });
    throw new Error('Expected the negative text demo to fail');
} catch (error: unknown) {
    if (!(error instanceof CoreCategoricalTextError)) throw error;
    output.push(
        '',
        'source-located negative',
        `diagnostic: ${error.code} (${error.phase})`,
        `location: ${error.span.file}:` +
            `${error.span.start.line}:${error.span.start.column}`,
        `message: ${error.detail}`
    );
}

output.push(
    '',
    'Boundary: dependency-free private syntax nodes; existing categorical ' +
        'program/checker; no Lambdapi process or browser promotion.'
);

process.stdout.write(`${output.join('\n')}\n`);
