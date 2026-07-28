/**
 * Focused SCALE-0A tests for canonical Lambdapi export inventory.
 */

import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { resolve } from 'node:path';
import { spawnSync } from 'node:child_process';
import { describe, it } from 'node:test';
import {
    CanonicalLambdapiExportError,
    CanonicalLambdapiCommandCounts,
    parseCanonicalLambdapiExport
} from '../src/v3_2';

const repositoryRoot = resolve(__dirname, '..');
const lambdapiRoot = resolve(repositoryRoot, 'emdash2');

const fixture = `
/* A comment with ; and [ unmatched presentation characters. */
require open emdash.emdash3_2;
flag "semi;colon" on;
protected injective symbol sample [A : Grpd] (x : τ A) : τ A
  ≔ λ (y : τ A), y;
inductive sample_pair (A : TYPE) : TYPE ≔
| sample_left : A → sample_pair A
| sample_right : {A} → sample_pair A;
rule @sample zero $n ↪ $n
// A grouped clause; this semicolon is only commentary.
with @sample (succ $m) $n ↪ succ (@sample $m $n);
unif_rule sample $x ≡ sample $y ↪
  [ $x ≡ $y; "a semicolon ; inside a string" ];
builtin "sample;builtin" ≔ sample;
notation sample infix 10;
opaque sample;
`;

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(
        assertDeepFrozen
    );
};

const expectExportError = (
    moduleId: string,
    source: string,
    code: CanonicalLambdapiExportError['code']
): void => {
    assert.throws(
        () => parseCanonicalLambdapiExport(moduleId, source),
        error =>
            error instanceof CanonicalLambdapiExportError &&
            error.code === code
    );
};

interface LiveExportExpectation {
    readonly moduleId: string;
    readonly file: string;
    readonly sha256: string;
    readonly imports: readonly string[];
    readonly counts: CanonicalLambdapiCommandCounts;
    readonly shape: {
        readonly definitions: number;
        readonly assumptions: number;
        readonly protectedDefinitions: number;
        readonly tacticBodies: number;
        readonly runtimeClauses: number;
        readonly constructors: number;
    };
}

const liveExpectations: readonly LiveExportExpectation[] = [
    {
        moduleId: 'emdash.emdash3_2',
        file: 'emdash3_2.lp',
        sha256:
            'fb6fbcf4d486f22fa000f16f2deefc4b9bae65a066b8def952a3f1756030cf2f',
        imports: [],
        counts: {
            require: 0,
            flag: 5,
            symbol: 758,
            inductive: 11,
            rule: 601,
            unif_rule: 61,
            builtin: 6,
            notation: 3,
            opaque: 1
        },
        shape: {
            definitions: 479,
            assumptions: 279,
            protectedDefinitions: 0,
            tacticBodies: 0,
            runtimeClauses: 637,
            constructors: 14
        }
    },
    {
        moduleId: 'emdash.emdash3_2_nat_arithmetic',
        file: 'emdash3_2_nat_arithmetic.lp',
        sha256:
            '2fc300997b2de8d53f3cbf7822aff5dedf50edd4167d28c0f12fccc006dcf354',
        imports: ['emdash.emdash3_2'],
        counts: {
            require: 1,
            flag: 0,
            symbol: 8,
            inductive: 0,
            rule: 1,
            unif_rule: 0,
            builtin: 0,
            notation: 0,
            opaque: 0
        },
        shape: {
            definitions: 7,
            assumptions: 1,
            protectedDefinitions: 0,
            tacticBodies: 0,
            runtimeClauses: 3,
            constructors: 0
        }
    },
    {
        moduleId: 'emdash.emdash3_2_eq1_hom_action',
        file: 'emdash3_2_eq1_hom_action.lp',
        sha256:
            'a1d73d0aac76ca1c5b57c6dd1e9407b3f3eb431839d88484f278fc0ac109c0e2',
        imports: ['emdash.emdash3_2'],
        counts: {
            require: 1,
            flag: 0,
            symbol: 77,
            inductive: 0,
            rule: 0,
            unif_rule: 0,
            builtin: 0,
            notation: 0,
            opaque: 0
        },
        shape: {
            definitions: 77,
            assumptions: 0,
            protectedDefinitions: 56,
            tacticBodies: 2,
            runtimeClauses: 0,
            constructors: 0
        }
    },
    {
        moduleId: 'emdash.emdash3_2_eq1_evidence_property',
        file: 'emdash3_2_eq1_evidence_property.lp',
        sha256:
            '83075b38429baee5b03c7829b2d82f908a04b374cdb839249a54dda72835f4ee',
        imports: [
            'emdash.emdash3_2',
            'emdash.emdash3_2_eq1_hom_action'
        ],
        counts: {
            require: 2,
            flag: 0,
            symbol: 60,
            inductive: 0,
            rule: 0,
            unif_rule: 0,
            builtin: 0,
            notation: 0,
            opaque: 0
        },
        shape: {
            definitions: 60,
            assumptions: 0,
            protectedDefinitions: 0,
            tacticBodies: 0,
            runtimeClauses: 0,
            constructors: 0
        }
    },
    {
        moduleId: 'emdash.emdash3_2_walking_end_hit',
        file: 'emdash3_2_walking_end_hit.lp',
        sha256:
            '6b7f2d63fe9490a01d5c96726673bb1070400a154e2287fb36cc1486734dfbda',
        imports: [
            'emdash.emdash3_2_nat_arithmetic',
            'emdash.emdash3_2_eq1_hom_action'
        ],
        counts: {
            require: 2,
            flag: 0,
            symbol: 81,
            inductive: 0,
            rule: 8,
            unif_rule: 1,
            builtin: 0,
            notation: 0,
            opaque: 0
        },
        shape: {
            definitions: 75,
            assumptions: 6,
            protectedDefinitions: 0,
            tacticBodies: 0,
            runtimeClauses: 10,
            constructors: 0
        }
    }
];

const runLambdapi = (args: readonly string[]): string => {
    const result = spawnSync('lambdapi', [...args], {
        cwd: lambdapiRoot,
        encoding: 'utf8',
        timeout: 60_000,
        maxBuffer: 64 * 1024 * 1024
    });
    assert.equal(
        result.error,
        undefined,
        result.error?.message
    );
    assert.equal(
        result.status,
        0,
        `lambdapi ${args.join(' ')} failed:\n${result.stderr}`
    );
    return result.stdout;
};

const sha256 = (source: string): string =>
    createHash('sha256').update(source).digest('hex');

describe('TypeScript v3.2 SCALE-0A canonical export inventory', () => {
    it('classifies the complete supported top-level command vocabulary', () => {
        const inventory = parseCanonicalLambdapiExport(
            'fixture.scale_inventory',
            fixture
        );

        assert.deepEqual(inventory.counts, {
            require: 1,
            flag: 1,
            symbol: 1,
            inductive: 1,
            rule: 1,
            unif_rule: 1,
            builtin: 1,
            notation: 1,
            opaque: 1
        });
        assert.deepEqual(
            inventory.commands.map(command => command.kind),
            [
                'require',
                'flag',
                'symbol',
                'inductive',
                'rule',
                'unif_rule',
                'builtin',
                'notation',
                'opaque'
            ]
        );
        assert.deepEqual(
            inventory.commands.map(command => command.ordinal),
            [0, 1, 2, 3, 4, 5, 6, 7, 8]
        );
        assert.deepEqual(
            inventory.imports,
            ['emdash.emdash3_2']
        );
    });

    it('preserves symbol, inductive, and grouped-rule inventory facts', () => {
        const inventory = parseCanonicalLambdapiExport(
            'fixture.scale_details',
            fixture
        );
        const declaration = inventory.commands[2];
        assert.equal(declaration.kind, 'symbol');
        if (declaration.kind !== 'symbol') {
            throw new Error('Expected the fixture symbol command');
        }
        assert.equal(declaration.name, 'sample');
        assert.deepEqual(
            declaration.modifiers,
            ['protected', 'injective']
        );
        assert.equal(declaration.hasBody, true);
        assert.match(declaration.text, /λ \(y : τ A\), y;$/u);

        const inductive = inventory.commands[3];
        assert.equal(inductive.kind, 'inductive');
        if (inductive.kind !== 'inductive') {
            throw new Error('Expected the fixture inductive command');
        }
        assert.equal(inductive.name, 'sample_pair');
        assert.equal(inductive.constructorCount, 2);

        const rule = inventory.commands[4];
        assert.equal(rule.kind, 'rule');
        if (rule.kind !== 'rule') {
            throw new Error('Expected the fixture rule command');
        }
        assert.equal(rule.clauseCount, 2);
        assert.equal(rule.text.includes('commentary'), false);
    });

    it('distinguishes opaque signatures from transparent definitions', () => {
        const inventory = parseCanonicalLambdapiExport(
            'fixture.scale_symbols',
            `
            constant symbol Opaque : TYPE;
            symbol transparent : TYPE ≔ TYPE;
            `
        );
        const [opaque, transparent] = inventory.commands;
        assert.equal(opaque.kind, 'symbol');
        assert.equal(transparent.kind, 'symbol');
        if (
            opaque.kind !== 'symbol' ||
            transparent.kind !== 'symbol'
        ) {
            throw new Error('Expected two symbol commands');
        }
        assert.deepEqual(opaque.modifiers, ['constant']);
        assert.equal(opaque.hasBody, false);
        assert.deepEqual(transparent.modifiers, []);
        assert.equal(transparent.hasBody, true);
    });

    it('keeps prefixed inductives and tactic bodies as whole commands', () => {
        const inventory = parseCanonicalLambdapiExport(
            'fixture.scale_generated',
            `
            (A : TYPE)inductive Wrapped : TYPE ≔
            | wrap : A → Wrapped A;
            protected symbol proved (x : TYPE) : TYPE ≔
            begin
              assume x;
              simplify rule off;
              solve;
            end;
            opaque proved;
            `
        );
        assert.deepEqual(
            inventory.commands.map(command => command.kind),
            ['inductive', 'symbol', 'opaque']
        );
        const inductive = inventory.commands[0];
        const proved = inventory.commands[1];
        const opacity = inventory.commands[2];
        assert.equal(inductive.kind, 'inductive');
        assert.equal(proved.kind, 'symbol');
        assert.equal(opacity.kind, 'opaque');
        if (
            inductive.kind !== 'inductive' ||
            proved.kind !== 'symbol' ||
            opacity.kind !== 'opaque'
        ) {
            throw new Error('Expected inductive, symbol, and opacity commands');
        }
        assert.equal(inductive.name, 'Wrapped');
        assert.equal(inductive.constructorCount, 1);
        assert.equal(proved.name, 'proved');
        assert.equal(proved.hasBody, true);
        assert.match(proved.text, /simplify rule off;/u);
        assert.deepEqual(opacity.symbols, ['proved']);
    });

    it('returns a recursively immutable inventory', () => {
        const inventory = parseCanonicalLambdapiExport(
            'fixture.scale_frozen',
            fixture
        );
        assertDeepFrozen(inventory);
    });

    it('fails closed on malformed framing and unsupported commands', () => {
        expectExportError(
            'bad-module',
            'symbol x : TYPE;',
            'INVALID_MODULE_ID'
        );
        expectExportError(
            'fixture.bad_delimiter',
            'symbol x : (TYPE];',
            'MISMATCHED_DELIMITER'
        );
        expectExportError(
            'fixture.bad_string',
            'flag "unterminated;',
            'UNTERMINATED_STRING'
        );
        expectExportError(
            'fixture.bad_comment',
            '/* unterminated',
            'UNTERMINATED_COMMENT'
        );
        expectExportError(
            'fixture.bad_terminator',
            'symbol x : TYPE',
            'UNTERMINATED_COMMAND'
        );
        expectExportError(
            'fixture.unknown',
            'assert ⊢ TYPE;',
            'UNSUPPORTED_COMMAND'
        );
        expectExportError(
            'fixture.bad_require',
            'require open bad-module;',
            'MALFORMED_COMMAND'
        );
        expectExportError(
            'fixture.bad_inductive',
            'inductive empty : TYPE;',
            'MALFORMED_COMMAND'
        );
        expectExportError(
            'fixture.bad_flag',
            'flag "eta_equality" maybe;',
            'MALFORMED_COMMAND'
        );
        expectExportError(
            'fixture.bad_rule',
            'rule f $x;',
            'MALFORMED_COMMAND'
        );
        expectExportError(
            'fixture.bad_unification',
            'unif_rule f $x ≡ f $y;',
            'MALFORMED_COMMAND'
        );
        expectExportError(
            'fixture.bad_builtin',
            'builtin "T" τ;',
            'MALFORMED_COMMAND'
        );
        expectExportError(
            'fixture.bad_notation',
            'notation f unknown;',
            'MALFORMED_COMMAND'
        );
        expectExportError(
            'fixture.bad_opacity',
            'opaque ;',
            'MALFORMED_COMMAND'
        );
        expectExportError(
            'fixture.bad_tactic_start',
            'symbol proof : TYPE ≔ begin solve;',
            'MISMATCHED_TACTIC_BLOCK'
        );
        expectExportError(
            'fixture.bad_tactic_end',
            'symbol proof : TYPE ≔ end;',
            'MISMATCHED_TACTIC_BLOCK'
        );
    });

    it(
        'pins deterministic live exports of all five active modules',
        {
            skip:
                process.env.EMDASH_RUN_LAMBDAPI_SCALE_PROBES !== '1'
        },
        () => {
            const version = runLambdapi(['--version']).trim();
            assert.equal(version, '3.0.0-90-gdb4f780');

            let coreExport: string | undefined;
            liveExpectations.forEach(expectation => {
                const exported = runLambdapi([
                    'export',
                    '-o',
                    'lp',
                    expectation.file
                ]);
                assert.equal(sha256(exported), expectation.sha256);

                const inventory = parseCanonicalLambdapiExport(
                    expectation.moduleId,
                    exported
                );
                assert.deepEqual(inventory.counts, expectation.counts);
                assert.deepEqual(inventory.imports, expectation.imports);
                assert.equal(
                    inventory.commands.length,
                    Object.values(expectation.counts).reduce(
                        (sum, count) => sum + count,
                        0
                    )
                );
                const symbols = inventory.commands.filter(
                    command => command.kind === 'symbol'
                );
                const rules = inventory.commands.filter(
                    command => command.kind === 'rule'
                );
                const inductives = inventory.commands.filter(
                    command => command.kind === 'inductive'
                );
                assert.deepEqual(
                    {
                        definitions: symbols.filter(
                            command => command.hasBody
                        ).length,
                        assumptions: symbols.filter(
                            command => !command.hasBody
                        ).length,
                        protectedDefinitions: symbols.filter(
                            command =>
                                command.modifiers.includes('protected')
                        ).length,
                        tacticBodies: symbols.filter(
                            command => /\bbegin\b/u.test(command.text)
                        ).length,
                        runtimeClauses: rules.reduce(
                            (sum, command) =>
                                sum + command.clauseCount,
                            0
                        ),
                        constructors: inductives.reduce(
                            (sum, command) =>
                                sum + command.constructorCount,
                            0
                        )
                    },
                    expectation.shape
                );
                if (expectation.file === 'emdash3_2.lp') {
                    coreExport = exported;
                }
            });

            const secondCoreExport = runLambdapi([
                'export',
                '-o',
                'lp',
                'emdash3_2.lp'
            ]);
            assert.equal(secondCoreExport, coreExport);
            assert.equal(
                sha256(secondCoreExport),
                liveExpectations[0].sha256
            );
        }
    );
});
