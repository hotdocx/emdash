/**
 * Machine-readable MIGRATE-1 inventory.
 *
 * The legacy root TypeScript engine is evidence, not an API compatibility
 * target.  This ledger makes every root source file, generic mechanism, and
 * legacy test file explicit before MIGRATE-2 is allowed to delete anything.
 */

export type LegacyMechanismDisposition =
    | 'port'
    | 'reimplement'
    | 'retain-temporarily-as-oracle'
    | 'delete';

export type LegacyMechanismState =
    | 'covered'
    | 'partial'
    | 'dependency-ready'
    | 'blocked-by-replacement'
    | 'deferred'
    | 'ready-to-delete';

export interface LegacyMechanismDispositionEntry {
    readonly id:
        | 'bidirectional-infer-check'
        | 'contextual-metavariables'
        | 'higher-order-pattern-unification'
        | 'rule-authority-separation'
        | 'capture-avoiding-substitution'
        | 'proof-state-traversal'
        | 'direct-typescript-constructors'
        | 'legacy-category-constructors'
        | 'global-mutable-setup'
        | 'legacy-parser';
    readonly disposition: LegacyMechanismDisposition;
    readonly state: LegacyMechanismState;
    readonly evidence: readonly string[];
    readonly nextBoundary: string;
}

export type LegacySourceDisposition =
    | 'split-then-delete'
    | 'delete'
    | 'defer-delete';

export interface LegacySourceDispositionEntry {
    readonly file: string;
    readonly disposition: LegacySourceDisposition;
    readonly retainedInvariant: string;
    readonly deletionBoundary: string;
}

export type LegacyTestDisposition =
    | 'replace-then-delete'
    | 'split-then-delete'
    | 'delete-without-port'
    | 'defer-delete';

export interface LegacyTestDispositionEntry {
    readonly file: string;
    readonly disposition: LegacyTestDisposition;
    readonly retainedInvariant: string;
    readonly replacementTests: readonly string[];
    readonly remainingBoundary: string;
}

export interface LegacyMigrationInventory {
    readonly revision: 'MIGRATE-1D';
    readonly status: 'ready-for-physical-deletion';
    readonly mechanisms: readonly LegacyMechanismDispositionEntry[];
    readonly sourceFiles: readonly LegacySourceDispositionEntry[];
    readonly testFiles: readonly LegacyTestDispositionEntry[];
    readonly nextSlice: 'MIGRATE-2';
}

const deepFreeze = <T>(value: T): T => {
    if (
        value !== null &&
        typeof value === 'object' &&
        !Object.isFrozen(value)
    ) {
        for (const child of Object.values(value as object)) {
            deepFreeze(child);
        }
        Object.freeze(value);
    }
    return value;
};

const canonicalInventory: LegacyMigrationInventory = {
    revision: 'MIGRATE-1D',
    status: 'ready-for-physical-deletion',
    mechanisms: [
        {
            id: 'bidirectional-infer-check',
            disposition: 'reimplement',
            state: 'covered',
            evidence: [
                'tests/v3_2_core_checker_tests.ts'
            ],
            nextBoundary:
                'Retain the Core checker; delete the legacy elaborator in ' +
                'MIGRATE-2.'
        },
        {
            id: 'contextual-metavariables',
            disposition: 'reimplement',
            state: 'covered',
            evidence: [
                'tests/v3_2_core_session_tests.ts',
                'tests/v3_2_core_checker_tests.ts'
            ],
            nextBoundary:
                'Retain session-local metas and delete mutable legacy holes ' +
                'in MIGRATE-2.'
        },
        {
            id: 'higher-order-pattern-unification',
            disposition: 'port',
            state: 'covered',
            evidence: [
                'tests/v3_2_pattern_unification_tests.ts'
            ],
            nextBoundary:
                'Retain the contextual Miller-pattern solver and delete the ' +
                'name-based legacy unifier in MIGRATE-2.'
        },
        {
            id: 'rule-authority-separation',
            disposition: 'reimplement',
            state: 'covered',
            evidence: [
                'tests/v3_2_manifest_tests.ts',
                'tests/v3_2_runtime_rewrite_tests.ts',
                'tests/v3_2_differential_rule_tests.ts'
            ],
            nextBoundary:
                'Keep proof-time evidence non-executable; delete both global ' +
                'legacy rule registries in MIGRATE-2.'
        },
        {
            id: 'capture-avoiding-substitution',
            disposition: 'reimplement',
            state: 'covered',
            evidence: [
                'tests/v3_2_core_binder_tests.ts',
                'tests/v3_2_telescope_structural_tests.ts'
            ],
            nextBoundary:
                'Retain the locally nameless Core operations and delete the ' +
                'HOAS/name-opening implementation in MIGRATE-2.'
        },
        {
            id: 'proof-state-traversal',
            disposition: 'reimplement',
            state: 'covered',
            evidence: [
                'tests/v3_2_proof_state_tests.ts',
                'tests/v3_2_proof_refinement_tests.ts'
            ],
            nextBoundary:
                'Retain Core inspection/refinement and delete mutable legacy ' +
                'proof holes and category traversal in MIGRATE-2.'
        },
        {
            id: 'direct-typescript-constructors',
            disposition: 'port',
            state: 'covered',
            evidence: [
                'tests/v3_2_elab0_tests.ts',
                'tests/v3_2_core_binder_tests.ts'
            ],
            nextBoundary:
                'Keep direct surface/Core constructors; textual parsing ' +
                'remains independent.'
        },
        {
            id: 'legacy-category-constructors',
            disposition: 'delete',
            state: 'ready-to-delete',
            evidence: [
                'tests/v3_2_differential_owner_tests.ts',
                'tests/v3_2_differential_rule_tests.ts',
                'tests/v3_2_differential_higher_cell_tests.ts'
            ],
            nextBoundary:
                'MIGRATE-2 deletes the stale category union after every ' +
                'replacement-focused migration gate is green.'
        },
        {
            id: 'global-mutable-setup',
            disposition: 'delete',
            state: 'ready-to-delete',
            evidence: [
                'tests/v3_2_core_context_tests.ts',
                'tests/v3_2_core_session_tests.ts',
                'tests/v3_2_manifest_tests.ts'
            ],
            nextBoundary:
                'MIGRATE-2 deletes reset-based definitions, counters, holes, ' +
                'and rule registries after migrated consumers are isolated.'
        },
        {
            id: 'legacy-parser',
            disposition: 'delete',
            state: 'ready-to-delete',
            evidence: [
                'docs/TYPESCRIPT_ELABORATOR_V3_2_MASTER_PLAN.md'
            ],
            nextBoundary:
                'Delete the legacy grammar in MIGRATE-2. Any new grammar ' +
                'requires H-06 and targets the v3.2 surface AST.'
        }
    ],
    sourceFiles: [
        {
            file: 'src/constants.ts',
            disposition: 'delete',
            retainedInvariant:
                'No generic invariant; the table is a stale category ' +
                'implicit-slot registry.',
            deletionBoundary: 'MIGRATE-2'
        },
        {
            file: 'src/elaboration.ts',
            disposition: 'split-then-delete',
            retainedInvariant:
                'Bidirectional organization and source-located mismatch ' +
                'lessons only.',
            deletionBoundary: 'MIGRATE-2 after MIGRATE-1C'
        },
        {
            file: 'src/equality.ts',
            disposition: 'split-then-delete',
            retainedInvariant:
                'Structural congruence and explicit conversion boundaries.',
            deletionBoundary: 'MIGRATE-2'
        },
        {
            file: 'src/globals.ts',
            disposition: 'delete',
            retainedInvariant:
                'No ambient definition or rule mutation is retained.',
            deletionBoundary: 'MIGRATE-2'
        },
        {
            file: 'src/parser.ts',
            disposition: 'defer-delete',
            retainedInvariant:
                'No grammar is a compatibility target.',
            deletionBoundary: 'MIGRATE-2; replacement requires H-06'
        },
        {
            file: 'src/pattern.ts',
            disposition: 'split-then-delete',
            retainedInvariant:
                'Positive higher-order pattern cases and explicit ' +
                'non-pattern rejection only.',
            deletionBoundary: 'MIGRATE-2 after MIGRATE-1B'
        },
        {
            file: 'src/proof.ts',
            disposition: 'split-then-delete',
            retainedInvariant:
                'Reachable-goal traversal, reporting, and checked refinement.',
            deletionBoundary: 'MIGRATE-2 after MIGRATE-1C'
        },
        {
            file: 'src/reduction.ts',
            disposition: 'split-then-delete',
            retainedInvariant:
                'Explicit step bounds and rewrite/checker separation.',
            deletionBoundary: 'MIGRATE-2'
        },
        {
            file: 'src/state.ts',
            disposition: 'delete',
            retainedInvariant:
                'No global counters, stores, flags, or mutable holes survive.',
            deletionBoundary: 'MIGRATE-2'
        },
        {
            file: 'src/stdlib.ts',
            disposition: 'delete',
            retainedInvariant:
                'No legacy category declaration or reset contract survives.',
            deletionBoundary: 'MIGRATE-2'
        },
        {
            file: 'src/structural.ts',
            disposition: 'split-then-delete',
            retainedInvariant:
                'Exhaustive structural traversal over the new Core only.',
            deletionBoundary: 'MIGRATE-2'
        },
        {
            file: 'src/types.ts',
            disposition: 'split-then-delete',
            retainedInvariant:
                'Direct-constructor ergonomics, plicity, and binder-mode ' +
                'lessons only.',
            deletionBoundary: 'MIGRATE-2 after MIGRATE-1C'
        },
        {
            file: 'src/unification.ts',
            disposition: 'split-then-delete',
            retainedInvariant:
                'Occurs checking, deterministic constraints, and the ' +
                'higher-order pattern boundary.',
            deletionBoundary: 'MIGRATE-2 after MIGRATE-1B'
        }
    ],
    testFiles: [
        {
            file: 'tests/equality_tests.ts',
            disposition: 'split-then-delete',
            retainedInvariant:
                'Alpha equality is structural; beta/eta remain outside the ' +
                'reviewed runtime fragment.',
            replacementTests: [
                'tests/v3_2_core_binder_tests.ts',
                'tests/v3_2_conversion_tests.ts'
            ],
            remainingBoundary:
                'Delete the old file in MIGRATE-2 without enabling generic ' +
                'beta or eta.'
        },
        {
            file: 'tests/dependent_types_tests.ts',
            disposition: 'split-then-delete',
            retainedInvariant:
                'Dependent Pi checking and implicit recovery, not the ' +
                'legacy Vec declarations.',
            replacementTests: [
                'tests/v3_2_core_checker_tests.ts',
                'tests/v3_2_dependent_context_tests.ts'
            ],
            remainingBoundary:
                'Delete bespoke legacy inductive declarations in MIGRATE-2.'
        },
        {
            file: 'tests/error_reporting_tests.ts',
            disposition: 'replace-then-delete',
            retainedInvariant:
                'Unbound-name, type-mismatch, non-function, occurs, and ' +
                'source-location diagnostics.',
            replacementTests: [
                'tests/v3_2_core_context_tests.ts',
                'tests/v3_2_core_session_tests.ts',
                'tests/v3_2_core_checker_tests.ts'
            ],
            remainingBoundary: 'Delete the old file in MIGRATE-2.'
        },
        {
            file: 'tests/rewrite_rules_tests.ts',
            disposition: 'split-then-delete',
            retainedInvariant:
                'Typed rule validation, bounded evaluation, and malformed ' +
                'rule rejection.',
            replacementTests: [
                'tests/v3_2_manifest_tests.ts',
                'tests/v3_2_runtime_rewrite_tests.ts'
            ],
            remainingBoundary:
                'Delete the dynamic user-rule registry tests in MIGRATE-2.'
        },
        {
            file: 'tests/rewrite_rules_tests2.ts',
            disposition: 'delete-without-port',
            retainedInvariant:
                'No unique invariant beyond rewrite_rules_tests.ts.',
            replacementTests: [
                'tests/v3_2_runtime_rewrite_tests.ts'
            ],
            remainingBoundary: 'Delete the duplicate legacy file in MIGRATE-2.'
        },
        {
            file: 'tests/inductive_types.ts',
            disposition: 'delete-without-port',
            retainedInvariant:
                'Dynamic Nat/Bool/List declarations and user rewrite rules ' +
                'are outside the frozen MVP.',
            replacementTests: [],
            remainingBoundary:
                'Delete in MIGRATE-2; a future inductive package needs its ' +
                'own reviewed product slice.'
        },
        {
            file: 'tests/equality_inductive_type_family.ts',
            disposition: 'delete-without-port',
            retainedInvariant:
                'The legacy Eq/J encoding is not the active v3.2 equality ' +
                'authority.',
            replacementTests: [],
            remainingBoundary:
                'Delete in MIGRATE-2; active equality remains Lambdapi-owned.'
        },
        {
            file: 'tests/elaboration_options_tests.ts',
            disposition: 'delete-without-port',
            retainedInvariant:
                'No normalizeResultTerm compatibility option is retained.',
            replacementTests: [],
            remainingBoundary:
                'Delete with the legacy elaborator in MIGRATE-2.'
        },
        {
            file: 'tests/higher_order_unification_tests.ts',
            disposition: 'replace-then-delete',
            retainedInvariant:
                'Flex-rigid solutions over distinct local-variable spines, ' +
                'with occurs, scope, and non-pattern negatives.',
            replacementTests: [
                'tests/v3_2_pattern_unification_tests.ts'
            ],
            remainingBoundary:
                'Delete the legacy corpus with the old unifier in MIGRATE-2.'
        },
        {
            file: 'tests/higher_order_pattern_matching_tests.ts',
            disposition: 'defer-delete',
            retainedInvariant:
                'Evidence for the higher-order pattern boundary only; ' +
                'ambient user rewrite matching is not retained.',
            replacementTests: [
                'tests/v3_2_runtime_rewrite_tests.ts',
                'tests/v3_2_pattern_unification_tests.ts'
            ],
            remainingBoundary:
                'The meta-pattern boundary is recorded; delete ambient ' +
                'legacy user-rule matching in MIGRATE-2.'
        },
        {
            file: 'tests/implicit_args_tests.ts',
            disposition: 'split-then-delete',
            retainedInvariant:
                'Generic implicit insertion, dependent recovery, ambiguity, ' +
                'and occurs behavior.',
            replacementTests: [
                'tests/v3_2_core_session_tests.ts',
                'tests/v3_2_core_checker_tests.ts'
            ],
            remainingBoundary:
                'Delete dynamic injectivity flags and the legacy file in ' +
                'MIGRATE-2.'
        },
        {
            file: 'tests/church_encoding_tests.ts',
            disposition: 'split-then-delete',
            retainedInvariant:
                'Dependent Pi/lambda checking through direct constructors.',
            replacementTests: [
                'tests/v3_2_core_binder_tests.ts',
                'tests/v3_2_core_checker_tests.ts'
            ],
            remainingBoundary:
                'Delete the encoding-specific legacy test in MIGRATE-2.'
        },
        {
            file: 'tests/church_encoding_implicit_tests.ts',
            disposition: 'split-then-delete',
            retainedInvariant:
                'Implicit Pi/lambda recovery through direct constructors.',
            replacementTests: [
                'tests/v3_2_core_checker_tests.ts'
            ],
            remainingBoundary:
                'Delete the encoding-specific legacy test in MIGRATE-2.'
        },
        {
            file: 'tests/let_binding_tests.ts',
            disposition: 'defer-delete',
            retainedInvariant:
                'Shadowing and dependent substitution evidence; no Let node ' +
                'is currently in the reviewed Core.',
            replacementTests: [
                'tests/v3_2_core_binder_tests.ts',
                'tests/v3_2_core_context_tests.ts'
            ],
            remainingBoundary:
                'Delete the legacy Let API in MIGRATE-2; add a new surface ' +
                'Let only from a later consumer.'
        },
        {
            file: 'tests/phase1_tests.ts',
            disposition: 'delete-without-port',
            retainedInvariant:
                'No MkCat or ComposeMorph compatibility surface is retained.',
            replacementTests: [],
            remainingBoundary: 'Delete with the old category layer.'
        },
        {
            file: 'tests/kernel_implicits_tests.ts',
            disposition: 'replace-then-delete',
            retainedInvariant:
                'Schema-driven owner implicit recovery and clash rejection.',
            replacementTests: [
                'tests/v3_2_elab0_tests.ts',
                'tests/v3_2_core_checker_tests.ts'
            ],
            remainingBoundary: 'Delete the stale implicit-slot table tests.'
        },
        {
            file: 'tests/functorial_elaboration.ts',
            disposition: 'delete-without-port',
            retainedInvariant:
                'No MkFunctorTerm proof/coherence contract is retained.',
            replacementTests: [],
            remainingBoundary:
                'Delete with the obsolete one-category constructor layer.'
        },
        {
            file: 'tests/proof_mode_tests.ts',
            disposition: 'replace-then-delete',
            retainedInvariant:
                'Reachable-goal inspection/reporting and checked intro, exact, ' +
                'and apply refinement.',
            replacementTests: [
                'tests/v3_2_proof_state_tests.ts',
                'tests/v3_2_proof_refinement_tests.ts'
            ],
            remainingBoundary:
                'Delete mutable holes, global lookup, and category-tag ' +
                'traversal with the legacy proof module in MIGRATE-2.'
        },
        {
            file: 'tests/emdash2_functor_transfor_tests.ts',
            disposition: 'replace-then-delete',
            retainedInvariant:
                'Binder modes, ordinary/displayed owner typing, endpoint ' +
                'negatives, and reviewed projection computation.',
            replacementTests: [
                'tests/v3_2_elab0_tests.ts',
                'tests/v3_2_dependent_context_tests.ts',
                'tests/v3_2_differential_higher_cell_tests.ts'
            ],
            remainingBoundary:
                'Delete stale category spellings and reductions in MIGRATE-2.'
        },
        {
            file: 'tests/emdash2_homd_curry_alias_tests.ts',
            disposition: 'split-then-delete',
            retainedInvariant:
                'Binder-mode checking and internal-Hom variance, not the ' +
                'retired alias API.',
            replacementTests: [
                'tests/v3_2_elab1c_tests.ts',
                'tests/v3_2_core_checker_tests.ts'
            ],
            remainingBoundary:
                'Delete the alias and compatibility tests in MIGRATE-2.'
        },
        {
            file: 'tests/emdash2_internalized_category_layer_tests.ts',
            disposition: 'replace-then-delete',
            retainedInvariant:
                'Recursive object-category recovery and internalized owner ' +
                'typing.',
            replacementTests: [
                'tests/v3_2_elab1c_tests.ts',
                'tests/v3_2_dependent_context_tests.ts',
                'tests/v3_2_differential_owner_tests.ts'
            ],
            remainingBoundary:
                'Delete the stale internalized category layer in MIGRATE-2.'
        },
        {
            file: 'tests/parser_tests.ts',
            disposition: 'defer-delete',
            retainedInvariant:
                'No legacy token grammar is retained as product behavior.',
            replacementTests: [],
            remainingBoundary:
                'Delete in MIGRATE-2; a replacement parser requires H-06.'
        }
    ],
    nextSlice: 'MIGRATE-2'
};

export const LEGACY_MIGRATION_INVENTORY = deepFreeze(canonicalInventory);

const sameInventory = (
    left: LegacyMigrationInventory,
    right: LegacyMigrationInventory
): boolean => JSON.stringify(left) === JSON.stringify(right);

/**
 * Reject any drift from the reviewed MIGRATE-1D inventory.
 *
 * The migration ledger is deliberately closed-world: adding a legacy root
 * source or test requires an explicit disposition before deletion can
 * proceed.
 */
export function validateLegacyMigrationInventory(
    inventory: LegacyMigrationInventory = LEGACY_MIGRATION_INVENTORY
): void {
    if (!sameInventory(inventory, canonicalInventory)) {
        throw new Error(
            'Legacy migration inventory differs from the canonical ' +
            'MIGRATE-1D disposition ledger'
        );
    }
}

export type LegacyMigrationRequiredEditKind =
    | 'runner'
    | 'audit-transition'
    | 'fixture-api'
    | 'fixture-consumer'
    | 'fixture-documentation'
    | 'package-manifest'
    | 'package-lock';

export interface LegacyMigrationRequiredEdit {
    readonly file: string;
    readonly kind: LegacyMigrationRequiredEditKind;
    readonly completionCriterion: string;
}

export interface LegacyMigrationDeletionBoundary {
    readonly sourceFiles: readonly string[];
    readonly testFiles: readonly string[];
    readonly auxiliaryFiles: readonly string[];
    readonly requiredEdits: readonly LegacyMigrationRequiredEdit[];
}

export interface LegacyMigrationReadiness {
    readonly revision: 'MIGRATE-1D';
    readonly status: 'ready-for-physical-deletion';
    readonly inventoryRevision: 'MIGRATE-1D';
    readonly nextSlice: 'MIGRATE-2';
    readonly deletionBoundary: LegacyMigrationDeletionBoundary;
    readonly checkpointGates: readonly string[];
    readonly retainedAuthorityBoundary: string;
}

const canonicalReadiness: LegacyMigrationReadiness = {
    revision: 'MIGRATE-1D',
    status: 'ready-for-physical-deletion',
    inventoryRevision: canonicalInventory.revision,
    nextSlice: 'MIGRATE-2',
    deletionBoundary: {
        sourceFiles: canonicalInventory.sourceFiles.map(entry => entry.file),
        testFiles: canonicalInventory.testFiles.map(entry => entry.file),
        auxiliaryFiles: [
            'tests/utils.ts'
        ],
        requiredEdits: [
            {
                file: 'tests/main_tests.ts',
                kind: 'runner',
                completionCriterion:
                    'Remove the legacy state import, debug setup, and every ' +
                    'legacy test side-effect import while retaining the ' +
                    'v3.2 runner.'
            },
            {
                file: 'tests/v3_2_migration_inventory_tests.ts',
                kind: 'audit-transition',
                completionCriterion:
                    'Replace the pre-deletion presence audit with an exact ' +
                    'post-deletion absence and retained-suite audit.'
            },
            {
                file: 'tests/v3_2_migration_readiness_tests.ts',
                kind: 'audit-transition',
                completionCriterion:
                    'Replace the readiness import graph with a post-deletion ' +
                    'forbidden-import and consumer-completion audit.'
            },
            {
                file: 'emdash-template/src/emdash_api.ts',
                kind: 'fixture-api',
                completionCriterion:
                    'Export only the v3.2 API required by the fixture; add ' +
                    'no legacy compatibility barrel.'
            },
            {
                file: 'emdash-template/src/App.tsx',
                kind: 'fixture-consumer',
                completionCriterion:
                    'Replace the legacy global-reset/elaborate example with ' +
                    'a session-local v3.2 constructor/checker example.'
            },
            {
                file: 'emdash-template/README.md',
                kind: 'fixture-documentation',
                completionCriterion:
                    'Describe packaging src/v3_2 and the v3.2 barrel rather ' +
                    'than copying the deleted root engine.'
            },
            {
                file: 'package.json',
                kind: 'package-manifest',
                completionCriterion:
                    'Remove the parser-only parsimmon runtime dependency.'
            },
            {
                file: 'pnpm-lock.yaml',
                kind: 'package-lock',
                completionCriterion:
                    'Regenerate the shared lockfile with the owning pnpm ' +
                    'wrapper after removing parsimmon.'
            }
        ]
    },
    checkpointGates: [
        'node --require ts-node/register --test ' +
            'tests/v3_2_migration_inventory_tests.ts ' +
            'tests/v3_2_migration_readiness_tests.ts ' +
            'tests/v3_2_pattern_unification_tests.ts ' +
            'tests/v3_2_proof_state_tests.ts ' +
            'tests/v3_2_proof_refinement_tests.ts',
        'node --require ts-node/register --test tests/v3_2_*_tests.ts',
        './scripts/pnpmw run check:ts',
        'EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check',
        'EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all',
        'git diff --check'
    ],
    retainedAuthorityBoundary:
        'Lambdapi remains the executable specification and required ' +
        'conformance oracle through GRADUATE-1/H-05. MIGRATE-2 deletes no ' +
        'active emdash2 authority and introduces no D0/D1 or legacy category ' +
        'compatibility API.'
};

export const LEGACY_MIGRATION_READINESS = deepFreeze(canonicalReadiness);

const sameReadiness = (
    left: LegacyMigrationReadiness,
    right: LegacyMigrationReadiness
): boolean => JSON.stringify(left) === JSON.stringify(right);

/**
 * Reject drift from the exact physical-deletion boundary reviewed by
 * MIGRATE-1D.
 */
export function validateLegacyMigrationReadiness(
    readiness: LegacyMigrationReadiness = LEGACY_MIGRATION_READINESS
): void {
    if (!sameReadiness(readiness, canonicalReadiness)) {
        throw new Error(
            'Legacy migration readiness differs from the canonical ' +
            'MIGRATE-1D physical-deletion boundary'
        );
    }
}

export interface LegacyMigrationCompletion {
    readonly revision: 'MIGRATE-2';
    readonly status: 'complete';
    readonly readinessRevision: 'MIGRATE-1D';
    readonly deletedFiles: readonly string[];
    readonly completedEdits: readonly string[];
    readonly removedRuntimeDependencies: readonly ['parsimmon'];
    readonly browserEntryPoint: 'src/v3_2/browser.ts';
    readonly compatibilityApiRetained: false;
    readonly parserReplacement: 'not-implemented-h06-required';
    readonly nextSlice: 'GRADUATE-1';
}

const canonicalCompletion: LegacyMigrationCompletion = {
    revision: 'MIGRATE-2',
    status: 'complete',
    readinessRevision: canonicalReadiness.revision,
    deletedFiles: [
        ...canonicalReadiness.deletionBoundary.sourceFiles,
        ...canonicalReadiness.deletionBoundary.testFiles,
        ...canonicalReadiness.deletionBoundary.auxiliaryFiles
    ],
    completedEdits:
        canonicalReadiness.deletionBoundary.requiredEdits.map(
            edit => edit.file
        ),
    removedRuntimeDependencies: ['parsimmon'],
    browserEntryPoint: 'src/v3_2/browser.ts',
    compatibilityApiRetained: false,
    parserReplacement: 'not-implemented-h06-required',
    nextSlice: 'GRADUATE-1'
};

export const LEGACY_MIGRATION_COMPLETION = deepFreeze(canonicalCompletion);

const sameCompletion = (
    left: LegacyMigrationCompletion,
    right: LegacyMigrationCompletion
): boolean => JSON.stringify(left) === JSON.stringify(right);

/**
 * Reject drift from the reviewed MIGRATE-2 physical-deletion result.
 */
export function validateLegacyMigrationCompletion(
    completion: LegacyMigrationCompletion = LEGACY_MIGRATION_COMPLETION
): void {
    if (!sameCompletion(completion, canonicalCompletion)) {
        throw new Error(
            'Legacy migration completion differs from the canonical ' +
            'MIGRATE-2 deletion result'
        );
    }
}
