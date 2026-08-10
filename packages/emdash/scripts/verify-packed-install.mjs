import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import {
  mkdir,
  mkdtemp,
  readdir,
  readFile,
  rm,
  stat,
  writeFile,
} from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import { validateEmdashNpmReleasePreflight } from './release-preflight.mjs';

const packageRoot = path.resolve(
  path.dirname(fileURLToPath(import.meta.url)),
  '..',
);
const repositoryRoot = path.resolve(packageRoot, '..', '..');
const pnpmWrapper = path.join(repositoryRoot, 'scripts', 'pnpmw');

const arguments_ = process.argv.slice(2);
let suppliedTarball;
if (arguments_.length > 0) {
  if (
    arguments_.length !== 2 ||
    arguments_[0] !== '--tarball' ||
    arguments_[1].length === 0
  ) {
    throw new Error(
      'Usage: verify-packed-install.mjs [--tarball /absolute/package.tgz]',
    );
  }
  suppliedTarball = path.resolve(arguments_[1]);
  const tarballStat = await stat(suppliedTarball);
  if (!tarballStat.isFile()) {
    throw new Error(`Supplied tarball is not a file: ${suppliedTarball}`);
  }
}

const run = (command, args, cwd, capture = false) => execFileSync(
  command,
  args,
  {
    cwd,
    encoding: 'utf8',
    stdio: capture ? ['ignore', 'pipe', 'inherit'] : 'inherit',
  },
);

const temporaryRoot = await mkdtemp(
  path.join(os.tmpdir(), 'emdash-packed-install-'),
);
const tarballDirectory = path.join(temporaryRoot, 'tarballs');
const consumerDirectory = path.join(temporaryRoot, 'consumer');

const collectPackageFiles = async (root, relative = '') => {
  const files = [];
  const entries = await readdir(path.join(root, relative), {
    withFileTypes: true,
  });
  for (const entry of entries) {
    const entryRelative = relative
      ? path.posix.join(relative, entry.name)
      : entry.name;
    if (entry.isDirectory()) {
      files.push(...await collectPackageFiles(root, entryRelative));
    } else if (entry.isFile()) {
      files.push(entryRelative);
    } else {
      throw new Error(
        `Packed package contains unsupported entry ${entryRelative}`,
      );
    }
  }
  return files;
};

try {
  await mkdir(consumerDirectory);

  let tarball = suppliedTarball;
  if (!tarball) {
    await mkdir(tarballDirectory);
    const packOutput = run(
      pnpmWrapper,
      [
        '--dir',
        packageRoot,
        'pack',
        '--json',
        '--pack-destination',
        tarballDirectory,
      ],
      repositoryRoot,
      true,
    );
    const packed = JSON.parse(packOutput);
    const packedRecord = Array.isArray(packed) ? packed[0] : packed;
    tarball = path.resolve(
      tarballDirectory,
      packedRecord.filename ?? packedRecord.path,
    );
  }

  await writeFile(
    path.join(consumerDirectory, 'package.json'),
    `${JSON.stringify({
      name: 'emdash-packed-install-smoke',
      private: true,
      type: 'module',
    }, null, 2)}\n`,
  );
  run(
    pnpmWrapper,
    [
      '--dir',
      consumerDirectory,
      'add',
      '--ignore-scripts',
      '--offline',
      tarball,
    ],
    repositoryRoot,
  );

  const installedRoot = path.join(
    consumerDirectory,
    'node_modules',
    '@hotdocx',
    'emdash',
  );
  const installedManifest = JSON.parse(
    await readFile(path.join(installedRoot, 'package.json'), 'utf8'),
  );
  const packedFiles = new Set(await collectPackageFiles(installedRoot));
  validateEmdashNpmReleasePreflight({
    manifest: installedManifest,
    repository: 'hotdocx/emdash',
    tag: `emdash-v${installedManifest.version}`,
  });
  for (const requiredFile of [
    'dist/index.js',
    'dist/index.cjs',
    'dist/authoring.js',
    'dist/authoring.cjs',
    'dist/workspace.js',
    'dist/workspace.cjs',
    'dist/types/package_core.d.ts',
    'dist/types/package_core.d.ts.map',
    'dist/types/package_authoring.d.ts',
    'dist/types/package_authoring.d.ts.map',
    'dist/types/package_workspace.d.ts',
    'dist/types/package_workspace.d.ts.map',
    'dist/types/package.json',
    'LICENSE',
    'README.md',
    'package.json',
  ]) {
    assert.equal(
      packedFiles.has(requiredFile),
      true,
      `packed package is missing ${requiredFile}`,
    );
  }
  const forbiddenDeclaration = new RegExp(
    '^dist/types/(?:surface|elaborator|lf_remote_workspace|' +
      'lf_transfer_acquisition|[^/]*_cli)\\.d\\.ts$',
    'u',
  );
  for (const file of packedFiles) {
    assert.equal(
      /^(?:scripts|src)\//u.test(file) || file.endsWith('package-lock.json'),
      false,
      `packed package leaked contributor input ${file}`,
    );
    assert.equal(
      forbiddenDeclaration.test(file),
      false,
      `packed package leaked forbidden declaration ${file}`,
    );
  }
  assert.equal(installedManifest.name, '@hotdocx/emdash');
  assert.equal(installedManifest.version, '0.2.0');
  assert.equal(
    installedManifest.scripts,
    undefined,
    'published package must not retain contributor-only scripts',
  );
  assert.deepEqual(
    Object.keys(installedManifest.exports),
    ['.', './authoring', './workspace', './package.json'],
  );
  assert.equal(installedManifest.dependencies, undefined);
  assert.equal(
    JSON.parse(
      await readFile(
        path.join(installedRoot, 'dist', 'types', 'package.json'),
        'utf8',
      ),
    ).type,
    'commonjs',
  );

  await writeFile(
    path.join(consumerDirectory, 'consumer.mjs'),
    `import assert from 'node:assert/strict';
import { CoreChecker, CORE_MVP_MANIFEST } from '@hotdocx/emdash';
import {
  CORE_LF_INSTANCE_SYNTHESIS_PROFILE,
  CORE_LF_INSTANCE_ROLE_SYNTHESIS_PROFILE,
  CORE_LF_INSTANCE_SCOPE_PROFILE,
  CoreLfScopedBuilder,
  synthesizeCoreLfInstance,
  synthesizeCoreLfInstanceByRoles,
} from '@hotdocx/emdash/authoring';
import {
  CORE_LF_DEVELOPMENT_DIFF_PROFILE,
  CORE_LF_PROOF_MAINTENANCE_PROFILE,
  CORE_LF_DECLARATION_WORKSPACE_PROFILE,
  CORE_LF_PREMISE_INDEX_PROFILE,
  CORE_LF_PROOF_DEVELOPMENT_PROFILE,
  CORE_LF_PROOF_DEVELOPMENT_SOURCE_PROFILE,
  CORE_OBVIOUS_PROOF_PROVIDER_PROFILE,
  CORE_PROOF_CHECKER_PROFILE,
  CORE_PROOF_PLAN_PROFILE,
  CORE_PROOF_PLAN_MACRO_PROFILE,
  CORE_PROOF_PLAN_PATCH_PROFILE,
  CORE_PROOF_GOAL_COUPLING_PROFILE,
  CORE_PROOF_REFINE_TEMPLATE_PROFILE,
  CORE_PROOF_SIMPLIFIER_PROFILE,
  CORE_RESEARCH_GOAL_GRAPH_PROFILE,
  CORE_RESEARCH_GOAL_VIEW_PROFILE,
  binderMode,
  compileCoreLfDeclarationWorkspace,
  compileCoreLfWorkspaceProofDocument,
  coreLfQualifiedSymbol,
  coreLfTransferAbsentBody,
  coreProofPlanConstructor,
  coreProofPlanExact,
  coreProofPlanHave,
  coreProofPlanHole,
  coreProofPlanIntro,
  coreProofPlanRefine,
  coreProofTemplatePlaceholder,
  applyCoreProofPlanPatch,
  compareCoreLfProofDevelopmentSources,
  inspectCoreLfProofMaintenance,
  CoreProofChecker,
  createCoreProofPlanHoleReplacement,
  createCoreLfAccessiblePremiseIndex,
  createCoreLfDeclarationWorkspace,
  createCoreLfModuleSpec,
  createCoreLfProofDevelopment,
  createCoreLfTransferDeclarationLinkage,
  createCoreLfTransferPolicyOverlay,
  createCoreProofArtifactFingerprint,
  createCoreResearchGoalGraphDefinition,
  createCoreResearchGoalView,
  evaluateCoreResearchGoalGraph,
  kernelBinder,
  kernelBound,
  kernelFree,
  kernelPi,
  parseCoreLfProofDevelopmentSourceText,
  parseCoreResearchGoalViewText,
  provenance,
  proposeCoreObviousProofPlanPatches,
  proposeCoreLfProofRepairs,
  replayCoreObviousProofCandidate,
  replayCoreLfProofRepairCandidate,
  serializeCoreLfDevelopmentSemanticDiff,
  serializeCoreLfProofMaintenanceInspection,
  serializeCoreLfProofRepairCandidateReplay,
  serializeCoreLfProofRepairProposal,
  serializeCoreProofGoalCouplingGraph,
  serializeCoreResearchGoalView,
  searchCoreLfAccessiblePremises,
  simplifyCoreProofPlan,
  sourceSpan,
  validateCoreResearchGoalView,
} from '@hotdocx/emdash/workspace';

assert.equal(typeof CoreChecker, 'function');
assert.equal(typeof CoreLfScopedBuilder, 'function');
assert.equal(typeof synthesizeCoreLfInstance, 'function');
assert.equal(typeof synthesizeCoreLfInstanceByRoles, 'function');
assert.equal(CORE_MVP_MANIFEST.status, 'frozen-reviewed');
assert.equal(
  CORE_LF_INSTANCE_SCOPE_PROFILE.productionLambdapiDependency,
  false,
);
assert.equal(
  CORE_LF_INSTANCE_SYNTHESIS_PROFILE.revision,
  'emdash-lf-instance-synthesis-v2',
);
assert.equal(
  CORE_LF_INSTANCE_ROLE_SYNTHESIS_PROFILE.productionLambdapiDependency,
  false,
);
assert.equal(
  CORE_LF_DEVELOPMENT_DIFF_PROFILE.revision,
  'emdash-lf-development-diff-v1',
);
assert.equal(
  CORE_LF_PROOF_MAINTENANCE_PROFILE.revision,
  'emdash-lf-proof-maintenance-v1',
);
assert.equal(
  CORE_LF_DECLARATION_WORKSPACE_PROFILE.nodeBuiltinDependency,
  false,
);
assert.equal(
  CORE_LF_PREMISE_INDEX_PROFILE.revision,
  'emdash-lf-premise-index-v1',
);
assert.equal(
  CORE_LF_PROOF_DEVELOPMENT_PROFILE.nodeBuiltinDependency,
  false,
);
assert.equal(
  CORE_LF_PROOF_DEVELOPMENT_SOURCE_PROFILE.nodeBuiltinDependency,
  false,
);
assert.equal(
  CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.revision,
  'emdash-obvious-proof-provider-v1',
);
assert.equal(
  CORE_PROOF_PLAN_PROFILE.revision,
  'emdash-proof-plan-v2',
);
assert.equal(
  CORE_PROOF_PLAN_MACRO_PROFILE.revision,
  'emdash-proof-plan-macros-v1',
);
assert.equal(
  CORE_PROOF_PLAN_PATCH_PROFILE.revision,
  'emdash-proof-plan-patch-v1',
);
assert.equal(
  CORE_PROOF_GOAL_COUPLING_PROFILE.revision,
  'emdash-proof-goal-coupling-v1',
);
assert.equal(
  CORE_PROOF_REFINE_TEMPLATE_PROFILE.revision,
  'emdash-proof-refine-template-v1',
);
assert.equal(
  CORE_PROOF_SIMPLIFIER_PROFILE.revision,
  'emdash-proof-simplifier-v1',
);
assert.equal(
  CORE_RESEARCH_GOAL_GRAPH_PROFILE.revision,
  'emdash-research-goal-graph-v1',
);
assert.equal(
  CORE_RESEARCH_GOAL_VIEW_PROFILE.revision,
  'emdash-research-goal-view-v1',
);
assert.equal(typeof coreProofPlanConstructor, 'function');
assert.equal(typeof coreProofPlanHave, 'function');
assert.equal(typeof coreProofPlanRefine, 'function');
assert.equal(typeof coreProofTemplatePlaceholder, 'function');
assert.equal(typeof applyCoreProofPlanPatch, 'function');
assert.equal(typeof compareCoreLfProofDevelopmentSources, 'function');
assert.equal(typeof inspectCoreLfProofMaintenance, 'function');
assert.equal(typeof createCoreProofPlanHoleReplacement, 'function');
assert.equal(typeof createCoreLfAccessiblePremiseIndex, 'function');
assert.equal(typeof createCoreLfProofDevelopment, 'function');
assert.equal(typeof createCoreResearchGoalGraphDefinition, 'function');
assert.equal(typeof createCoreResearchGoalView, 'function');
assert.equal(typeof evaluateCoreResearchGoalGraph, 'function');
assert.equal(typeof CoreProofChecker, 'function');
assert.equal(
  CORE_PROOF_CHECKER_PROFILE.permitsAnnotatedLambdaInference,
  false,
);
assert.equal(typeof parseCoreLfProofDevelopmentSourceText, 'function');
assert.equal(typeof parseCoreResearchGoalViewText, 'function');
assert.equal(typeof proposeCoreObviousProofPlanPatches, 'function');
assert.equal(typeof proposeCoreLfProofRepairs, 'function');
assert.equal(typeof replayCoreObviousProofCandidate, 'function');
assert.equal(typeof replayCoreLfProofRepairCandidate, 'function');
assert.equal(typeof serializeCoreLfDevelopmentSemanticDiff, 'function');
assert.equal(typeof serializeCoreLfProofMaintenanceInspection, 'function');
assert.equal(typeof serializeCoreLfProofRepairCandidateReplay, 'function');
assert.equal(typeof serializeCoreLfProofRepairProposal, 'function');
assert.equal(typeof serializeCoreProofGoalCouplingGraph, 'function');
assert.equal(typeof serializeCoreResearchGoalView, 'function');
assert.equal(typeof searchCoreLfAccessiblePremises, 'function');
assert.equal(typeof simplifyCoreProofPlan, 'function');
assert.equal(typeof validateCoreResearchGoalView, 'function');

// Preserve the public 0.1 hosted-consumer path over direct TypeScript source.
const compatibilityHash = (digit) => 'sha256:' + digit.repeat(64);
const compatibilityProvenance = provenance(
  'surface',
  '0.1 installed-consumer compatibility',
  sourceSpan('compatibility.emdash.ts', 1, 1, 1, 2),
);
const compatibilityModuleId = 'compat.identity';
const compatibilitySymbol = coreLfQualifiedSymbol(
  compatibilityModuleId,
  'A',
);
const compatibilityModule = createCoreLfModuleSpec({
  revision: 'compat-module-1',
  moduleId: compatibilityModuleId,
  fragmentId: 'declarations',
  authorityPath: 'compatibility.emdash.ts',
  sourceSha256: compatibilityHash('a'),
  dependencies: [],
  externalSymbols: [],
  declarations: [{
    order: 0,
    symbol: compatibilitySymbol,
    type: { tag: 'type' },
    body: coreLfTransferAbsentBody(),
    modifiers: {
      visibility: 'public',
      rigidity: 'ordinary',
      sourceOpacity: 'opaque',
    },
    provenance: {
      authorityPath: 'compatibility.emdash.ts',
      sourceFragment: 'symbol A : TYPE;',
    },
  }],
  inductives: [],
  runtimeRules: [],
  proofRules: [],
});
const compatibilityPolicy = createCoreLfTransferPolicyOverlay(
  compatibilityModule,
  {
    revision: 'compat-policy-1',
    moduleRevision: compatibilityModule.revision,
    entries: [{
      order: 0,
      target: { kind: 'declaration', symbol: compatibilitySymbol },
      policy: 'opaque-signature',
      evidence: 'public 0.1 hosted-consumer compatibility',
    }],
  },
);
const compatibilityLinkage = createCoreLfTransferDeclarationLinkage(
  compatibilityModule,
  {
    revision: 'compat-linkage-1',
    moduleRevision: compatibilityModule.revision,
    entries: [{
      order: 0,
      symbol: compatibilitySymbol,
      kind: 'free-declaration',
      coreName: 'compat_A',
      backendName: 'A',
    }],
  },
);
const compatibilityWorkspace = compileCoreLfDeclarationWorkspace(
  createCoreLfDeclarationWorkspace({
    revision: 'compat-workspace-1',
    modules: [{
      module: compatibilityModule,
      policy: compatibilityPolicy,
      linkage: compatibilityLinkage,
    }],
  }),
);
const compatibilityType = kernelPi(
  kernelBinder(
    'value',
    kernelFree('compat_A', compatibilityProvenance),
    binderMode('explicit', 'functorial'),
    compatibilityProvenance,
  ),
  kernelFree('compat_A', compatibilityProvenance),
  compatibilityProvenance,
);
const compatibilityFingerprint = createCoreProofArtifactFingerprint({
  source: {
    id: 'compatibility.emdash.ts#identity',
    sha256: compatibilityHash('b'),
  },
  profileSha256: compatibilityHash('c'),
  dependencies: [{
    moduleId: compatibilityModuleId,
    interfaceSha256: compatibilityHash('d'),
  }],
});
const compatibilityProof = (open) => ({
  moduleId: compatibilityModuleId,
  declarationId: open ? 'open_identity' : 'complete_identity',
  type: compatibilityType,
  plan: coreProofPlanIntro(
    open
      ? coreProofPlanHole('body', { provenance: compatibilityProvenance })
      : coreProofPlanExact(kernelBound(0, compatibilityProvenance)),
    { name: 'value', provenance: compatibilityProvenance },
  ),
  provenance: compatibilityProvenance,
  fingerprint: compatibilityFingerprint,
});
const compatibilityComplete = compileCoreLfWorkspaceProofDocument(
  compatibilityWorkspace,
  compatibilityProof(false),
).artifact.proofArtifact;
const compatibilityOpen = compileCoreLfWorkspaceProofDocument(
  compatibilityWorkspace,
  compatibilityProof(true),
).artifact.proofArtifact;
assert.equal(compatibilityComplete.state.status, 'complete');
assert.equal(compatibilityOpen.state.status, 'incomplete');
assert.deepEqual(
  compatibilityOpen.state.goals.map((goal) => goal.id),
  ['body'],
);
`,
  );
  await writeFile(
    path.join(consumerDirectory, 'consumer.cjs'),
    `const assert = require('node:assert/strict');
const core = require('@hotdocx/emdash');
const authoring = require('@hotdocx/emdash/authoring');
const workspace = require('@hotdocx/emdash/workspace');

assert.equal(typeof core.CoreChecker, 'function');
assert.equal(typeof authoring.CoreLfScopedBuilder, 'function');
assert.equal(typeof authoring.synthesizeCoreLfInstance, 'function');
assert.equal(typeof authoring.synthesizeCoreLfInstanceByRoles, 'function');
assert.equal(
  authoring.CORE_LF_INSTANCE_SYNTHESIS_PROFILE.revision,
  'emdash-lf-instance-synthesis-v2',
);
assert.equal(
  authoring.CORE_LF_INSTANCE_ROLE_SYNTHESIS_PROFILE.performsIo,
  false,
);
assert.equal(
  workspace.CORE_LF_DEVELOPMENT_DIFF_PROFILE.compilesProofs,
  false,
);
assert.equal(
  workspace.CORE_LF_PROOF_MAINTENANCE_PROFILE.retainsSessionState,
  false,
);
assert.equal(
  workspace.CORE_LF_DECLARATION_WORKSPACE_PROFILE.nodeBuiltinDependency,
  false,
);
assert.equal(
  workspace.CORE_LF_PREMISE_INDEX_PROFILE.performsIo,
  false,
);
assert.equal(
  workspace.CORE_LF_PROOF_DEVELOPMENT_PROFILE.nodeBuiltinDependency,
  false,
);
assert.equal(
  workspace.CORE_LF_PROOF_DEVELOPMENT_SOURCE_PROFILE.hostExecutionTrusted,
  false,
);
assert.equal(
  workspace.CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.randomizes,
  false,
);
assert.equal(
  workspace.CORE_PROOF_PLAN_PROFILE.revision,
  'emdash-proof-plan-v2',
);
assert.equal(
  workspace.CORE_PROOF_PLAN_MACRO_PROFILE.addsProofPlanTags,
  false,
);
assert.equal(
  workspace.CORE_PROOF_PLAN_PATCH_PROFILE.performsSemanticChecks,
  false,
);
assert.equal(
  workspace.CORE_PROOF_GOAL_COUPLING_PROFILE.addsProofStateFields,
  false,
);
assert.equal(
  workspace.CORE_PROOF_REFINE_TEMPLATE_PROFILE.addsProofPlanTags,
  false,
);
assert.equal(
  workspace.CORE_PROOF_SIMPLIFIER_PROFILE.addsProofPlanTags,
  false,
);
assert.equal(
  workspace.CORE_RESEARCH_GOAL_GRAPH_PROFILE.revision,
  'emdash-research-goal-graph-v1',
);
assert.equal(
  workspace.CORE_RESEARCH_GOAL_VIEW_PROFILE.portableProjectionOnly,
  true,
);
assert.equal(typeof workspace.coreProofPlanConstructor, 'function');
assert.equal(typeof workspace.coreProofPlanHave, 'function');
assert.equal(typeof workspace.coreProofPlanRefine, 'function');
assert.equal(typeof workspace.coreProofTemplatePlaceholder, 'function');
assert.equal(
  typeof workspace.compileCoreLfDeclarationWorkspace,
  'function',
);
assert.equal(
  typeof workspace.compileCoreLfWorkspaceProofDocument,
  'function',
);
assert.equal(typeof workspace.applyCoreProofPlanPatch, 'function');
assert.equal(
  typeof workspace.compareCoreLfProofDevelopmentSources,
  'function',
);
assert.equal(typeof workspace.inspectCoreLfProofMaintenance, 'function');
assert.equal(
  typeof workspace.createCoreProofPlanHoleReplacement,
  'function',
);
assert.equal(
  typeof workspace.createCoreLfAccessiblePremiseIndex,
  'function',
);
assert.equal(typeof workspace.createCoreLfProofDevelopment, 'function');
assert.equal(
  typeof workspace.createCoreResearchGoalGraphDefinition,
  'function',
);
assert.equal(typeof workspace.createCoreResearchGoalView, 'function');
assert.equal(typeof workspace.evaluateCoreResearchGoalGraph, 'function');
assert.equal(typeof workspace.CoreProofChecker, 'function');
assert.equal(
  workspace.CORE_PROOF_CHECKER_PROFILE.acceptsCatalogRuntime,
  false,
);
assert.equal(
  typeof workspace.parseCoreLfProofDevelopmentSourceText,
  'function',
);
assert.equal(typeof workspace.parseCoreResearchGoalViewText, 'function');
assert.equal(
  typeof workspace.proposeCoreObviousProofPlanPatches,
  'function',
);
assert.equal(typeof workspace.proposeCoreLfProofRepairs, 'function');
assert.equal(
  typeof workspace.replayCoreObviousProofCandidate,
  'function',
);
assert.equal(
  typeof workspace.replayCoreLfProofRepairCandidate,
  'function',
);
assert.equal(
  typeof workspace.serializeCoreLfDevelopmentSemanticDiff,
  'function',
);
assert.equal(
  typeof workspace.serializeCoreLfProofMaintenanceInspection,
  'function',
);
assert.equal(
  typeof workspace.serializeCoreLfProofRepairCandidateReplay,
  'function',
);
assert.equal(
  typeof workspace.serializeCoreLfProofRepairProposal,
  'function',
);
assert.equal(
  typeof workspace.serializeCoreProofGoalCouplingGraph,
  'function',
);
assert.equal(typeof workspace.serializeCoreResearchGoalView, 'function');
assert.equal(
  typeof workspace.searchCoreLfAccessiblePremises,
  'function',
);
assert.equal(typeof workspace.simplifyCoreProofPlan, 'function');
assert.equal(typeof workspace.validateCoreResearchGoalView, 'function');
`,
  );
  await writeFile(
    path.join(consumerDirectory, 'consumer.ts'),
    `import {
  CORE_MVP_MANIFEST,
  CoreChecker,
  type KernelExpression,
} from '@hotdocx/emdash';
import {
  CORE_LF_INSTANCE_SYNTHESIS_PROFILE,
  CORE_LF_INSTANCE_ROLE_SYNTHESIS_PROFILE,
  CORE_LF_INSTANCE_SCOPE_PROFILE,
  CoreLfScopedBuilder,
  synthesizeCoreLfInstance,
  synthesizeCoreLfInstanceByRoles,
} from '@hotdocx/emdash/authoring';
import {
  CORE_LF_DEVELOPMENT_DIFF_PROFILE,
  CORE_LF_PROOF_MAINTENANCE_PROFILE,
  CORE_LF_DECLARATION_WORKSPACE_PROFILE,
  CORE_LF_PREMISE_INDEX_PROFILE,
  CORE_LF_PROOF_DEVELOPMENT_PROFILE,
  CORE_LF_PROOF_DEVELOPMENT_SOURCE_PROFILE,
  CORE_OBVIOUS_PROOF_PROVIDER_PROFILE,
  CORE_PROOF_CHECKER_PROFILE,
  CORE_PROOF_PLAN_PROFILE,
  CORE_PROOF_PLAN_MACRO_PROFILE,
  CORE_PROOF_PLAN_PATCH_PROFILE,
  CORE_PROOF_GOAL_COUPLING_PROFILE,
  CORE_PROOF_REFINE_TEMPLATE_PROFILE,
  CORE_PROOF_SIMPLIFIER_PROFILE,
  CORE_RESEARCH_GOAL_GRAPH_PROFILE,
  CORE_RESEARCH_GOAL_VIEW_PROFILE,
  type CoreLfCompiledDeclarationWorkspace,
  type CoreLfWorkspaceProofCompilation,
  compileCoreLfDeclarationWorkspace,
  compileCoreLfWorkspaceProofDocument,
  coreProofPlanConstructor,
  coreProofPlanHave,
  coreProofPlanRefine,
  coreProofTemplatePlaceholder,
  applyCoreProofPlanPatch,
  compareCoreLfProofDevelopmentSources,
  inspectCoreLfProofMaintenance,
  CoreProofChecker,
  createCoreProofPlanHoleReplacement,
  createCoreLfAccessiblePremiseIndex,
  createCoreLfProofDevelopment,
  createCoreResearchGoalGraphDefinition,
  createCoreResearchGoalView,
  evaluateCoreResearchGoalGraph,
  parseCoreLfProofDevelopmentSourceText,
  parseCoreResearchGoalViewText,
  proposeCoreObviousProofPlanPatches,
  proposeCoreLfProofRepairs,
  replayCoreObviousProofCandidate,
  replayCoreLfProofRepairCandidate,
  serializeCoreLfDevelopmentSemanticDiff,
  serializeCoreLfProofMaintenanceInspection,
  serializeCoreLfProofRepairCandidateReplay,
  serializeCoreLfProofRepairProposal,
  serializeCoreProofGoalCouplingGraph,
  serializeCoreResearchGoalView,
  searchCoreLfAccessiblePremises,
  simplifyCoreProofPlan,
  validateCoreResearchGoalView,
} from '@hotdocx/emdash/workspace';

const checkerConstructor: typeof CoreChecker = CoreChecker;
const declarationWorkspaceCompiler:
  typeof compileCoreLfDeclarationWorkspace =
    compileCoreLfDeclarationWorkspace;
const workspaceProofCompiler: typeof compileCoreLfWorkspaceProofDocument =
  compileCoreLfWorkspaceProofDocument;
const maybeCompiledWorkspace:
  CoreLfCompiledDeclarationWorkspace | undefined = undefined;
const maybeWorkspaceProof:
  CoreLfWorkspaceProofCompilation | undefined = undefined;
const builder = new CoreLfScopedBuilder();
const exactSynthesizer: typeof synthesizeCoreLfInstance =
  synthesizeCoreLfInstance;
const roleSynthesizer: typeof synthesizeCoreLfInstanceByRoles =
  synthesizeCoreLfInstanceByRoles;
const maybeTerm: KernelExpression | undefined = undefined;
const developmentFactory: typeof createCoreLfProofDevelopment =
  createCoreLfProofDevelopment;
const premiseIndexFactory: typeof createCoreLfAccessiblePremiseIndex =
  createCoreLfAccessiblePremiseIndex;
const premiseSearch: typeof searchCoreLfAccessiblePremises =
  searchCoreLfAccessiblePremises;
const obviousProvider: typeof proposeCoreObviousProofPlanPatches =
  proposeCoreObviousProofPlanPatches;
const obviousReplay: typeof replayCoreObviousProofCandidate =
  replayCoreObviousProofCandidate;
const planPatch: typeof applyCoreProofPlanPatch = applyCoreProofPlanPatch;
const developmentDiff: typeof compareCoreLfProofDevelopmentSources =
  compareCoreLfProofDevelopmentSources;
const developmentDiffSerializer:
  typeof serializeCoreLfDevelopmentSemanticDiff =
    serializeCoreLfDevelopmentSemanticDiff;
const proofMaintenance: typeof inspectCoreLfProofMaintenance =
  inspectCoreLfProofMaintenance;
const proofRepairProvider: typeof proposeCoreLfProofRepairs =
  proposeCoreLfProofRepairs;
const proofRepairReplay: typeof replayCoreLfProofRepairCandidate =
  replayCoreLfProofRepairCandidate;
const proofMaintenanceSerializer:
  typeof serializeCoreLfProofMaintenanceInspection =
    serializeCoreLfProofMaintenanceInspection;
const proofRepairProposalSerializer:
  typeof serializeCoreLfProofRepairProposal =
    serializeCoreLfProofRepairProposal;
const proofRepairReplaySerializer:
  typeof serializeCoreLfProofRepairCandidateReplay =
    serializeCoreLfProofRepairCandidateReplay;
const holeReplacement: typeof createCoreProofPlanHoleReplacement =
  createCoreProofPlanHoleReplacement;
const proofCheckerConstructor: typeof CoreProofChecker = CoreProofChecker;
const sourceParser: typeof parseCoreLfProofDevelopmentSourceText =
  parseCoreLfProofDevelopmentSourceText;
const constructorMacro: typeof coreProofPlanConstructor =
  coreProofPlanConstructor;
const contextualHave: typeof coreProofPlanHave = coreProofPlanHave;
const refineTemplate: typeof coreProofPlanRefine = coreProofPlanRefine;
const placeholderBuilder: typeof coreProofTemplatePlaceholder =
  coreProofTemplatePlaceholder;
const graphSerializer: typeof serializeCoreProofGoalCouplingGraph =
  serializeCoreProofGoalCouplingGraph;
const proofSimplifier: typeof simplifyCoreProofPlan = simplifyCoreProofPlan;
const goalDefinitionFactory: typeof createCoreResearchGoalGraphDefinition =
  createCoreResearchGoalGraphDefinition;
const goalEvaluator: typeof evaluateCoreResearchGoalGraph =
  evaluateCoreResearchGoalGraph;
const goalViewFactory: typeof createCoreResearchGoalView =
  createCoreResearchGoalView;
const goalViewParser: typeof parseCoreResearchGoalViewText =
  parseCoreResearchGoalViewText;
const goalViewSerializer: typeof serializeCoreResearchGoalView =
  serializeCoreResearchGoalView;
const goalViewValidator: typeof validateCoreResearchGoalView =
  validateCoreResearchGoalView;
void checkerConstructor;
void declarationWorkspaceCompiler;
void workspaceProofCompiler;
void maybeCompiledWorkspace;
void maybeWorkspaceProof;
void builder;
void exactSynthesizer;
void roleSynthesizer;
void developmentFactory;
void premiseIndexFactory;
void premiseSearch;
void obviousProvider;
void obviousReplay;
void planPatch;
void developmentDiff;
void developmentDiffSerializer;
void proofMaintenance;
void proofRepairProvider;
void proofRepairReplay;
void proofMaintenanceSerializer;
void proofRepairProposalSerializer;
void proofRepairReplaySerializer;
void holeReplacement;
void proofCheckerConstructor;
void sourceParser;
void constructorMacro;
void contextualHave;
void refineTemplate;
void placeholderBuilder;
void graphSerializer;
void proofSimplifier;
void goalDefinitionFactory;
void goalEvaluator;
void goalViewFactory;
void goalViewParser;
void goalViewSerializer;
void goalViewValidator;
void maybeTerm;
void CORE_MVP_MANIFEST;
void CORE_LF_INSTANCE_SCOPE_PROFILE;
void CORE_LF_INSTANCE_SYNTHESIS_PROFILE;
void CORE_LF_INSTANCE_ROLE_SYNTHESIS_PROFILE;
void CORE_LF_DECLARATION_WORKSPACE_PROFILE;
void CORE_LF_DEVELOPMENT_DIFF_PROFILE;
void CORE_LF_PROOF_MAINTENANCE_PROFILE;
void CORE_LF_PREMISE_INDEX_PROFILE;
void CORE_LF_PROOF_DEVELOPMENT_PROFILE;
void CORE_LF_PROOF_DEVELOPMENT_SOURCE_PROFILE;
void CORE_OBVIOUS_PROOF_PROVIDER_PROFILE;
void CORE_PROOF_CHECKER_PROFILE;
void CORE_PROOF_PLAN_PROFILE;
void CORE_PROOF_PLAN_MACRO_PROFILE;
void CORE_PROOF_PLAN_PATCH_PROFILE;
void CORE_PROOF_GOAL_COUPLING_PROFILE;
void CORE_PROOF_REFINE_TEMPLATE_PROFILE;
void CORE_PROOF_SIMPLIFIER_PROFILE;
void CORE_RESEARCH_GOAL_GRAPH_PROFILE;
void CORE_RESEARCH_GOAL_VIEW_PROFILE;
`,
  );
  await writeFile(
    path.join(consumerDirectory, 'browser-entry.js'),
    `import { CoreChecker } from '@hotdocx/emdash';
import {
  CORE_LF_INSTANCE_SYNTHESIS_PROFILE,
  CORE_LF_INSTANCE_ROLE_SYNTHESIS_PROFILE,
  CoreLfScopedBuilder,
  synthesizeCoreLfInstance,
  synthesizeCoreLfInstanceByRoles,
} from '@hotdocx/emdash/authoring';
import {
  CORE_LF_DEVELOPMENT_DIFF_PROFILE,
  CORE_LF_PROOF_MAINTENANCE_PROFILE,
  CORE_LF_DECLARATION_WORKSPACE_PROFILE,
  CORE_LF_PREMISE_INDEX_PROFILE,
  CORE_LF_PROOF_DEVELOPMENT_PROFILE,
  CORE_LF_PROOF_DEVELOPMENT_SOURCE_PROFILE,
  CORE_OBVIOUS_PROOF_PROVIDER_PROFILE,
  CORE_PROOF_CHECKER_PROFILE,
  CORE_PROOF_PLAN_PROFILE,
  CORE_PROOF_PLAN_MACRO_PROFILE,
  CORE_PROOF_PLAN_PATCH_PROFILE,
  CORE_PROOF_GOAL_COUPLING_PROFILE,
  CORE_PROOF_REFINE_TEMPLATE_PROFILE,
  CORE_PROOF_SIMPLIFIER_PROFILE,
  CORE_RESEARCH_GOAL_GRAPH_PROFILE,
  CORE_RESEARCH_GOAL_VIEW_PROFILE,
  compileCoreLfDeclarationWorkspace,
  compileCoreLfWorkspaceProofDocument,
  coreProofPlanConstructor,
  coreProofPlanHave,
  coreProofPlanRefine,
  coreProofTemplatePlaceholder,
  applyCoreProofPlanPatch,
  compareCoreLfProofDevelopmentSources,
  inspectCoreLfProofMaintenance,
  CoreProofChecker,
  createCoreProofPlanHoleReplacement,
  createCoreLfAccessiblePremiseIndex,
  createCoreLfProofDevelopment,
  createCoreResearchGoalGraphDefinition,
  createCoreResearchGoalView,
  evaluateCoreResearchGoalGraph,
  parseCoreLfProofDevelopmentSourceText,
  parseCoreResearchGoalViewText,
  proposeCoreObviousProofPlanPatches,
  proposeCoreLfProofRepairs,
  replayCoreObviousProofCandidate,
  replayCoreLfProofRepairCandidate,
  serializeCoreLfDevelopmentSemanticDiff,
  serializeCoreLfProofMaintenanceInspection,
  serializeCoreLfProofRepairCandidateReplay,
  serializeCoreLfProofRepairProposal,
  serializeCoreProofGoalCouplingGraph,
  serializeCoreResearchGoalView,
  searchCoreLfAccessiblePremises,
  simplifyCoreProofPlan,
  validateCoreResearchGoalView,
} from '@hotdocx/emdash/workspace';

globalThis.emdashPackedSmoke = {
  CoreChecker,
  CoreLfScopedBuilder,
  exactSynthesisRevision: CORE_LF_INSTANCE_SYNTHESIS_PROFILE.revision,
  synthesizeCoreLfInstance,
  roleSynthesisRevision: CORE_LF_INSTANCE_ROLE_SYNTHESIS_PROFILE.revision,
  synthesizeCoreLfInstanceByRoles,
  workspaceRevision: CORE_LF_DECLARATION_WORKSPACE_PROFILE.revision,
  developmentDiffRevision: CORE_LF_DEVELOPMENT_DIFF_PROFILE.revision,
  proofMaintenanceRevision: CORE_LF_PROOF_MAINTENANCE_PROFILE.revision,
  premiseIndexRevision: CORE_LF_PREMISE_INDEX_PROFILE.revision,
  obviousProofRevision: CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.revision,
  proofDevelopmentRevision: CORE_LF_PROOF_DEVELOPMENT_PROFILE.revision,
  proofSourceRevision: CORE_LF_PROOF_DEVELOPMENT_SOURCE_PROFILE.revision,
  proofCheckerRevision: CORE_PROOF_CHECKER_PROFILE.revision,
  proofPlanRevision: CORE_PROOF_PLAN_PROFILE.revision,
  proofPlanMacroRevision: CORE_PROOF_PLAN_MACRO_PROFILE.revision,
  proofPlanPatchRevision: CORE_PROOF_PLAN_PATCH_PROFILE.revision,
  proofGoalCouplingRevision: CORE_PROOF_GOAL_COUPLING_PROFILE.revision,
  proofRefineTemplateRevision: CORE_PROOF_REFINE_TEMPLATE_PROFILE.revision,
  proofSimplifierRevision: CORE_PROOF_SIMPLIFIER_PROFILE.revision,
  researchGoalGraphRevision: CORE_RESEARCH_GOAL_GRAPH_PROFILE.revision,
  researchGoalViewRevision: CORE_RESEARCH_GOAL_VIEW_PROFILE.revision,
  compileCoreLfDeclarationWorkspace,
  compileCoreLfWorkspaceProofDocument,
  coreProofPlanConstructor,
  coreProofPlanHave,
  coreProofPlanRefine,
  coreProofTemplatePlaceholder,
  applyCoreProofPlanPatch,
  compareCoreLfProofDevelopmentSources,
  inspectCoreLfProofMaintenance,
  CoreProofChecker,
  createCoreProofPlanHoleReplacement,
  createCoreLfAccessiblePremiseIndex,
  createCoreLfProofDevelopment,
  createCoreResearchGoalGraphDefinition,
  createCoreResearchGoalView,
  evaluateCoreResearchGoalGraph,
  parseCoreLfProofDevelopmentSourceText,
  parseCoreResearchGoalViewText,
  proposeCoreObviousProofPlanPatches,
  proposeCoreLfProofRepairs,
  replayCoreObviousProofCandidate,
  replayCoreLfProofRepairCandidate,
  serializeCoreLfDevelopmentSemanticDiff,
  serializeCoreLfProofMaintenanceInspection,
  serializeCoreLfProofRepairCandidateReplay,
  serializeCoreLfProofRepairProposal,
  serializeCoreProofGoalCouplingGraph,
  serializeCoreResearchGoalView,
  searchCoreLfAccessiblePremises,
  simplifyCoreProofPlan,
  validateCoreResearchGoalView,
};
`,
  );

  run(process.execPath, ['consumer.mjs'], consumerDirectory);
  run(process.execPath, ['consumer.cjs'], consumerDirectory);
  run(
    path.join(repositoryRoot, 'node_modules', '.bin', 'tsc'),
    [
      '--noEmit',
      '--strict',
      '--target',
      'ES2020',
      '--module',
      'NodeNext',
      '--moduleResolution',
      'NodeNext',
      'consumer.ts',
    ],
    consumerDirectory,
  );
  run(
    path.join(packageRoot, 'node_modules', '.bin', 'esbuild'),
    [
      'browser-entry.js',
      '--bundle',
      '--format=esm',
      '--platform=browser',
      '--target=es2020',
      '--outfile=browser-bundle.js',
    ],
    consumerDirectory,
  );

  console.log('Packed @hotdocx/emdash install verified.');
} finally {
  await rm(temporaryRoot, { recursive: true, force: true });
}
