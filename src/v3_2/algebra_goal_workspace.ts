/** Node-owned workspace files. Mathematical state is inert data, not executable modules. */
import {
    closeSync, constants, existsSync, fstatSync, fsyncSync, lstatSync, mkdirSync,
    openSync, readFileSync, realpathSync, renameSync, unlinkSync, writeFileSync
} from 'node:fs';
import { createHash, randomUUID } from 'node:crypto';
import path from 'node:path';
import {
    AlgebraGoalError, type AlgebraGoalSource, algebraGoalInput, computeAlgebraGoal,
    createAlgebraGoalExampleSource, describeAlgebraGoal, normalizeAlgebraGoalSource,
    serializeAlgebraGoalSource, algebraGoalPolynomialFromTerms
} from './algebra_goal_source';
import {
    ALGEBRA_CURVE_VIEWPORT, algebraWorkbenchEscapeHtml, renderAlgebraPolynomialCurveSvg,
    sampleAlgebraPolynomialCurves
} from './algebra_polynomial_plot';
import { algebraPolynomialText } from './algebra_polynomial';

export const ALGEBRA_GOAL_WORKSPACE_PROFILE = Object.freeze({
    revision: 'emdash-algebra-goal-workspace-v1',
    sourceFile: 'emdash.goal.json', generatedDirectory: '.emdash',
    maximumSourceBytes: 1024 * 1024, maximumArtifactBytes: 4 * 1024 * 1024,
    computationFile: '.emdash/computation.json', viewFile: '.emdash/view.json',
    constructionFile: '.emdash/construction.json',
    executesUserSource: false, writesGit: false, invokesNetwork: false
} as const);

export const algebraGoalSha256 = (value: string | Uint8Array): string =>
    'sha256:' + createHash('sha256').update(value).digest('hex');

const isMissing = (error: unknown) => (error as NodeJS.ErrnoException)?.code === 'ENOENT';
function rootDirectory(root: string, create = false): string {
    if (!path.isAbsolute(root)) throw new AlgebraGoalError('INVALID_ROOT', 'Supply an absolute workspace directory');
    if (create && !existsSync(root)) mkdirSync(root, { recursive: true });
    const stat = lstatSync(root);
    if (!stat.isDirectory() || stat.isSymbolicLink()) {
        throw new AlgebraGoalError('INVALID_ROOT', 'The workspace root must be a directory, not a symlink');
    }
    return realpathSync(root);
}

/** The service itself uses fixed owned names; callers cannot provide arbitrary file paths. */
function ownedPath(root: string, relative: string, createParents = false): string {
    const parts = relative.split('/');
    if (parts.some(part => !part || part === '.' || part === '..' || part.includes('\\'))) {
        throw new AlgebraGoalError('INVALID_PATH', 'Invalid workspace-owned path');
    }
    let current = root;
    for (let i = 0; i < parts.length; i++) {
        current = path.join(current, parts[i]);
        let stat;
        try { stat = lstatSync(current); } catch (error) {
            if (!isMissing(error)) throw error;
            if (i < parts.length - 1 && createParents) {
                mkdirSync(current);
                stat = lstatSync(current);
            } else if (i < parts.length - 1) {
                throw error;
            } else return current;
        }
        if (stat.isSymbolicLink() || (i < parts.length - 1 ? !stat.isDirectory() : !stat.isFile())) {
            throw new AlgebraGoalError('UNSAFE_PATH', `Workspace-owned path is not an ordinary ${i < parts.length - 1 ? 'directory' : 'file'}: ${relative}`);
        }
    }
    return current;
}

function readOwned(root: string, relative: string, maximum: number): string {
    const filename = ownedPath(root, relative);
    const fd = openSync(filename, constants.O_RDONLY | constants.O_NOFOLLOW);
    try {
        if (fstatSync(fd).size > maximum) throw new AlgebraGoalError('FILE_LIMIT', `${relative} exceeds its byte limit`);
        const bytes = readFileSync(fd);
        if (bytes.byteLength > maximum) throw new AlgebraGoalError('FILE_LIMIT', `${relative} exceeds its byte limit`);
        return new TextDecoder('utf-8', { fatal: true }).decode(bytes);
    } finally { closeSync(fd); }
}

function writeOwned(root: string, relative: string, contents: string, exclusive = false): string {
    const maximum = relative === ALGEBRA_GOAL_WORKSPACE_PROFILE.sourceFile
        ? ALGEBRA_GOAL_WORKSPACE_PROFILE.maximumSourceBytes : ALGEBRA_GOAL_WORKSPACE_PROFILE.maximumArtifactBytes;
    if (Buffer.byteLength(contents) > maximum) {
        throw new AlgebraGoalError('FILE_LIMIT', `${relative} exceeds its byte limit`);
    }
    const filename = ownedPath(root, relative, true);
    if (exclusive) {
        const fd = openSync(filename, constants.O_WRONLY | constants.O_CREAT | constants.O_EXCL | constants.O_NOFOLLOW, 0o600);
        try { writeFileSync(fd, contents); fsyncSync(fd); } finally { closeSync(fd); }
    } else {
        const temporary = `${filename}.${randomUUID()}.tmp`;
        try {
            const fd = openSync(temporary, constants.O_WRONLY | constants.O_CREAT | constants.O_EXCL | constants.O_NOFOLLOW, 0o600);
            try { writeFileSync(fd, contents); fsyncSync(fd); } finally { closeSync(fd); }
            ownedPath(root, relative); // Recheck the target before replacing derived/explicitly updated data.
            renameSync(temporary, filename);
        } finally { try { unlinkSync(temporary); } catch (error) { if (!isMissing(error)) throw error; } }
    }
    return filename;
}

const json = (value: unknown) => JSON.stringify(value, null, 2) + '\n';

async function withMutation<T>(root: string, action: () => Promise<T> | T): Promise<T> {
    const lock = '.emdash/operation.lock';
    const token = json({ revision: ALGEBRA_GOAL_WORKSPACE_PROFILE.revision, pid: process.pid, nonce: randomUUID() });
    for (let attempt = 0; ; attempt++) {
        try { writeOwned(root, lock, token, true); break; } catch (error) {
            if ((error as NodeJS.ErrnoException).code !== 'EEXIST' || attempt > 0) throw error;
            const previous = readOwned(root, lock, 4096);
            let owner: { revision?: string; pid?: number; nonce?: string };
            try { owner = JSON.parse(previous); } catch { throw new AlgebraGoalError('WORKSPACE_BUSY', 'An existing workspace lock could not be identified'); }
            if (owner.revision !== ALGEBRA_GOAL_WORKSPACE_PROFILE.revision ||
                !Number.isSafeInteger(owner.pid) || owner.pid! <= 0 || typeof owner.nonce !== 'string') {
                throw new AlgebraGoalError('WORKSPACE_BUSY', 'An existing workspace lock belongs to another owner');
            }
            try { process.kill(owner.pid!, 0); } catch (check) {
                if ((check as NodeJS.ErrnoException).code === 'ESRCH' && readOwned(root, lock, 4096) === previous) {
                    unlinkSync(ownedPath(root, lock)); // Only this service's exact dead-process lock.
                    continue;
                }
            }
            throw new AlgebraGoalError('WORKSPACE_BUSY', 'Another operation is using this workspace');
        }
    }
    try { return await action(); } finally {
        try { if (readOwned(root, lock, 4096) === token) unlinkSync(ownedPath(root, lock)); }
        catch (error) { if (!isMissing(error)) throw error; }
    }
}

export function readAlgebraGoalWorkspace(rootInput: string) {
    const root = rootDirectory(rootInput);
    const sourceText = readOwned(root, ALGEBRA_GOAL_WORKSPACE_PROFILE.sourceFile,
        ALGEBRA_GOAL_WORKSPACE_PROFILE.maximumSourceBytes);
    return Object.freeze({ root, sourceText, sourceRevision: algebraGoalSha256(sourceText),
        source: normalizeAlgebraGoalSource(JSON.parse(sourceText)) });
}

function assertCurrent(root: string, expected: string): void {
    if (readAlgebraGoalWorkspace(root).sourceRevision !== expected) {
        throw new AlgebraGoalError('STALE_SOURCE', 'The mathematical source changed; inspect it before continuing');
    }
}

function artifactState(root: string, relative: string, sourceRevision: string) {
    try {
        const value = JSON.parse(readOwned(root, relative, ALGEBRA_GOAL_WORKSPACE_PROFILE.maximumArtifactBytes));
        const profiles: Record<string, string> = {
            [ALGEBRA_GOAL_WORKSPACE_PROFILE.computationFile]: 'emdash-algebra-goal-computation-artifact-v1',
            [ALGEBRA_GOAL_WORKSPACE_PROFILE.viewFile]: 'emdash-algebra-goal-view-v1',
            [ALGEBRA_GOAL_WORKSPACE_PROFILE.constructionFile]: 'emdash-algebra-goal-construction-v1'
        };
        if (value.revision !== profiles[relative]) return { status: 'unreadable', reason: 'Unsupported artifact revision' };
        if (relative === ALGEBRA_GOAL_WORKSPACE_PROFILE.constructionFile) {
            let computationRevision;
            try {
                computationRevision = algebraGoalSha256(readOwned(root, ALGEBRA_GOAL_WORKSPACE_PROFILE.computationFile,
                    ALGEBRA_GOAL_WORKSPACE_PROFILE.maximumArtifactBytes));
            } catch {
                return { status: 'stale', path: path.join(root, relative), reason: 'The retained computation is unavailable' };
            }
            if (value.computationRevision !== computationRevision) {
                return { status: 'stale', path: path.join(root, relative), reason: 'The retained computation changed' };
            }
        }
        return { status: value.sourceRevision === sourceRevision ? 'current' : 'stale', path: path.join(root, relative) };
    } catch (error) {
        if (isMissing(error)) return { status: 'absent' };
        return { status: 'unreadable', reason: error instanceof Error ? error.message : String(error) };
    }
}

export function inspectAlgebraGoalWorkspace(rootInput: string) {
    const current = readAlgebraGoalWorkspace(rootInput);
    return {
        revision: ALGEBRA_GOAL_WORKSPACE_PROFILE.revision,
        workspace: current.root, sourceRevision: current.sourceRevision,
        source: current.source, mathematics: describeAlgebraGoal(current.source),
        artifacts: {
            computation: artifactState(current.root, ALGEBRA_GOAL_WORKSPACE_PROFILE.computationFile, current.sourceRevision),
            view: artifactState(current.root, ALGEBRA_GOAL_WORKSPACE_PROFILE.viewFile, current.sourceRevision),
            construction: artifactState(current.root, ALGEBRA_GOAL_WORKSPACE_PROFILE.constructionFile, current.sourceRevision)
        },
        artifactStatusMeaning: 'source freshness only; construction freshly checks retained relation data'
    };
}

export async function initializeAlgebraGoalWorkspace(rootInput: string, sourceInput?: unknown) {
    const source = sourceInput === undefined ? createAlgebraGoalExampleSource() : normalizeAlgebraGoalSource(sourceInput);
    const root = rootDirectory(rootInput, true);
    return withMutation(root, () => {
        writeOwned(root, ALGEBRA_GOAL_WORKSPACE_PROFILE.sourceFile, serializeAlgebraGoalSource(source), true);
        return inspectAlgebraGoalWorkspace(root);
    });
}

export async function updateAlgebraGoalWorkspace(rootInput: string, expectedRevision: string, sourceInput: unknown) {
    const source = normalizeAlgebraGoalSource(sourceInput), root = rootDirectory(rootInput);
    return withMutation(root, () => {
        if (typeof expectedRevision !== 'string' || !expectedRevision.startsWith('sha256:')) {
            throw new AlgebraGoalError('EXPECTED_REVISION_REQUIRED', 'Use the source revision returned by inspection');
        }
        const previous = readAlgebraGoalWorkspace(root);
        assertCurrent(root, expectedRevision);
        // Retain the exact preceding source without inventing Git snapshots or editing user notes.
        const history = `.emdash/history/${previous.sourceRevision.slice(7)}.json`;
        writeOwned(root, history, previous.sourceText);
        assertCurrent(root, expectedRevision);
        writeOwned(root, ALGEBRA_GOAL_WORKSPACE_PROFILE.sourceFile, serializeAlgebraGoalSource(source));
        return inspectAlgebraGoalWorkspace(root);
    });
}

export async function computeAlgebraGoalWorkspace(rootInput: string) {
    const root = rootDirectory(rootInput);
    return withMutation(root, () => {
        const current = readAlgebraGoalWorkspace(root);
        const computation = computeAlgebraGoal(current.source);
        const artifact = { revision: 'emdash-algebra-goal-computation-artifact-v1', sourceRevision: current.sourceRevision, computation };
        assertCurrent(root, current.sourceRevision);
        const artifactPath = writeOwned(root, ALGEBRA_GOAL_WORKSPACE_PROFILE.computationFile, json(artifact));
        const ring = algebraGoalInput(current.source).ideal.ring;
        const display = (terms: unknown) => {
            const value = algebraPolynomialText(algebraGoalPolynomialFromTerms(ring, terms));
            return value.length <= 2048 ? value : value.slice(0, 2048) + '… (full value in artifact)';
        };
        return { sourceRevision: current.sourceRevision, mathematics: describeAlgebraGoal(current.source),
            member: computation.member, engine: computation.engine, artifactPath,
            resultStatus: 'exact-native-computation', proofStatus: 'no-proof-goal-or-assumption',
            coefficients: computation.coefficients.map((terms, i) => ({
                generator: current.source.generators[i].name, coefficient: display(terms)
            })), remainder: display(computation.remainder),
            coefficientCount: computation.coefficients.length, basisSize: computation.basis.length };
    });
}

export async function renderAlgebraGoalWorkspace(rootInput: string) {
    const root = rootDirectory(rootInput);
    return withMutation(root, () => {
        const current = readAlgebraGoalWorkspace(root), input = algebraGoalInput(current.source);
        const view = sampleAlgebraPolynomialCurves(input, { ...ALGEBRA_CURVE_VIEWPORT, cells: 96 });
        const svg = renderAlgebraPolynomialCurveSvg(view);
        const escape = algebraWorkbenchEscapeHtml;
        const html = `<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><meta name="emdash-source-revision" content="${current.sourceRevision}">
<title>${escape(current.source.title)}</title><style>body{font:16px/1.6 system-ui;margin:24px auto;padding:0 20px;max-width:900px;color:#263e36;overflow-wrap:anywhere}svg{width:100%;height:auto}pre{white-space:pre-wrap;overflow-wrap:anywhere}h1{line-height:1.2}</style>
<h1>${escape(current.source.title)}</h1><p>Exact polynomial inputs over Q[${escape(input.ideal.ring.variables.join(','))}].</p>
<pre>${input.ideal.generators.map((p, i) => `${escape(current.source.generators[i].name)} = ${escape(algebraPolynomialText(p))}`).join('\n')}</pre>
${svg}<p>${escape(view.limitation)}</p></html>`;
        assertCurrent(root, current.sourceRevision);
        const svgPath = writeOwned(root, '.emdash/view.svg', svg);
        const htmlPath = writeOwned(root, '.emdash/view.html', html);
        writeOwned(root, ALGEBRA_GOAL_WORKSPACE_PROFILE.viewFile, json({
            revision: 'emdash-algebra-goal-view-v1', sourceRevision: current.sourceRevision,
            mathematicalSource: view.source, interpretation: view.interpretation,
            htmlSha256: algebraGoalSha256(html), svgSha256: algebraGoalSha256(svg)
        }));
        return { sourceRevision: current.sourceRevision, htmlPath, svgPath,
            resultStatus: view.authority, limitation: view.limitation };
    });
}

/** Shared host boundary used by the forthcoming construction command. */
export async function withAlgebraGoalConstruction<T>(rootInput: string, construct: (input: {
    source: AlgebraGoalSource; sourceRevision: string; computation: unknown; computationRevision: string;
}) => Promise<{ artifact: unknown; summary: T }>) {
    const root = rootDirectory(rootInput);
    return withMutation(root, async () => {
        const current = readAlgebraGoalWorkspace(root);
        const retainedBytes = readOwned(root, ALGEBRA_GOAL_WORKSPACE_PROFILE.computationFile,
            ALGEBRA_GOAL_WORKSPACE_PROFILE.maximumArtifactBytes);
        const retained = JSON.parse(retainedBytes);
        if (retained.revision !== 'emdash-algebra-goal-computation-artifact-v1' || retained.sourceRevision !== current.sourceRevision) {
            throw new AlgebraGoalError('STALE_RESULT', 'Compute a current relation before constructing with it');
        }
        const computationRevision = algebraGoalSha256(retainedBytes);
        const result = await construct({ source: current.source, sourceRevision: current.sourceRevision,
            computation: retained.computation, computationRevision });
        assertCurrent(root, current.sourceRevision);
        if (algebraGoalSha256(readOwned(root, ALGEBRA_GOAL_WORKSPACE_PROFILE.computationFile,
            ALGEBRA_GOAL_WORKSPACE_PROFILE.maximumArtifactBytes)) !== computationRevision) {
            throw new AlgebraGoalError('STALE_RESULT', 'The retained coefficient data changed during construction');
        }
        const artifactPath = writeOwned(root, ALGEBRA_GOAL_WORKSPACE_PROFILE.constructionFile,
            json({ revision: 'emdash-algebra-goal-construction-v1', sourceRevision: current.sourceRevision,
                computationRevision, result: result.artifact }));
        return { ...result.summary, sourceRevision: current.sourceRevision, computationRevision, artifactPath };
    });
}
