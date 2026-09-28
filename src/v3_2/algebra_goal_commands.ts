/** One command catalog and dispatcher for the local CLI and MCP transport. */
import {
    ALGEBRA_GOAL_SOURCE_PROFILE, AlgebraGoalError, algebraGoalRecord,
    createAlgebraGoalExampleSource
} from './algebra_goal_source';
import {
    ALGEBRA_GOAL_WORKSPACE_PROFILE, computeAlgebraGoalWorkspace,
    initializeAlgebraGoalWorkspace, inspectAlgebraGoalWorkspace,
    renderAlgebraGoalWorkspace, updateAlgebraGoalWorkspace
} from './algebra_goal_workspace';
import { constructAlgebraGoalWorkspace } from './algebra_goal_construction';

const string = { type: 'string' } as const;
const termSchema = {
    type: 'object', additionalProperties: false, required: ['coefficient', 'exponents'],
    properties: {
        coefficient: { type: 'string', minLength: 1, maxLength: ALGEBRA_GOAL_SOURCE_PROFILE.maximumCoefficientCharacters },
        exponents: { type: 'array', minItems: 1, maxItems: 4, items: { type: 'string', pattern: '^(0|[1-9][0-9]{0,3})$' } }
    }
};
const polynomialSchema = {
    type: 'object', additionalProperties: false, required: ['name', 'terms'],
    properties: {
        name: { type: 'string', pattern: '^[A-Za-z][A-Za-z0-9_]*$', maxLength: 64 },
        terms: { type: 'array', maxItems: ALGEBRA_GOAL_SOURCE_PROFILE.maximumInputTerms, items: termSchema }
    }
};
export const ALGEBRA_GOAL_SOURCE_SCHEMA = {
    type: 'object', additionalProperties: false, required: ['revision', 'title', 'ring', 'generators', 'query'],
    properties: {
        revision: { type: 'string', const: ALGEBRA_GOAL_SOURCE_PROFILE.revision },
        title: { type: 'string', minLength: 1, maxLength: 1024 },
        ring: { type: 'object', additionalProperties: false, required: ['field', 'variables', 'order'], properties: {
            field: { type: 'string', const: 'Q' },
            variables: { type: 'array', minItems: 1, maxItems: 4, items: { type: 'string', maxLength: 64 } },
            order: { type: 'string', enum: ['lex', 'grlex', 'grevlex'] }
        } },
        generators: { type: 'array', minItems: 1, maxItems: 8, items: polynomialSchema },
        query: polynomialSchema
    }
} as const;

export interface AlgebraGoalCommandDescription {
    readonly command: string;
    readonly tool: string;
    readonly description: string;
    readonly writes: boolean;
    readonly properties: Readonly<Record<string, unknown>>;
    readonly required: readonly string[];
}

export const ALGEBRA_GOAL_COMMANDS: readonly AlgebraGoalCommandDescription[] = Object.freeze([
    { command: 'init', tool: 'emdash_initialize', writes: true,
        description: 'Initialize ordinary mathematical workspace files. Defaults to a polynomial relation example; never overwrites an existing source.',
        properties: { source: ALGEBRA_GOAL_SOURCE_SCHEMA }, required: [] },
    { command: 'inspect', tool: 'emdash_inspect', writes: false,
        description: 'Read the current mathematical source, exact revision and artifact freshness. Does not execute user modules or assume a proof goal.',
        properties: {}, required: [] },
    { command: 'update', tool: 'emdash_update', writes: true,
        description: 'Replace the mathematical source after comparing its inspected revision; retain the previous source and invalidate older results.',
        properties: { expectedRevision: string, source: ALGEBRA_GOAL_SOURCE_SCHEMA }, required: ['expectedRevision', 'source'] },
    { command: 'compute', tool: 'emdash_compute', writes: true,
        description: 'Compute exact rational-polynomial ideal membership and retain coefficients/remainder for further constructions. Requires no proof goal or assumption.',
        properties: {}, required: [] },
    { command: 'render', tool: 'emdash_render', writes: true,
        description: 'Derive a bounded approximate plane-curve SVG/HTML view from the current two-variable polynomial source. Exact data remains separate.',
        properties: {}, required: [] },
    { command: 'construct', tool: 'emdash_construct', writes: true,
        description: 'Reuse retained membership coefficients in a whole free complex and apply its upper map to one. Native mode needs no assumption. Internal mode additionally constructs and uses a typed Core complex, requiring an explicit computed-equation adoption reason and the supported integer-polynomial interpretation.',
        properties: {
            mode: { type: 'string', enum: ['native', 'internal'], default: 'native' },
            adoptionReason: { type: 'string', minLength: 1, maxLength: 2048,
                description: 'Explicit caller decision to use the checked computed equation as an assumption for internal construction; not a proof or human-approval claim.' }
        }, required: [] }
]);

export function algebraGoalCapabilities() {
    return {
        revision: 'emdash-algebra-goal-commands-v1', runtime: 'node',
        sourceProfile: ALGEBRA_GOAL_SOURCE_PROFILE, workspaceProfile: ALGEBRA_GOAL_WORKSPACE_PROFILE,
        commands: ALGEBRA_GOAL_COMMANDS, example: createAlgebraGoalExampleSource(),
        cloudTransport: 'not-implemented', executesUserModules: false,
        mathematicalScope: 'bounded rational-polynomial computation and free complexes; plane-curve samples are approximate; internal construction uses an explicit computed equation and a bounded integer-polynomial interpretation'
    };
}

export type AlgebraGoalCommandResponse =
    | { readonly ok: true; readonly command: string; readonly result: object }
    | { readonly ok: false; readonly error: { readonly code: string; readonly message: string } };

export function algebraGoalFailure(error: unknown): AlgebraGoalCommandResponse {
    const caught = error as { code?: string; message?: string; path?: string };
    const code = typeof caught?.code === 'string' ? caught.code : 'COMMAND_FAILED';
    const message = error instanceof SyntaxError ? 'Input is not valid JSON' :
        code === 'ENOENT' ? 'A required workspace file is missing; initialize or compute the workspace first' :
            code === 'EEXIST' ? 'The workspace source or operation lock already exists; inspect it before continuing' :
                error instanceof Error ? error.message : String(error);
    return { ok: false, error: { code, message } };
}

export async function executeAlgebraGoalCommand(input: unknown): Promise<AlgebraGoalCommandResponse> {
    try {
        const request = algebraGoalRecord(input,
            ['command', 'root', 'source', 'expectedRevision', 'mode', 'adoptionReason'], 'request');
        if (request.command === 'capabilities') {
            if (Object.keys(request).length !== 1) throw new AlgebraGoalError('INVALID_REQUEST', 'capabilities accepts no workspace input');
            return { ok: true, command: 'capabilities', result: algebraGoalCapabilities() };
        }
        const description = ALGEBRA_GOAL_COMMANDS.find(c => c.command === request.command);
        if (!description) throw new AlgebraGoalError('UNKNOWN_COMMAND', 'Unknown algebra goal command');
        if (Object.keys(request).some(key => !['command', 'root', ...Object.keys(description.properties)].includes(key))) {
            throw new AlgebraGoalError('INVALID_REQUEST', 'This command does not accept the supplied option');
        }
        if (typeof request.root !== 'string' || !request.root.trim()) throw new AlgebraGoalError('INVALID_ROOT', 'Supply a workspace root');
        let result: object;
        switch (description.command) {
            case 'init': result = await initializeAlgebraGoalWorkspace(request.root, request.source); break;
            case 'inspect': result = inspectAlgebraGoalWorkspace(request.root); break;
            case 'update': result = await updateAlgebraGoalWorkspace(request.root, request.expectedRevision as string, request.source); break;
            case 'compute': result = await computeAlgebraGoalWorkspace(request.root); break;
            case 'render': result = await renderAlgebraGoalWorkspace(request.root); break;
            case 'construct': result = await constructAlgebraGoalWorkspace(request.root,
                { mode: request.mode, adoptionReason: request.adoptionReason }); break;
            default: throw new AlgebraGoalError('UNKNOWN_COMMAND', 'Unknown command');
        }
        return { ok: true, command: description.command, result };
    } catch (error) { return algebraGoalFailure(error); }
}
