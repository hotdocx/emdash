/** Portable command entry; ordinary authoring programs are separate host actions. */
import { readFileSync, statSync } from 'node:fs';
import path from 'node:path';
import { AlgebraGoalError } from './algebra_goal_source';
import { ALGEBRA_GOAL_COMMANDS, algebraGoalFailure, executeAlgebraGoalCommand } from './algebra_goal_commands';
import { ALGEBRA_GOAL_WORKSPACE_PROFILE } from './algebra_goal_workspace';

export const ALGEBRA_GOAL_CLI_USAGE =
    'emdash-agent <capabilities|init|inspect|update|compute|render> --root DIRECTORY ' +
    '[--source JSON_FILE --expected-revision SHA256]\n' +
    'emdash-agent request  # one inert JSON command on stdin';

export async function readAlgebraGoalStdin(stream: AsyncIterable<Uint8Array | string> = process.stdin): Promise<string> {
    const chunks: Uint8Array[] = [];
    let size = 0;
    for await (const chunk of stream) {
        const bytes = typeof chunk === 'string' ? Buffer.from(chunk) : chunk;
        size += bytes.byteLength;
        if (size > ALGEBRA_GOAL_WORKSPACE_PROFILE.maximumSourceBytes) {
            throw new AlgebraGoalError('INPUT_LIMIT', 'Command input exceeds one MiB');
        }
        chunks.push(bytes);
    }
    return new TextDecoder('utf-8', { fatal: true }).decode(Buffer.concat(chunks));
}

export async function runAlgebraGoalCli(argv: readonly string[]): Promise<number> {
    try {
        if (argv[0] === '--help' || argv[0] === 'help') { process.stdout.write(ALGEBRA_GOAL_CLI_USAGE + '\n'); return 0; }
        let request: unknown;
        if (argv[0] === 'request') {
            if (argv.length !== 1) throw new AlgebraGoalError('INVALID_ARGUMENT', 'request reads only stdin');
            request = JSON.parse(await readAlgebraGoalStdin());
        } else {
            const parsed: Record<string, unknown> = { command: argv[0] ?? 'capabilities' };
            const description = ALGEBRA_GOAL_COMMANDS.find(c => c.command === parsed.command);
            if (!description && parsed.command !== 'capabilities') throw new AlgebraGoalError('UNKNOWN_COMMAND', 'Unknown algebra goal command');
            if (parsed.command === 'capabilities' && argv.length > 1) throw new AlgebraGoalError('INVALID_ARGUMENT', 'capabilities accepts no options');
            for (let index = 1; index < argv.length; index += 2) {
                const option = argv[index], value = argv[index + 1];
                if (value === undefined) throw new AlgebraGoalError('INVALID_ARGUMENT', `Missing value for ${option}`);
                const key = option === '--root' ? 'root' : option === '--source' ? 'source' :
                    option === '--expected-revision' ? 'expectedRevision' : undefined;
                if (!key || key in parsed) throw new AlgebraGoalError('INVALID_ARGUMENT', `Unknown or repeated option: ${option}`);
                if (key !== 'root' && !(key in description!.properties)) {
                    throw new AlgebraGoalError('INVALID_ARGUMENT', `This command does not accept ${option}`);
                }
                if (key === 'root') parsed.root = path.resolve(value);
                else if (key === 'source') {
                    const filename = path.resolve(value);
                    if (statSync(filename).size > ALGEBRA_GOAL_WORKSPACE_PROFILE.maximumSourceBytes) {
                        throw new AlgebraGoalError('INPUT_LIMIT', 'Source exceeds one MiB');
                    }
                    parsed.source = JSON.parse(new TextDecoder('utf-8', { fatal: true }).decode(readFileSync(filename)));
                } else parsed[key] = value;
            }
            request = parsed;
        }
        const response = await executeAlgebraGoalCommand(request);
        process.stdout.write(JSON.stringify(response) + '\n');
        return response.ok ? 0 : 1;
    } catch (error) {
        process.stdout.write(JSON.stringify(algebraGoalFailure(error)) + '\n');
        return 1;
    }
}
