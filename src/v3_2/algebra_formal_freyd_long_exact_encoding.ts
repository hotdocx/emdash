/** Lossless transport for the deeply nested selected homological serializers. */

import { serializeCoreLfWorkspaceCanonicalJson } from './lf_workspace';

const revision = 'emdash-formal-freyd-long-exact-data-table-v1';
type Atom = null | boolean | number | string;
type Value = Atom | Value[] | { [key: string]: Value };
type Node = readonly ['atom', Atom] | readonly ['array', readonly number[]] |
    readonly ['object', readonly (readonly [string, number])[]] |
    readonly ['json-text', number, '' | '\n'];

/**
 * No hash, truncation, or semantic normalization: equal nodes share indices.
 * Existing serializers embed JSON text in JSON. A tagged text node avoids
 * repeatedly escaping it, while preserving text versus object and its newline.
 */
export function encodeAlgebraFormalFreydLongExactData(text: string): string {
    const nodes: Node[] = [];
    const byNode = new Map<string, number>();
    const byText = new Map<string, number>();
    const intern = (node: Node) => {
        const key = JSON.stringify(node);
        const previous = byNode.get(key);
        if (previous !== undefined) return previous;
        const index = nodes.length;
        nodes.push(node);
        byNode.set(key, index);
        return index;
    };
    const visit = (value: Value): number => {
        if (typeof value === 'string') {
            const previous = byText.get(value);
            if (previous !== undefined) return previous;
            let node: Node = ['atom', value];
            // Only exact JSON object/array text is unfolded. Other text remains
            // literal, including noncanonical whitespace and JSON-looking IDs.
            if (value.startsWith('{') || value.startsWith('[')) {
                try {
                    const parsed: Value = JSON.parse(value);
                    const serialized = JSON.stringify(parsed);
                    if (value === serialized || value === serialized + '\n') {
                        node = ['json-text', visit(parsed), value === serialized ? '' : '\n'];
                    }
                } catch { /* Ordinary text, not a serialized child. */ }
            }
            const index = intern(node);
            byText.set(value, index);
            return index;
        }
        if (Array.isArray(value)) return intern(['array', value.map(visit)]);
        if (value !== null && typeof value === 'object') {
            return intern(['object', Object.entries(value).map(([key, item]) => [key, visit(item)] as const)]);
        }
        return intern(['atom', value as Atom]);
    };
    const root = visit(text);
    return serializeCoreLfWorkspaceCanonicalJson({ revision, nodes, root }, 'longExactDataTable');
}

/** Recover the exact original serialization; references must be acyclic/backward. */
export function decodeAlgebraFormalFreydLongExactData(text: string): string {
    const fail = (): never => { throw new Error('Invalid long-exact data table'); };
    const input = JSON.parse(text) as { revision?: unknown; nodes?: unknown; root?: unknown } | null;
    if (!input || input.revision !== revision || !Array.isArray(input.nodes)) return fail();
    const values: Value[] = [];
    const reference = (index: unknown): Value => {
        if (typeof index !== 'number' || !Number.isSafeInteger(index) || index < 0 || index >= values.length) return fail();
        return values[index];
    };
    for (const node of input.nodes) {
        if (!Array.isArray(node)) return fail();
        let value: Value;
        switch (node[0]) {
            case 'atom':
                if (node.length !== 2 || !(node[1] === null || typeof node[1] === 'string' ||
                    typeof node[1] === 'boolean' || (typeof node[1] === 'number' && Number.isFinite(node[1])))) return fail();
                value = node[1];
                break;
            case 'array':
                if (node.length !== 2 || !Array.isArray(node[1])) return fail();
                value = node[1].map(reference);
                break;
            case 'object': {
                if (node.length !== 2 || !Array.isArray(node[1])) return fail();
                const object: { [key: string]: Value } = Object.create(null);
                for (const entry of node[1]) {
                    if (!Array.isArray(entry) || entry.length !== 2 || typeof entry[0] !== 'string' ||
                        Object.prototype.hasOwnProperty.call(object, entry[0])) return fail();
                    object[entry[0]] = reference(entry[1]);
                }
                value = object;
                break;
            }
            case 'json-text':
                if (node.length !== 3 || (node[2] !== '' && node[2] !== '\n')) return fail();
                value = JSON.stringify(reference(node[1])) + node[2];
                break;
            default: return fail();
        }
        values.push(value);
    }
    const result = reference(input.root);
    if (typeof result !== 'string') return fail();
    return result;
}
