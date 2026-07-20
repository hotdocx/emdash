import registryJson from '../documents.json';

export type DocumentLayout = 'single-column' | 'two-column';

export interface PrintDocument {
    id: string;
    slug: string;
    file: string;
    title: string;
    kind: 'article' | 'book';
    default: boolean;
    generated: boolean;
    aliases: string[];
    groups: string[];
    layout: DocumentLayout;
    checks: {
        validate: boolean;
        render: boolean;
    };
    timeoutMs: number;
}

interface DocumentRegistry {
    version: number;
    documents: PrintDocument[];
}

const registry = registryJson as DocumentRegistry;

export const printDocuments = registry.documents;

export function defaultPrintDocument(): PrintDocument {
    const selected = printDocuments.find((document) => document.default);
    if (!selected) throw new Error('print document registry has no default');
    return selected;
}

export function resolvePrintDocument(selector: string): PrintDocument | undefined {
    const normalized = selector.trim().replace(/^\/+/, '');
    if (normalized === '') return defaultPrintDocument();
    return printDocuments.find((document) =>
        [document.id, document.slug, document.file, ...document.aliases].includes(normalized)
    );
}

export function registeredDocumentHint(): string {
    return printDocuments.map((document) => document.slug).join(', ');
}
