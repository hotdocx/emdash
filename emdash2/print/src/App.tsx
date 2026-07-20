import { useEffect, useRef, useState } from 'react';
import { Previewer } from 'pagedjs';
import {
    registeredDocumentHint,
    resolvePrintDocument,
} from './documentRegistry';
import { renderMarkdownToHtml } from './pipeline/commonMarkdownPipeline';
import { cleanupEmptyPagedPages } from './preview/pagedCleanup';
import './print-styles.css';

interface PreviewControllerProps {
    markdown: string;
    isTwoColumn: boolean;
    documentKind: 'article' | 'book';
}

function paperBodyHtml(html: string, documentKind: 'article' | 'book') {
    if (documentKind === 'article') {
        return `<div class="paper-body">${html}</div>`;
    }

    const endMarker = /<div[^>]*\bclass="[^"]*\bbook-source-end\b[^"]*"[^>]*><\/div>/g;
    const sections = html
        .split(endMarker)
        .map((section) => section.trim())
        .filter(Boolean);
    if (sections.length < 2) {
        throw new Error('Generated book source boundaries are missing from rendered HTML');
    }
    return sections
        .map((section, index) =>
            `<section class="paper-body book-source-section" data-book-section="${index + 1}" data-break-before="page">${section}</section>`
        )
        .join('');
}

const PreviewController = ({ markdown, isTwoColumn, documentKind }: PreviewControllerProps) => {
    const containerRef = useRef<HTMLDivElement>(null);

    useEffect(() => {
        let isMounted = true;
        const processAndRender = async () => {
            const model = await renderMarkdownToHtml(markdown, {
                idPrefix: 'print-document',
                arrowgrams: { mode: 'static-only' },
            });

            const escapeHtml = (input: unknown) =>
                String(input ?? '')
                    .replace(/&/g, '&amp;')
                    .replace(/</g, '&lt;')
                    .replace(/>/g, '&gt;')
                    .replace(/"/g, '&quot;')
                    .replace(/'/g, '&#39;');

            const editionParts = [
                model.metadata.edition,
                model.metadata.editionVersion ? `version ${model.metadata.editionVersion}` : '',
                model.metadata.publicationDate,
            ].filter(Boolean);
            const titleBlockHtml = `<div class="title-block">${model.metadata.title ? `<div class="title">${escapeHtml(model.metadata.title)}</div>` : ''}${model.metadata.authors ? `<div class="authors">${escapeHtml(model.metadata.authors)}</div>` : ''}${editionParts.length > 0 ? `<div class="edition">${escapeHtml(editionParts.join(' / '))}</div>` : ''}</div>`;
            const layoutClass = isTwoColumn ? 'layout-two-column' : 'layout-single-column';
            const finalHtml = `<div class="${layoutClass} document-${documentKind}">${titleBlockHtml}${paperBodyHtml(model.html, documentKind)}</div>`;

            if (isMounted && containerRef.current) {
                const container = containerRef.current;
                container.removeAttribute('data-pagination-complete');
                container.removeAttribute('data-page-count');
                container.innerHTML = '';
                const paged = new Previewer();
                // KaTeX and print styles are bundled locally by the application.
                // @ts-ignore pagedjs has incomplete declaration coverage.
                await paged.preview(finalHtml, [], container);
                cleanupEmptyPagedPages(container);
                if (isMounted && containerRef.current === container) {
                    container.dataset.pageCount = String(
                        container.querySelectorAll('.pagedjs_page').length
                    );
                    container.dataset.paginationComplete = 'true';
                }
            }
        };

        void processAndRender();
        return () => {
            isMounted = false;
        };
    }, [markdown, isTwoColumn, documentKind]);

    return (
        <div ref={containerRef} className="preview-content-area">
            <p className="loading-indicator">Processing Document...</p>
        </div>
    );
};

export default function App() {
    const [markdown, setMarkdown] = useState<string | null>(null);
    const [isTwoColumn, setIsTwoColumn] = useState(false);
    const [documentKind, setDocumentKind] = useState<'article' | 'book'>('article');

    useEffect(() => {
        const params = new URLSearchParams(window.location.search);
        const requested = (params.get('paper') || '').trim();
        const isLocalStorageRef = /^ls:/i.test(requested);
        const isAbsoluteUrl = /^https?:\/\//i.test(requested);

        if (isLocalStorageRef) {
            const key = requested.replace(/^ls:/i, '').trim();
            if (!key) {
                setMarkdown(`# Error: Could not load localStorage paper\n\nPass a key as \`?paper=ls:some_key\`.`);
                return;
            }

            const stored = localStorage.getItem(key);
            if (stored == null) {
                setMarkdown(`# Error: Could not load localStorage key \`${key}\`\n\nNo value found. Create it in localStorage first, or use a registered document selector.`);
                return;
            }

            setIsTwoColumn(false);
            setDocumentKind('article');
            setMarkdown(stored);
            return;
        }

        const baseUrl = new URL(import.meta.env.BASE_URL, window.location.origin);
        let paperUrl: string;
        let selectedFile: string;

        if (isAbsoluteUrl) {
            paperUrl = requested;
            selectedFile = requested;
            setIsTwoColumn(false);
            setDocumentKind('article');
        } else {
            const document = resolvePrintDocument(requested);
            if (!document) {
                setMarkdown(
                    `# Error: Unknown registered document\n\n\`${requested}\` is not in \`print/documents.json\`.\n\nRegistered document selectors: ${registeredDocumentHint()}.`
                );
                return;
            }
            paperUrl = new URL(document.file, baseUrl).toString();
            selectedFile = document.file;
            setIsTwoColumn(document.layout === 'two-column');
            setDocumentKind(document.kind);
        }

        fetch(paperUrl)
            .then((response) => {
                if (!response.ok) {
                    throw new Error('Failed to load content: HTTP ' + response.status);
                }
                return response.text();
            })
            .then((text) => setMarkdown(text))
            .catch((error) => {
                console.error(error);
                const displayPath = isAbsoluteUrl
                    ? selectedFile
                    : 'print/public/' + selectedFile;
                setMarkdown(
                    `# Error: Could not load ${paperUrl}\n\nPlease ensure \`${displayPath}\` exists. Local documents must be registered in \`print/documents.json\`.\n\nYou can also load from localStorage with \`?paper=ls:some_key\`, or pass an absolute URL.`
                );
            });
    }, []);

    if (!markdown) return <div className="loading-indicator">Loading Content...</div>;

    return (
        <div className="preview-container">
            <div className="preview-controls">
                <button
                    className={`control-button ${isTwoColumn ? 'active' : ''}`}
                    onClick={() => setIsTwoColumn(!isTwoColumn)}
                >
                    {isTwoColumn ? 'Single Column' : 'Two Column'}
                </button>
                <button className="control-button" onClick={() => window.print()}>
                    Print / Save PDF
                </button>
            </div>
            <PreviewController
                markdown={markdown}
                isTwoColumn={isTwoColumn}
                documentKind={documentKind}
            />
        </div>
    );
}
