import { useState, useEffect, useRef } from 'react';
import { Previewer } from 'pagedjs';
import { renderMarkdownToHtml } from './pipeline/commonMarkdownPipeline';
import { cleanupEmptyPagedPages } from './preview/pagedCleanup';
import './print-styles.css';

interface PreviewControllerProps {
    markdown: string;
    isTwoColumn: boolean;
}

const PreviewController = ({ markdown, isTwoColumn }: PreviewControllerProps) => {
    const containerRef = useRef<HTMLDivElement>(null);

    useEffect(() => {
        let isMounted = true;
        const processAndRender = async () => {
            const model = await renderMarkdownToHtml(markdown, {
                idPrefix: `print-${Date.now()}`,
                arrowgrams: { mode: "static-only" },
            });

            const escapeHtml = (input: unknown) =>
                String(input ?? "")
                    .replace(/&/g, "&amp;")
                    .replace(/</g, "&lt;")
                    .replace(/>/g, "&gt;")
                    .replace(/"/g, "&quot;")
                    .replace(/'/g, "&#39;");

            const titleBlockHtml = `<div class="title-block">${model.metadata.title ? `<div class="title">${escapeHtml(model.metadata.title)}</div>` : ''}${model.metadata.authors ? `<div class="authors">${escapeHtml(model.metadata.authors)}</div>` : ''}</div>`;
            const layoutClass = isTwoColumn ? 'layout-two-column' : 'layout-single-column';
            const finalHtml = `<div class="${layoutClass}">${titleBlockHtml}<div class="paper-body">${model.html}</div></div>`;

            if (isMounted && containerRef.current) {
                containerRef.current.innerHTML = '';
                const paged = new Previewer();
                // Pass KaTeX CSS but rely on imported print-styles.css for the rest
                // @ts-ignore
                await paged.preview(finalHtml, ["https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/katex.min.css"], containerRef.current);
                cleanupEmptyPagedPages(containerRef.current);
            }
        };
        processAndRender();
        return () => { isMounted = false; };
    }, [markdown, isTwoColumn]);

    return (
        <div ref={containerRef} className="preview-content-area">
            <p className="loading-indicator">Processing Document...</p>
        </div>
    );
};

export default function App() {
    const [markdown, setMarkdown] = useState<string | null>(null);
    const [isTwoColumn, setIsTwoColumn] = useState(false);

    useEffect(() => {
        const params = new URLSearchParams(window.location.search);
        const requested = (params.get('paper') || '').trim();
        const isLocalStorageRef = /^ls:/i.test(requested);
        const isAbsoluteUrl = /^https?:\/\//i.test(requested);
        const requestedPath = isAbsoluteUrl ? requested : requested.replace(/^\/+/, '');
        const normalized =
            requestedPath === '' || requestedPath === 'index' || requestedPath === 'index.md'
                ? 'index.md'
                : requestedPath === '0' || requestedPath === 'index_0' || requestedPath === 'index_0.md'
                    ? 'index_0.md'
                    : requestedPath;

        if (isLocalStorageRef) {
            const key = requested.replace(/^ls:/i, '').trim();
            if (!key) {
                setMarkdown(`# Error: Could not load localStorage paper\n\nPass a key as \`?paper=ls:some_key\`.`);
                return;
            }

            const stored = localStorage.getItem(key);
            if (stored == null) {
                setMarkdown(`# Error: Could not load localStorage key \`${key}\`\n\nNo value found. Create it in localStorage first, or use \`?paper=index_3_2.md\`.`);
                return;
            }

            setMarkdown(stored);
            return;
        }

        const safe = isAbsoluteUrl
            ? normalized
            : /^[A-Za-z0-9_.-]+\.md$/.test(normalized)
              ? normalized
              : 'index.md';
        const baseUrl = new URL(import.meta.env.BASE_URL, window.location.origin);
        const paperUrl = isAbsoluteUrl ? safe : new URL(safe, baseUrl).toString();

        // Fetch the selected paper from public folder (default: index.md relative to BASE_URL).
        fetch(paperUrl)
            .then(response => {
                if (!response.ok) throw new Error('Failed to load content');
                return response.text();
            })
            .then(text => setMarkdown(text))
            .catch(err => {
                console.error(err);
                setMarkdown(`# Error: Could not load ${paperUrl}\n\nPlease ensure \`print/public/${isAbsoluteUrl ? 'index.md' : safe}\` exists, or open with \`?paper=index.md\`, \`?paper=index_0.md\`, or \`?paper=index_3_2.md\`.\n\nYou can also load from localStorage with \`?paper=ls:some_key\`, or pass an absolute URL.`);
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
                <button className="control-button" onClick={() => window.print()}>Print / Save PDF</button>
            </div>
            <PreviewController markdown={markdown} isTwoColumn={isTwoColumn} />
        </div>
    );
}
