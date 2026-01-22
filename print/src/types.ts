import { z } from 'zod';

export const NodeSchema = z.object({
    name: z.string(),
    label: z.string().optional(),
    left: z.number(),
    top: z.number(),
});

export type NodeSpec = z.infer<typeof NodeSchema>;

export const ArrowStyleSchema = z.object({
    mode: z.enum(['arrow', 'adjunction', 'corner', 'corner_inverse']).optional(),
    head: z.object({
        name: z.enum(['normal', 'none', 'epi', 'hook', 'maps_to', 'harpoon']).optional(),
        side: z.enum(['top', 'bottom']).optional(),
    }).optional(),
    tail: z.object({
        name: z.enum(['normal', 'none', 'mono', 'hook', 'maps_to']).optional(),
        side: z.enum(['top', 'bottom']).optional(),
    }).optional(),
    body: z.object({
        name: z.enum(['solid', 'dashed', 'dotted', 'squiggly', 'wavy', 'barred', 'double_barred', 'bullet_solid', 'bullet_hollow']).optional(),
    }).optional(),
    level: z.number().int().optional(),
});

export type ArrowStyleSpec = z.infer<typeof ArrowStyleSchema>;

export const ArrowSchema = z.object({
    from: z.string(),
    to: z.string(),
    name: z.string().optional(),
    label: z.string().optional(),
    curve: z.number().optional(),
    shift: z.number().optional(),
    radius: z.number().optional(),
    angle: z.number().optional(),
    label_alignment: z.enum(['over', 'left', 'right']).optional(),
    style: ArrowStyleSchema.optional(),
});

export type ArrowSpec = z.infer<typeof ArrowSchema>;

export const DiagramSpecSchema = z.object({
    version: z.number().int().optional(),
    nodes: z.array(NodeSchema),
    arrows: z.array(ArrowSchema).optional(),
});

export type DiagramSpec = z.infer<typeof DiagramSpecSchema>;

export interface Vec2 {
    x: number;
    y: number;
}

export interface ComputedArrowPath {
    d: string;
    fill: string;
    stroke: string;
    strokeWidth: number;
    strokeDasharray?: string;
    strokeLinecap?: "round" | "butt" | "square";
    mask?: string;
}

export interface ComputedArrowPart {
    props: {
        d: string;
        fill: string;
        stroke: string;
        strokeWidth: number;
        strokeLinecap: "round" | "butt" | "square";
        transform?: string;
        mask?: string;
    }
}

export interface ComputedArrow {
    key: string;
    spec: ArrowSpec;
    paths: ComputedArrowPath[];
    label: {
        text?: string;
        props: {
            x: number;
            y: number;
            textAnchor: string;
            dominantBaseline: string;
            fontSize: number;
        }
    };
    heads: ComputedArrowPart[];
    tail: ComputedArrowPart[];
    midpoint: Vec2;
    // For interaction/debugging
    bbox?: { x: number, y: number, width: number, height: number };
}

export interface ComputedMask {
    id: string;
    paths: {
        d: string;
        fill: string;
        stroke: string;
        strokeWidth: number;
    }[];
}

export interface ComputedDiagram {
    nodes: NodeSpec[];
    arrows: ComputedArrow[];
    masks: ComputedMask[];
    viewBox: string;
    error: string | null;
}