#!/usr/bin/env python3
"""Finite semantic audit, independent of the unrepaired Lambdapi encoding.

Z is the walking 2-cell p ⇒ q : x → y. D(x)=1, D(y)=[1], with
D(p)(*)=0 and D(q)(*)=1. The two coefficient models below are strict
2-functors E:Z→Cat and strict transformations F:D⇒E. They realize both
incomparable diagonal values of the old unrestricted Homd target.

The positive comparison uses a proposed *supporting index*, not a new
definition of homd_int. Its objects are (y,v,q:c→y); arrows are
(s, β:D(s)v→w, θ:q'⇒s∘q). All categories here are finite and locally
posetal, so β/θ coherence is equality between unique parallel arrows.
This is a strict 2-dimensional model, not an ω-categorical implementation.
"""

from dataclasses import dataclass
from itertools import product
import json


def closure(objects, generators):
    relation = {(x, x) for x in objects} | set(generators)
    while True:
        extended = relation | {(x, z) for x, y in relation for w, z in relation if y == w}
        if extended == relation:
            return frozenset(relation)
        relation = extended


BASE = {"ix": ("x", "x"), "p": ("x", "y"), "q": ("x", "y"), "iy": ("y", "y")}
D_OBJECTS = {"x": (0,), "y": (0, 1)}


def base_compose(g, f):
    assert BASE[f][1] == BASE[g][0]
    return g if f in ("ix", "iy") else f


def base_cell(f, g):
    return f == g or (f, g) == ("p", "q")


def d_transport(r, v):
    return {"p": 0, "q": 1}.get(r, v)


@dataclass(frozen=True)
class Point:
    base: str
    value: int
    path: str


@dataclass(frozen=True)
class Arrow:
    source: Point
    target: Point
    base: str


class NativeIndexModel:
    def __init__(self, c):
        self.source = c
        self.objects = tuple(
            Point(y, v, q)
            for y in D_OBJECTS for v in D_OBJECTS[y]
            for q, endpoints in BASE.items() if endpoints == (c, y)
        )
        self.arrows = frozenset(
            Arrow(a, b, s)
            for a, b in product(self.objects, repeat=2)
            for s, endpoints in BASE.items()
            if endpoints == (a.base, b.base)
            and d_transport(s, a.value) <= b.value
            and base_cell(b.path, base_compose(s, a.path))
        )
        self.cells = frozenset(
            (f, g) for f, g in product(self.arrows, repeat=2)
            if f.source == g.source and f.target == g.target and base_cell(f.base, g.base)
        )

    def compose(self, g, f):
        assert f.target == g.source
        result = Arrow(f.source, g.target, base_compose(g.base, f.base))
        assert result in self.arrows
        return result

    def validate(self):
        for f in self.arrows:
            left = Arrow(f.target, f.target, "i" + f.target.base)
            right = Arrow(f.source, f.source, "i" + f.source.base)
            assert self.compose(left, f) == f == self.compose(f, right)
            assert (f, f) in self.cells
        assert all(f == g for f, g in self.cells if (g, f) in self.cells)
        for f, g, h in product(self.arrows, repeat=3):
            if f.target == g.source and g.target == h.source:
                assert self.compose(h, self.compose(g, f)) == self.compose(self.compose(h, g), f)
            if (f, g) in self.cells and (g, h) in self.cells:
                assert (f, h) in self.cells
        for (f, f1), (g, g1) in product(self.cells, repeat=2):
            if f.target == g.source:
                assert (self.compose(g, f), self.compose(g1, f1)) in self.cells


def precompose_point(point, r):
    return Point(point.base, point.value, base_compose(point.path, r))


def precompose_arrow(arrow, r):
    return Arrow(precompose_point(arrow.source, r), precompose_point(arrow.target, r), arrow.base)


def audit():
    # Independent fibre-2-cell discriminator. In the walking 2-cell category,
    # Hom(-,y) sends p/q to the functors 1→[1] selecting p/q. Total source
    # reversal would demand the missing component q→p; dimension-1
    # transposition retains the available component p→q.
    precompose_p = base_compose("iy", "p")
    precompose_q = base_compose("iy", "q")
    assert base_cell(precompose_p, precompose_q)
    assert not base_cell(precompose_q, precompose_p)
    sx, sy = NativeIndexModel("x"), NativeIndexModel("y")
    for index in (sx, sy):
        index.validate()
    # The target index retains the walking base 2-cell, including noninvertibility.
    nonidentity = [(f, g) for f, g in sx.cells if f != g]
    assert nonidentity and all((g, f) not in sx.cells for f, g in nonidentity)

    # Source change S(r):S_y→S_x is a strict 2-functor for r=p,q.
    for r in ("p", "q"):
        assert all(precompose_point(a, r) in sx.objects for a in sy.objects)
        assert all(precompose_arrow(f, r) in sx.arrows for f in sy.arrows)
        assert all((precompose_arrow(f, r), precompose_arrow(g, r)) in sx.cells for f, g in sy.cells)
        for f, g in product(sy.arrows, repeat=2):
            if f.target == g.source:
                assert precompose_arrow(sy.compose(g, f), r) == sx.compose(
                    precompose_arrow(g, r), precompose_arrow(f, r))

    # α:p⇒q gives S(q)⇒S(p), not S(p)⇒S(q).
    def alpha_component(a):
        return Arrow(precompose_point(a, "q"), precompose_point(a, "p"), "iy")

    for a in sy.objects:
        cell = alpha_component(a)
        assert cell in sx.arrows
        assert Arrow(cell.target, cell.source, "iy") not in sx.arrows
    for f in sy.arrows:
        assert sx.compose(precompose_arrow(f, "p"), alpha_component(f.source)) == sx.compose(
            alpha_component(f.target), precompose_arrow(f, "q"))

    # E(x) is discrete {0,1}; F_x(*)=1. E_p=(a,b), E_q=(c,d),
    # F_y=(b,d). Edges a→c and b→d give E(α), including its F comparison.
    examples = {
        "forward_direction_fails": [("a", "b"), ("b", "d"), ("a", "c")],
        "reverse_direction_fails": [("a", "c"), ("c", "d"), ("b", "d")],
    }
    observations = {}
    for name, generators in examples.items():
        order = closure("abcd", generators)
        ep, eq, fy = ("a", "b"), ("c", "d"), ("b", "d")
        assert all((ep[u], eq[u]) in order for u in (0, 1))  # E(α)
        assert (fy[0], fy[1]) in order  # F_y is a functor
        assert ep[1] == fy[d_transport("p", 0)] and eq[1] == fy[d_transport("q", 0)]
        # The α compatibility also holds: both sides are the unique b→d.
        assert (ep[1], eq[1]) == (fy[0], fy[1])

        def m(index, u, a):
            assert a in index.objects
            if a.base == "x":
                return u == 1  # Hom_discrete(2)(u,F_x(*))
            transported = u if a.path == "iy" else {"p": ep, "q": eq}[a.path][u]
            return (transported, fy[a.value]) in order

        # Every coefficient point defines a strict functor on the positive
        # supporting index. Values are Empty/Unit, with at most one map/cell.
        for index, source_values in [(sx, (0, 1)), (sy, "abcd")]:
            for u in source_values:
                assert all(not m(index, u, f.source) or m(index, u, f.target) for f in index.arrows)
        # Negative fibre action u'→u induces Hom(u,−)→Hom(u',−).
        for u1, u in order:
            assert all(not m(sy, u, a) or m(sy, u1, a) for a in sy.objects)

        # Native x-action and the retained base-2-cell use the SAME original E.
        noninvertible_observations = []
        for u in (0, 1):
            for a in sy.objects:
                for r, transport in [("p", ep), ("q", eq)]:
                    assert m(sx, u, precompose_point(a, r)) == m(sy, transport[u], a)
                source = m(sx, u, precompose_point(a, "q"))
                target = m(sx, u, precompose_point(a, "p"))
                assert not source or target
                if source != target:
                    noninvertible_observations.append({"u": u, "v": a.value})
        assert noninvertible_observations

        # Old T_y=[D_y,[Hom_Z(x,y)^op,Cat]] acts at p/q by the two
        # diagonal evaluations H(D(p)*,p) and H(D(q)*,q).
        h = {(v, r): m(sx, 0, Point("y", v, r)) for v in (0, 1) for r in ("p", "q")}
        for (v, r), (w, s) in product(h, repeat=2):
            if v <= w and base_cell(s, r):
                assert not h[v, r] or h[w, s]  # H is a legitimate whole functor
        diagonal = (h[0, "p"], h[1, "q"])
        assert diagonal == ((True, False) if name.startswith("forward") else (False, True))
        observations[name] = {
            "E_y_generators": generators,
            "H_rows_v0_v1_columns_p_q": [[int(h[v, r]) for r in ("p", "q")] for v in (0, 1)],
            "old_diagonal_Empty0_Unit1": [int(value) for value in diagonal],
            "correct_source_alpha_noninvertible_components": noninvertible_observations,
        }
    return {
        "scope": "strict walking-2-cell base, finite ordinary fibres; no Lambdapi or omega qualification",
        "old_local_target": "neither orientation of the base 2-cell works for all original inputs",
        "negative_fibre_source": "dimension-1 transpose preserves p⇒q; total reversal demands missing q⇒p",
        "supporting_index": {
            "S_x_objects": len(sx.objects), "S_x_arrows": len(sx.arrows),
            "S_x_nonidentity_2_cells": len(nonidentity),
            "S_y_objects": len(sy.objects), "S_y_arrows": len(sy.arrows),
            "axioms_source_action_and_native_Hom_observations": "passed",
        },
        "models": observations,
    }


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("run without -O: this semantic audit requires its assertions")
    print(json.dumps(audit(), indent=2, ensure_ascii=False))
