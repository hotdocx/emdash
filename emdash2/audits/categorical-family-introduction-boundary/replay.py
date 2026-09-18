#!/usr/bin/env python3
"""Assemble the retained Γ/H consumers against their current library owners."""

from pathlib import Path
import re


def main() -> None:
    audit = Path(__file__).resolve().parent
    root = audit.parents[1]
    output = root / "tmp/probes"
    output.mkdir(parents=True, exist_ok=True)

    def fragment(name: str) -> str:
        return (audit / name).read_text()

    def write(name: str, parts: list[str]) -> None:
        source = "\n".join(parts)
        path = output / name
        path.write_text(source)
        count = len(re.findall(r"(?m)^\s*assert(?:not)?\b", source))
        print(f"{path.relative_to(root)}: {count} assertions")

    # The graph helpers are protected, so retain the complete source owner.
    graph = (root / "emdash3_2_gray_transformation_graph.lp").read_text()
    constructor = fragment("constructor_fragment.lp")
    write("ua4_library_actions.lp", [graph, constructor] + [
        fragment(name) for name in (
            "triangle.lpfragment", "next_source.lpfragment",
            "third_source.lpfragment",
        )
    ])
    write("ua4_library_projection.lp", [
        "require open emdash.emdash3_2_cubical_square_total;",
        fragment("projection_consumer.lpfragment"),
    ])

    parts = [
        graph,
        "require open emdash.emdash3_2_iso_evidence_constructors;",
        "require open emdash.emdash3_2_one_cat_modifications;",
        "require open emdash.emdash3_2_one_cat_zero_cones;",
        "require open emdash.emdash3_2_one_cat_adjunction_family_views;",
        constructor.split("// The target side is the actual action", 1)[0],
    ]
    parts += [fragment(name) for name in (
        "whole_source.lpfragment", "target_section_extraction.lpfragment",
        "target_basechange_link.lpfragment", "target_section_grouping.lpfragment",
        "target_classification.lpfragment", "target_classification_controls.lpfragment",
        "triangle_comparison.lpfragment", "triangle_controls.lpfragment",
        "boundary_comparison.lpfragment", "boundary_reconstruction.lpfragment",
        "whole_homology_comparison.lpfragment", "whole_homology_point_view.lpfragment",
        "whole_homology_controls.lpfragment",
    )]
    # All computation/comparison rules now come from the positive owners.
    assert not any(re.search(r"(?m)^(?:unif_rule|rule)\b", p) for p in parts[1:])
    write("ua4_library_whole_homology.lp", parts)


if __name__ == "__main__":
    main()
