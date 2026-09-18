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

    # Only the private structural controls need a complete source owner.
    write("ua4_comma_owner_checks.lp", [
        (root / "emdash3_2_represented_comma_families.lp").read_text(),
        fragment("comma_family_owner_checks.lpfragment"),
    ])
    write("ua4_library_projection.lp", [
        "require open emdash.emdash3_2_cubical_square_total;",
        fragment("projection_consumer.lpfragment"),
    ])

    parts = [
        "require open emdash.emdash3_2_represented_comma_families;",
        "require open emdash.emdash3_2_one_cat_modifications;",
        "require open emdash.emdash3_2_one_cat_zero_cones;",
    ]
    parts += [fragment(name) for name in (
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
