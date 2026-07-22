from __future__ import annotations

import unittest

from scripts.warning_summary import critical_pair_shape, warning_inventory


PAIR = [
    "[emdash3_2.lp:10:0-20]",
    "Unjoinable critical pair:",
    "t ≔ @comp_fapp0 $A $x $y $z $g $f",
    "t ↪[] $left ↪* $left",
    "  with @fapp1_fapp0 $A $B $F $x $y $f ↪ $left",
    "t ↪[1] $right ↪* $right",
    "  with @comp_fapp0 $A $x $y $z $g $f ↪ $right",
]


class WarningSummaryTests(unittest.TestCase):
    def test_critical_pair_shape_extracts_term_and_participants(self) -> None:
        head, participants = critical_pair_shape(PAIR, 1)
        self.assertEqual(head, "comp_fapp0")
        self.assertEqual(participants, ["fapp1_fapp0", "comp_fapp0"])

    def test_inventory_classifies_rule_family_independently_of_order(self) -> None:
        reverse = [
            "[emdash3_2.lp:20:0-20]",
            "Unjoinable critical pair:",
            "t ≔ @fapp1_fapp0 $A $B $F $x $y $f",
            "t ↪[] $left ↪* $left",
            "  with comp_fapp0 $A $x $y $z $g $f ↪ $left",
            "t ↪[1] $right ↪* $right",
            "  with fapp1_fapp0 $A $B $F $x $y $f ↪ $right",
        ]
        inventory = warning_inventory(PAIR + reverse)
        self.assertEqual(
            inventory.rule_families[("comp_fapp0", "fapp1_fapp0")], 2
        )
        self.assertEqual(inventory.parser_issues, {})

    def test_inventory_keeps_warning_categories_and_locations(self) -> None:
        lines = PAIR + [
            "[emdash3_2.lp:30:4-6]",
            "Pattern variable A can be replaced by a '_'.",
            "[WARNING] future diagnostic",
        ]
        inventory = warning_inventory(lines)
        self.assertEqual(inventory.categories["unjoinable critical pair"], 1)
        self.assertEqual(inventory.categories["replaceable pattern variable"], 1)
        self.assertEqual(inventory.categories["other warning"], 1)
        self.assertEqual(inventory.locations["emdash3_2.lp:10"], 1)
        self.assertEqual(inventory.locations["emdash3_2.lp:30"], 2)

    def test_malformed_pair_is_reported_instead_of_silently_dropped(self) -> None:
        malformed = PAIR[:-1]
        inventory = warning_inventory(malformed)
        self.assertEqual(inventory.rule_families, {})
        self.assertEqual(
            inventory.parser_issues["critical pair with 1 participant rule(s)"],
            1,
        )


if __name__ == "__main__":
    unittest.main()
