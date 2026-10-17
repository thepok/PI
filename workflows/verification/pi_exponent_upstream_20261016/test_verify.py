#!/usr/bin/env python3
"""Failure-path checks for the external verification report parser."""

import unittest

from verify import (ALLOWED_AXIOMS, AuditError, THEOREMS, external_allowed,
                    masked_lean, parse_axioms, source_imports)


def good_report() -> str:
    return "\n".join(f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
                     for name in THEOREMS) + "\n"


class AuditParserTests(unittest.TestCase):
    def test_accepts_complete_wrapped_report(self):
        output = good_report().replace("[propext, Classical.choice, Quot.sound]",
                                       "[propext,\n Classical.choice, Quot.sound]")
        actual = parse_axioms("A harmless #check output\n" + output)
        self.assertEqual(set(actual), set(THEOREMS))
        self.assertTrue(all(set(value) == ALLOWED_AXIOMS for value in actual.values()))

    def test_rejects_missing_report(self):
        with self.assertRaises(AuditError):
            parse_axioms("\n".join(good_report().splitlines()[:-1]))

    def test_rejects_duplicate_report(self):
        with self.assertRaises(AuditError):
            parse_axioms(good_report() + good_report().splitlines()[0] + "\n")

    def test_rejects_disallowed_axiom(self):
        with self.assertRaises(AuditError):
            parse_axioms(good_report().replace("Quot.sound", "sorryAx", 1))

    def test_rejects_unexpected_report(self):
        with self.assertRaises(AuditError):
            parse_axioms(good_report() + "'Other.theorem' depends on axioms: [propext]\n")

    def test_rejects_malformed_report(self):
        with self.assertRaises(AuditError):
            parse_axioms(good_report().replace("Quot.sound]", "Quot.sound,]", 1))
        with self.assertRaises(AuditError):
            parse_axioms(good_report() + "'Other.theorem' depends on axioms: [unfinished\n")

    def test_source_lexer_and_import_boundary(self):
        source = ('/- outer /- axiom fake -/ sorry -/\n'
                  'import Mathlib -- native_decide\n'
                  'import Lean.Elab.Tactic.Omega\n'
                  'def text := "unsafe and \\"sorry\\""\n')
        self.assertEqual(source_imports(source, "test"), ["Mathlib", "Lean.Elab.Tactic.Omega"])
        self.assertTrue(external_allowed("Mathlib"))
        self.assertTrue(external_allowed("Mathlib.Analysis.Real.Pi.Bounds"))
        self.assertFalse(external_allowed("ComparatorChallenges.PiExponent"))
        self.assertFalse(external_allowed("MathlibUnreviewed"))
        with self.assertRaises(AuditError):
            source_imports("import Mathlib\naxiom fake : False\n", "test")
        with self.assertRaises(AuditError):
            masked_lean("/- unfinished")


if __name__ == "__main__":
    unittest.main()
