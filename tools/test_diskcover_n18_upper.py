# SPDX-License-Identifier: MIT
import unittest
from unittest.mock import patch

import diskcover_n18_upper as cert


class N18UpperTests(unittest.TestCase):
    def test_exact_rational_cover(self):
        result = cert.check_n18_upper()
        self.assertEqual(result["status"], "certified_upper_only")
        self.assertEqual(result["checked"], {
            "visited": 49725, "outside": 6528, "covered": 30766,
            "split": 12431, "max_depth": 199,
        })

    def test_reject_incomplete_cover(self):
        with patch.object(cert, "RADIUS_NUMERATOR", 29*10**58), \
             patch.object(cert, "RADIUS_DISPLAY", "0.29"+"0"*58):
            with self.assertRaisesRegex(ArithmeticError, "unresolved target box"):
                cert.check_n18_upper()

    def test_duplicate_center_rejected(self):
        with patch.object(cert, "CENTER_NUMERATORS",
                          cert.CENTER_NUMERATORS[:-1] + cert.CENTER_NUMERATORS[:1]):
            with self.assertRaisesRegex(ArithmeticError, "18 distinct"):
                cert.check_n18_upper()


if __name__ == "__main__":
    unittest.main()
