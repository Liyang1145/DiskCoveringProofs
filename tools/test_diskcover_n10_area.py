# SPDX-License-Identifier: MIT
from fractions import Fraction
import unittest

from diskcover_n10_area import check_n10_area, check_n10_eight_owner


class N10AreaTests(unittest.TestCase):
    def test_directed_areas(self):
        report = check_n10_area()
        self.assertEqual(report["status"], "directed_arithmetic_only")
        lower = Fraction(report["target_area_lower"])
        gaps = [lower-Fraction(upper) for upper in report["case_area_uppers"]]
        self.assertEqual(len(gaps), 2)
        self.assertGreater(gaps[0], Fraction("0.00011015"))
        self.assertGreater(gaps[1], Fraction("0.21453"))


    def test_eight_owner_constants(self):
        report = check_n10_eight_owner()
        self.assertEqual(report["status"], "directed_arithmetic_only")
        self.assertEqual(len(report["checks"]), 26)
        self.assertIn("h times sine", report["checks"])
        self.assertIn("radial comparison", report["checks"])


if __name__ == "__main__":
    unittest.main()
