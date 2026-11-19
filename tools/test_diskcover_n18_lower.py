# SPDX-License-Identifier: MIT
import unittest
from fractions import Fraction
from unittest.mock import patch

import diskcover_n18_lower as cert


class N18LowerTests(unittest.TestCase):
    def test_exact_two_circle_exclusion(self):
        result = cert.check_n18_lower()
        self.assertEqual(result["lower_exact"], "0.26590")
        self.assertEqual(result["radial_bins"], 53_180)
        self.assertEqual(result["max_weighted_sum_upper"], "7851033/2500000")
        self.assertLess(Fraction(result["max_weighted_sum_upper"]),
                        Fraction(result["pi_lower"]))

    def test_reject_underestimated_inner_angle(self):
        with patch.object(cert, "U", cert.U - 1):
            with self.assertRaisesRegex(ArithmeticError, "inner angular cap"):
                cert.check_n18_lower()

    def test_reject_nonclosing_weight(self):
        with patch.object(cert, "W", 100):
            with self.assertRaisesRegex(ArithmeticError, "did not close"):
                cert.check_n18_lower()


if __name__ == "__main__":
    unittest.main()
