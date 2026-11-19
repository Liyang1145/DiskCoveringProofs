# SPDX-License-Identifier: MIT
"""Run with python -m unittest discover -s tools -p test_diskcover_global.py."""
import unittest
from fractions import Fraction

from diskcover_global import solve_global


class DiskCoverGlobalTest(unittest.TestCase):
    def test_exact_supported_orders(self):
        for n, sq in ((1, 1), (2, 1), (3, Fraction(3, 4)),
                      (4, Fraction(1, 2)), (7, Fraction(1, 4))):
            with self.subTest(n=n):
                case = solve_global(n)
                self.assertEqual(case["status"], "exact_global")
                self.assertEqual(Fraction(case["radius_squared"]), sq)
                self.assertEqual(len(case["centers"]), n)
                self.assertEqual(case["proof"]["kind"], "analytic")
                self.assertTrue(case["proof"]["lower"])
                self.assertTrue(case["proof"]["upper"])

    def test_not_implemented_is_not_success(self):
        for n in sorted(set(range(5, 23)) - {7}):
            self.assertIsNone(solve_global(n))

    def test_invalid_order(self):
        for n in (0, 23, 1.0, True):
            with self.assertRaises(ValueError):
                solve_global(n)
