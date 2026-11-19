# SPDX-License-Identifier: MIT
import unittest
from fractions import Fraction

from diskcover_n20_upper import _covered, _outside, _replay, check_n20_upper


class DiskCoverN20UpperTest(unittest.TestCase):
    def test_certified_upper(self):
        out = check_n20_upper()
        self.assertEqual(out["status"], "certified_upper_only")
        self.assertEqual(Fraction(out["upper_rational"]), Fraction("0.2708481784399775"))
        self.assertEqual(Fraction(out["upper_squared"]), Fraction("0.2708481784399775")**2)
        self.assertEqual(len({tuple(p) for p in out["center_numerators"]}), 20)
        self.assertEqual(out["checked"], dict(
            visited=13589, outside=1728, covered=8464, split=3397, max_depth=55,
        ))

    def test_closed_box_boundaries(self):
        self.assertFalse(_outside((3, 4, 4, 5), 25))
        self.assertTrue(_outside((3, 4, 4, 5), 24))
        self.assertTrue(_covered((0, 3, 0, 4), [(0, 0)], 25))
        self.assertFalse(_covered((0, 3, 0, 4), [(0, 0)], 24))

    def test_unresolved_boxes_fail(self):
        with self.assertRaisesRegex(ArithmeticError, "unresolved target box"):
            _replay([(0, 0)], 4, 3, 1)
