# SPDX-License-Identifier: MIT
import unittest
from fractions import Fraction as F

from diskcover_n19_upper import _covered, _nonpositive, check_n19_upper


class DiskCoverN19UpperTest(unittest.TestCase):
    def test_certified_upper(self):
        result = check_n19_upper()
        self.assertEqual(result["status"], "certified_upper_only")
        self.assertEqual(F(result["upper_squared"]), F(1, 13))
        centers = {tuple(p) for p in result["weighted_centers"]}
        self.assertEqual(len(centers), 19)
        self.assertEqual(result["checked"], {"interior_triples": 792,
                         "boundary_bisectors": 342, "boundary_stationary": 36,
                         "boundary_reference": 1})

    def test_radical_sign_and_boundary(self):
        self.assertTrue(_nonpositive(-2, 1, 4))
        self.assertTrue(_nonpositive(2, -1, 4))
        self.assertFalse(_nonpositive(0, 1, 2))
        self.assertFalse(_nonpositive(2, -1, 2))
        origin = (F(0), F(0))
        v = (F(0), F(1))
        self.assertTrue(_covered(origin, v, F(1), [origin]))
        self.assertFalse(_covered(origin, v, F(1001,1000), [origin]))
