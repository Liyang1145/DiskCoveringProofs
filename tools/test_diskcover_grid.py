# SPDX-License-Identifier: MIT
"""Run with python -m unittest discover -s tools -p test_diskcover_grid.py."""
import unittest
from fractions import Fraction
from itertools import combinations

from diskcover_grid import solve_grid


class DiskCoverGridTest(unittest.TestCase):
    def test_discrete_optimum_against_brute_force(self):
        k = 2
        g = [(x, y) for x in range(-k, k + 1) for y in range(-k, k + 1)
             if x*x + y*y <= k*k]
        def dist2(a, b):
            return sum((x-y)**2 for x, y in zip(a, b))
        for n in range(1, len(g)+1):
            with self.subTest(n=n):
                brute = min(max(min(dist2(p, c) for c in centers) for p in g)
                            for centers in combinations(g, n))
                result = solve_grid(n, k)
                self.assertTrue(result['discrete_exact'])
                self.assertEqual(Fraction(result['discrete_upper_squared']),
                                 Fraction(brute, k*k))

    def test_bounds_and_witness_all_orders(self):
        k = 5
        for n in range(1, 23):
            with self.subTest(n=n):
                result = solve_grid(n, k, max_nodes=0)
                self.assertEqual(result['nodes'], 0)
                lower, upper = map(Fraction, (result['lower'], result['upper']))
                self.assertLessEqual(lower, upper)
                self.assertLessEqual(upper, 1)
                c = [tuple(map(Fraction, p)) for p in result['discrete_centers']]
                self.assertLessEqual(len(c), n)
                best = Fraction(result['discrete_upper_squared'])
                for x in range(-k, k+1):
                    for y in range(-k, k+1):
                        if x*x + y*y <= k*k:
                            self.assertTrue(any((Fraction(x,k)-a)**2
                                                +(Fraction(y,k)-b)**2 <= best
                                                for a,b in c))

    def test_limits(self):
        for args in ((0,), (23,), (1, 0), (1, 17), (1, 2, -1)):
            with self.subTest(args=args), self.assertRaises(ValueError):
                solve_grid(*args)


if __name__ == '__main__':
    unittest.main()
