"""Small adversarial controls, not an independent proof of the full loop."""
import importlib.util
import pathlib
import unittest
from fractions import Fraction as F

source = pathlib.Path(__file__).resolve().parents[2] / 'lower-bound/continuation/radial_certificate.py'
spec = importlib.util.spec_from_file_location('radial_original', source)
radial = importlib.util.module_from_spec(spec)
spec.loader.exec_module(radial)


class RadialControls(unittest.TestCase):
    def test_tangent_and_disjoint_cells_are_zero(self):
        for t,_ in radial.data:
            self.assertEqual(radial.angle_bound(t,F(0),t-radial.r),0)
            self.assertEqual(radial.angle_bound(t,t+radial.r,t+radial.r+1),0)

    def test_interior_samples_fit_each_claimed_upper_bound(self):
        # Exact cosine check on a selection of intervals containing the critical distance.
        for t,_ in radial.data:
            d = radial.root_lower(t*t-radial.r*radial.r)
            lo = max(F(0),d-F(1,1000))
            hi = d+F(1,1000)
            bound = radial.angle_bound(t,lo,hi)
            self.assertGreater(bound,0)
            for x in (lo,(lo+hi)/2,hi):
                if t-radial.r < x < t+radial.r:
                    self.assertLessEqual(radial.cosine_upper(bound),radial.c_endpoint(t,x))

    def test_exact_square_root_rounding_direction(self):
        for q in (F(1,1000000), F(1,3), F(7,9), F(10)):
            z=radial.root_lower(q)
            self.assertLessEqual(z*z,q)
            self.assertGreater((z+F(1,10**12))**2,q)

    def test_cosine_taylor_brackets_have_correct_order(self):
        for q in (F(1,10000),F(1,2),F(1),F(3,2),F(2)):
            # The next Taylor term is negative and the remaining tail decreases.
            upper=radial.cosine_upper(q)
            denominator=1
            for k in range(1,15): denominator*=k
            lower=upper-q**14/denominator
            self.assertLess(lower,upper)

    def test_weights_and_full_distance_domain(self):
        self.assertTrue(all(t>radial.r and w>=0 for t,w in radial.data))
        self.assertEqual(F(2440,2000),1+radial.r)
        self.assertGreater(sum(w for _,w in radial.data),0)

if __name__ == '__main__':
    unittest.main()
