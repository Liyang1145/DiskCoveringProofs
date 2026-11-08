import unittest
from fractions import Fraction as F
import exact_masks as e

class Controls(unittest.TestCase):
    def test_radical_sign_at_equality(self):
        self.assertEqual(e.sign(F(2),F(-1),F(4)),0)
        self.assertEqual(e.sign(F(2),F(-1),F(3)),1)
        self.assertEqual(e.sign(F(-2),F(1),F(3)),-1)

    def test_collinear_tangent(self):
        x=e.generate({'radius':'1/2','points':[['-1/2','0'],['1/2','0'],['0','0']]})
        self.assertEqual(x['tangent_pairs'],1)
        self.assertIn('0x7',x['masks_hex'])

    def test_three_circles_common_singleton(self):
        # 4/5,3/5 rational unit circle points: intersection reduces to the origin.
        x=e.generate({'radius':'1','points':[['1','0'],['-4/5','3/5'],['-4/5','-3/5']]})
        self.assertIn('0x7',x['masks_hex'])

    def test_outside_witness_and_duplicate_rejected(self):
        with self.assertRaises(ValueError):e.generate({'radius':'1','points':[['2','0']]})
        with self.assertRaises(ValueError):e.generate({'radius':'1','points':[['0','0'],['0','0']]})

    def test_singleton(self):
        x=e.generate({'radius':'1/10','points':[['0','0']]})
        self.assertEqual(x['masks_hex'],['0x1'])

if __name__=='__main__':unittest.main()
