# SPDX-License-Identifier: MIT
"""Mathematical rejection controls; never modify archived or shipped inputs."""
import copy
import gzip
import json
from pathlib import Path
import tempfile
import unittest

import mathcheck_n12 as n12
import mathcheck_n11 as n11


class MathematicalRejectionControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.domain = json.loads(gzip.decompress((n12.DATA/"domain.json.gz").read_bytes()))
        cls.root = json.loads((n12.DATA/"root.json").read_text())
        cls.atom = next(v for v in cls.domain["leaves"] if v["type"] == "atomic")
        n12.init_worker(n12.DATA)

    def test_exact_root_recomputed(self):
        self.assertTrue(n12.check_root(n12.DATA/"root.json")["strict_self_map"])

    def test_forged_equation_rejected(self):
        doc = copy.deepcopy(self.root)
        doc["polynomials"][0] += " + 1"
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp)/"root.json"; path.write_text(json.dumps(doc))
            with self.assertRaisesRegex(ValueError, "polynomial differs"):
                n12.check_root(path)

    def test_singular_preconditioner_rejected(self):
        doc = copy.deepcopy(self.root); doc["preconditioner"] = [["0"]*4 for _ in range(4)]
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp)/"root.json"; path.write_text(json.dumps(doc))
            with self.assertRaisesRegex(ValueError, "contraction failed"):
                n12.check_root(path)

    def test_missing_terminal_is_coverage_gap(self):
        doc = {**self.domain, "leaves": self.domain["leaves"][:-1]}
        with self.assertRaisesRegex(ValueError, "coverage gap"):
            n12.check_partition(doc)

    def test_duplicate_terminal_rejected(self):
        doc = {**self.domain, "leaves": self.domain["leaves"]+[self.domain["leaves"][0]]}
        with self.assertRaisesRegex(ValueError, "duplicate"):
            n12.check_partition(doc)

    def test_pending_is_not_certified(self):
        doc = {**self.domain, "pending": [self.domain["leaves"][0]["H"]]}
        with self.assertRaisesRegex(ValueError, "pending"):
            n12.check_partition(doc)

    def test_wrong_core_witness_rejected(self):
        with self.assertRaisesRegex(ValueError, "core witness"):
            n12.check_prunes(self.domain, [["0", "0"]])

    def test_real_atomic_inequality_recomputed(self):
        result = n12.atomic_replay((0, self.atom, 26))
        self.assertEqual(result["gap"], 3736554)
        self.assertEqual(result["ring_boxes"], 5247)
        self.assertGreater(result["demand"], 10*result["maximum_capture"])

    def test_zero_demand_cannot_exclude(self):
        atom = copy.deepcopy(self.atom)
        atom["proposal"]["weights"] = [[0]*len(v) for v in atom["proposal"]["weights"]]
        with self.assertRaisesRegex(ValueError, "invalid demand"):
            n12.atomic_replay((0, atom, 26))

    def test_unknown_unit_set_rejected(self):
        with self.assertRaisesRegex(ValueError, "unsupported atom count"):
            n12.atomic_replay((0, {**self.atom, "atomN": 8193}, 26))

    def test_unsafe_integer_scale_rejected(self):
        with self.assertRaisesRegex(ValueError, "unsupported scale"):
            n12.atomic_replay((0, self.atom, 29))

    def test_nonunit_vector_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            data = Path(tmp)
            (data/"vectors-2048.json").write_text(json.dumps([["0", "0"]]*2048))
            with self.assertRaisesRegex(ValueError, "unit vector"):
                n12.init_worker(data)
        n12.init_worker(n12.DATA)

    def test_n11_perturbed_root_is_not_saved_pass(self):
        data = json.loads((n11.DEFAULT_DATA/"root_input.json").read_text())
        data["center_hex"][0] = "0x1.0p+0"
        with self.assertRaises((ValueError, ArithmeticError)):
            n11.root_check(data)


if __name__ == "__main__":
    unittest.main(verbosity=2)
