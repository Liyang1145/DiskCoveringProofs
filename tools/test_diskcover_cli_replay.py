# SPDX-License-Identifier: MIT
"""Proof-runner routing and fail-closed JSON output."""
import contextlib
from io import StringIO
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from diskcover_replay import ReplayError
from solve_diskcover import main


class ProofCLI(unittest.TestCase):
    def call(self, args):
        out, err = StringIO(), StringIO()
        status = 0
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            try:
                main(args)
            except SystemExit as exc:
                status = exc.code
        return status, out.getvalue(), err.getvalue()

    def test_replay_selected_and_flags_forwarded(self):
        exact = {"n": 18, "status": "exact_global", "radius_exact": "sqrt(t_*)"}
        with patch("diskcover_replay.solve_replayed", return_value=exact) as replay:
            code, out, _ = self.call(["18", "--require-global-proof", "--offline",
                                      "--proof-data-dir", "test-data", "--proof-workers", "2"])
        self.assertEqual(code, 0)
        self.assertEqual(json.loads(out), exact)
        replay.assert_called_once_with(18, Path("test-data"), offline=True, workers=2)

    def test_replay_failure_has_no_answer(self):
        with patch("diskcover_replay.solve_replayed", side_effect=ReplayError("bad proof input")):
            code, out, err = self.call(["16", "--require-global-proof"])
        self.assertNotEqual(code, 0)
        self.assertEqual(out, "")
        self.assertIn("did not complete", err)

    def test_unknown_and_static_do_not_run_replay(self):
        with patch("diskcover_replay.solve_replayed") as replay:
            code, out, _ = self.call(["15", "--require-global-proof"])
            self.assertEqual(code, 2)
            self.assertEqual(out, "")
            code, out, _ = self.call(["4", "--require-global-proof"])
            self.assertEqual(code, 0)
            self.assertEqual(json.loads(out)["status"], "exact_global")
            replay.assert_not_called()

    def test_catalog_does_not_run_proof(self):
        with patch("diskcover_replay.solve_replayed") as replay:
            code, out, _ = self.call(["19"])
            replay.assert_not_called()
        self.assertEqual(code, 0)
        self.assertEqual(json.loads(out)["source"]["status"], "independent_global_replay")


if __name__ == "__main__":
    unittest.main()
