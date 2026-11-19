# SPDX-License-Identifier: MIT
"""Focused failure and exact schema checks for the replay adapter."""
from contextlib import redirect_stderr, redirect_stdout
import hashlib
from io import BytesIO, StringIO
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import Mock, patch

import diskcover_replay as replay


class DiskCoverReplayTest(unittest.TestCase):
    def test_order_and_worker_scope(self):
        self.assertEqual({i for i in range(1,23) if replay.supports_replay(i)},
                         {13,16,17,18,19})
        self.assertFalse(replay.supports_replay(True))
        self.assertFalse(replay.supports_replay(13.0))
        for n,w in ((12,4),(13,0),(13,7),(13,True)):
            with self.subTest(n=n,w=w), self.assertRaises(replay.ReplayError):
                replay.solve_replayed(n,offline=True,workers=w)

    def test_offline_missing_or_corrupted_input(self):
        with tempfile.TemporaryDirectory() as work, patch.object(replay,"_download") as fetch:
            cache=Path(work)
            with self.assertRaisesRegex(replay.ReplayError,"missing regular proof input"):
                replay.solve_replayed(16,cache,True)
            (cache/"root16.json").write_bytes(b"not pinned")
            with self.assertRaisesRegex(replay.ReplayError,"SHA-256 mismatch"):
                replay.solve_replayed(16,cache,True)
            fetch.assert_not_called()

    def test_pinned_download_atomic_replacement(self):
        with tempfile.TemporaryDirectory() as work:
            cache=Path(work)/"root16.json"
            cache.write_bytes(b"old entry")
            expected=hashlib.sha256(b"verified").hexdigest()
            fake=Mock()
            fake.open.return_value=BytesIO(b"unverified")
            with patch.object(replay,"build_opener",return_value=fake):
                with self.assertRaisesRegex(replay.ReplayError,"SHA-256 mismatch"):
                    replay._download("https://example.com/test",expected,cache)
            self.assertEqual(cache.read_bytes(),b"old entry")
            self.assertEqual(list(cache.parent.iterdir()),[cache])
            fake.open.return_value=BytesIO(b"verified")
            with patch.object(replay,"build_opener",return_value=fake):
                replay._download("https://example.com/test",expected,cache)
            self.assertEqual(cache.read_bytes(),b"verified")

    def test_final_json_is_separate_and_nonzero_exit_rejected(self):
        command=[sys.executable,"-B","-u","-c",
                 "print('progress'); print('{\\n  \"n\": 13,\"status\": \"exact_global\"\\n}')"]
        stderr,stdout=StringIO(),StringIO()
        with redirect_stderr(stderr), redirect_stdout(stdout):
            report=replay._execute(command)
        self.assertEqual(report,{"n":13,"status":"exact_global"})
        self.assertIn("progress",stderr.getvalue())
        self.assertEqual(stdout.getvalue(),"")
        with self.assertRaisesRegex(replay.ReplayError,"exited with status 9"):
            replay._execute(command[:-1]+[command[-1]+";raise SystemExit(9)"])

    def test_outward_decimal_sqrt_strict_even_at_exact_endpoints(self):
        from fractions import Fraction as F
        a,b=map(F,replay._outward_radius(F(9,100),F(1,4),2))
        self.assertEqual((a,b),(F(29,100),F(51,100)))
        self.assertLess(a*a,F(9,100))
        self.assertGreater(b*b,F(1,4))

    def test_bad_order_or_status_is_never_an_exact_result(self):
        for payload in ({"n":19,"status":"exact_global"},
                        {"n":18,"status":"exact_global_proof_replayed"}):
            with self.assertRaisesRegex(replay.ReplayError,"order/status"):
                replay._result(19,payload,None)

    def test_exact_root_coordinate_and_center_indices(self):
        n=13
        path=replay.ROOT/replay.LOCAL_ROOT13[0]
        report={"n":n,"status":"exact_global","radius_decimal_interval":[
            "0.346645456927389643467869738193878789537187452966783984053969",
            "0.346645456927389643467869738193878789537187452966783984053970",
        ]}
        result=replay._result(n,report,path)
        self.assertEqual(result["radius_exact"],"sqrt(x[62])")
        self.assertEqual(result["centers"][0],["x[18]","x[19]"])
        self.assertEqual(result["centers"][-1],["x[42]","x[43]"])
        self.assertEqual(len(result["root"]["midpoint"]),119)
        report["radius_decimal_interval"]=["0.35","0.36"]
        with self.assertRaisesRegex(replay.ReplayError,"does not enclose"):
            replay._result(n,report,path)


if __name__=="__main__":
    unittest.main()
