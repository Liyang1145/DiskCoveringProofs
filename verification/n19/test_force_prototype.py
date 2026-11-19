# SPDX-License-Identifier: MIT
import copy
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from force_census import check_chunk
from force_prototype import verify_tree


class ForcePrototypeTests(unittest.TestCase):
    def test_exact_sample_and_mutations(self):
        with Path(__file__).with_name("force_prototype_sample.json").open() as f:
            sample = json.load(f)
        for rec in sample:
            with self.subTest(index=rec["index"]):
                self.assertEqual(verify_tree(rec["owners"],rec["faces"],rec["tree"]),
                                 {"force":1,"empty":0,"split":0})
        rec=sample[0]
        b, faces=rec["owners"],rec["faces"]
        with self.assertRaises(ArithmeticError):
            verify_tree(b,faces,["empty"])
        corrupt=copy.deepcopy(rec["tree"])
        # Rod zero touches an anchor and an unanchored center.
        corrupt[1][1][0][0]+=1
        with self.assertRaises(ArithmeticError):
            verify_tree(b,faces,corrupt)
        corrupt=copy.deepcopy(rec["tree"])
        corrupt[1][0][0]=-1
        with self.assertRaises(ArithmeticError):
            verify_tree(b,faces,corrupt)


    def test_chunk_rejects_unbound_graph_and_false_membership(self):
        with Path(__file__).with_name("force_prototype_sample.json").open() as f:
            rec = json.load(f)[0]
        faces=tuple(rec["faces"])
        rec.update(status="excluded_force",replay={"force":1,"empty":0,"split":0})
        chunk={"owners":12,"start":0,"stop":1,"records":[rec]}
        with TemporaryDirectory() as directory:
            output=Path(directory)/"chunk.json"
            output.write_text(json.dumps(chunk))
            self.assertEqual(check_chunk(output,12,0,[faces],{},True),[])
            self.assertRaises(ArithmeticError,check_chunk,output,12,1,[faces],{},False)
            corrupt=list(faces)
            corrupt[0]+=1
            self.assertRaises(ArithmeticError,check_chunk,output,12,0,[tuple(corrupt)],{},True)
            rec["status"]="candidate_energy"
            output.write_text(json.dumps(chunk))
            self.assertRaises(ArithmeticError,check_chunk,output,12,0,[faces],{},True)
            rec["status"]="unresolved"
            output.write_text(json.dumps(chunk))
            self.assertEqual(check_chunk(output,12,0,[faces],{},True),[(12,0)])


if __name__=="__main__":
    unittest.main()
