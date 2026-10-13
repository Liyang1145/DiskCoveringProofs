"""Import old tree as UNTRUSTED proposal; rebuild local proof and replay every leaf.

No old success flag or obsolete timing-report hash is an accepting premise.
Only the newly exported stable mathematical certificate is bound by version 2.
"""
from pathlib import Path
import gzip
import hashlib
import json
import root_certificate
import local_isolation
import candidate_tree

ROOT = Path(__file__).resolve().parent
EV = ROOT/"evidence"


def main():
    source = EV/"candidate-tree-round2.json.gz"
    target = EV/"candidate-tree-stable-v2.json.gz"
    assert not target.exists()
    root_certificate.verify()
    local_isolation.main()
    with gzip.open(source,"rt",encoding="utf8") as stream:
        proposal = json.load(stream)
    historical = proposal.pop("local_sha256")
    assert proposal["root_sha256"] == candidate_tree.sha(EV/"core-root.json")
    assert proposal["constants_sha256"] == candidate_tree.sha(EV/"angle-constants.json")
    proposal["binding_version"] = 2
    proposal["local_certificate_sha256"] = candidate_tree.sha(EV/"local-isolation-certificate.json")
    proposal["historical_timing_report_sha256_not_trusted"] = historical
    proposal["untrusted_import_tree_sha256"] = candidate_tree.sha(source)
    with gzip.open(target,"wt",encoding="utf8") as stream:
        json.dump(proposal,stream,separators=(",",":"))
    candidate_tree.verify(target)
    report = {"verified":True,"old_timing_binding_not_used_for_acceptance":True,
              "fresh_exact_local_matrix_check":True,"all_tree_leaves_replayed":True,
              "new_tree_sha256":candidate_tree.sha(target),
              "new_local_certificate_sha256":candidate_tree.sha(EV/"local-isolation-certificate.json"),
              "global_optimality_proved":False}
    (EV/"binding-repair-verified.json").write_text(json.dumps(report,indent=2),encoding="utf8")
    print("N21 STABLE INPUT BINDING REPAIRED BY FRESH PROOF AND FULL TREE REPLAY",flush=True)


if __name__ == "__main__":
    main()
