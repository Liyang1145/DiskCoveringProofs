#!/usr/bin/env python3
"""Reconstruct the exact 389-cell B13 residual from frozen Lean sources.

The residual is a complement, not a stored list:

  terminal true nodes - 120 sharp ids - 1997 emitted paid ids = 389 ids.

This script parses the frozen terminal flags and the exact finite ID sets, then
checks every count and subset relation before writing the census.  It makes no
claim that a terminal is paid: the 389 ids remain unpaid mathematical work.
"""
import glob
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
LEAN = ROOT / "n11-work/lean/N11Formalization"
DBM = LEAN / "DBMSourceTreeData.lean"
SHARP = LEAN / "Patch120DomainPacket.lean"
BATCH22 = LEAN / "Paid16Batch22Packet.lean"
SURVEY = ROOT / "n11-work/evidence-20261028/inputs/paid16-general-next512.json"
CAP_CERTS = HERE / "next512-row-cap-certificates.json"
OUT = HERE / "residual389-census.json"


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def array_after(text, name):
    match = re.search(rf"def {name}\b[^\n]*:=\s*!?\[([^\]]*)\]", text)
    if not match:
        raise AssertionError(f"missing array definition {name}")
    return {int(x) for x in re.findall(r"\b\d+\b", match.group(1))}


def main():
    dbm_text = DBM.read_text()
    terminals = {
        int(node) for node, flag in re.findall(
            r"def node(\d+) : Node 5011 where.*?\n\s*terminal := (true|false)",
            dbm_text, re.S)
        if flag == "true"
    }
    sharp = array_after(SHARP.read_text(), "patchID")

    generated = set()
    for path_text in glob.glob(str(LEAN / "Paid16General*.lean")):
        text = Path(path_text).read_text()
        for match in re.finditer(r"def nodeID\b[^\n]*:=\s*!?\[([^\]]*)\]", text):
            generated.update(int(x) for x in re.findall(r"\b\d+\b", match.group(1)))
        for match in re.finditer(r"def ids\d+\b[^\n]*:=\s*\{([^}]*)\}", text):
            generated.update(int(x) for x in re.findall(r"\b\d+\b", match.group(1)))
    generated.update(array_after(BATCH22.read_text(), "nodeID"))

    survey = json.loads(SURVEY.read_text(encoding="utf-8-sig"))
    base36 = set(survey["paid_ids"])
    paid = generated | base36
    residual = sorted(terminals - sharp - paid)

    assert len(terminals) == 2506
    assert len(sharp) == 120 and sharp <= terminals
    assert len(generated) == 1961 and generated <= terminals and not generated & sharp
    assert len(base36) == 36 and base36 <= terminals and not base36 & sharp
    assert not generated & base36
    assert len(paid) == 1997 and paid <= terminals and not paid & sharp
    assert len(residual) == 389 and set(residual) <= terminals
    assert not set(residual) & paid and not set(residual) & sharp

    records = {rec["id"]: rec for rec in survey["records"]}
    assert len(records) == 512
    local_residual = sorted(set(residual) & set(records))
    assert len(local_residual) == 7
    assert all(not records[node_id]["pass"] for node_id in local_residual)

    caps = {cert["id"]: cert for cert in
            json.loads(CAP_CERTS.read_text())["certificates"]}
    assert set(caps) == set(local_residual)
    assert all(caps[node_id]["excludes_any_row_count"] for node_id in local_residual)

    result = {
        "scope": "exact complement of frozen terminal, sharp, and paid ID sets; no mathematical payment of residual cells",
        "source_sha256": {
            "DBMSourceTreeData.lean": sha256(DBM),
            "Patch120DomainPacket.lean": sha256(SHARP),
            "Paid16Batch22Packet.lean": sha256(BATCH22),
            "paid16-general-next512.json": sha256(SURVEY),
            "next512-row-cap-certificates.json": sha256(CAP_CERTS),
        },
        "counts": {
            "terminal_true": len(terminals),
            "sharp": len(sharp),
            "generated_paid": len(generated),
            "base_paid": len(base36),
            "paid_total": len(paid),
            "residual": len(residual),
        },
        "residual_ids": residual,
        "residual_ids_sha256": hashlib.sha256(
            ",".join(map(str, residual)).encode()).hexdigest().upper(),
        "local_survey_records": [
            {
                "id": node_id,
                "pass_recorded": records[node_id]["pass"],
                "excluded_for_any_row_count": True,
                "strict_cap_margin": caps[node_id]["strict_margin"],
            }
            for node_id in local_residual
        ],
        "missing_local_survey_records": len(residual) - len(local_residual),
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "residual_ids"}, indent=2))


if __name__ == "__main__":
    main()
