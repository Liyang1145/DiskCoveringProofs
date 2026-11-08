"""Replay the entire covering proof with Python's standard library."""

from pathlib import Path

import eleven
import local
import lower
import network
import topology
import upper


def main():
    if not __debug__:
        raise RuntimeError("Run the verifier with assertions enabled.")
    upper.certify()
    local.main()
    lower.ten()
    lower.eleven()
    lower.high_classification()
    eleven.redundant_unmarked()
    eleven.redundant_marked()
    eleven.sector_certificate()
    eleven.ear_certificate()
    topology.main()
    network.check_files([Path(__file__).with_name("cover-proof.json.gz")], require_complete=True)
    print("All face representatives excluded below the exact construction radius R.")


if __name__ == "__main__":
    main()
