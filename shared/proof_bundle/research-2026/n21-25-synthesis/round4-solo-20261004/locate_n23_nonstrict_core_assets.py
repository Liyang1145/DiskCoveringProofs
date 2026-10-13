"""Read archive directories for exact historical N23 core prerequisites."""
from pathlib import Path
import argparse
import zipfile

from n25_outer_search import publish
from stream_catalog import sha

ROOT = Path(__file__).resolve().parent
assert __debug__


def wanted(name):
    name = name.replace("\\", "/")
    return (
        name.endswith("/n23-core-angle-resume1/core-angle-tree.json.gz")
        or name.endswith("/evidence/n23/local-isolation-certificate.json")
        or name.endswith("/evidence/n23/algebraic-check1/root-verified.json")
        or name.endswith("/evidence/n23/algebraic-check1/upper-verified.json")
    )


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    incoming = ROOT.parents[4]
    assert incoming.name == "_incoming-local-math-20261004"
    archives = sorted(incoming.glob("math-delta-*.zip"))
    assert len(archives) == 134
    scanned, matches = [], []
    for archive in archives:
        with zipfile.ZipFile(archive) as stream:
            infos = stream.infolist()
            for info in infos:
                if wanted(info.filename):
                    name = info.filename.replace("\\", "/")
                    assert not name.startswith("/") and ".." not in Path(name).parts
                    matches.append({
                        "archive": archive.name, "member": name,
                        "bytes": info.file_size, "zip_crc32": info.CRC,
                    })
            scanned.append({"archive": archive.name, "members_scanned": len(infos)})
        if len(scanned) % 20 == 0:
            print("N23 nonstrict prerequisite archive-directory scan", len(scanned),
                  "/134; names", len(matches), flush=True)
    output.mkdir()
    publish(output / "OBSERVATION.json", {
        "schema": "N23-nonstrict-core-prerequisite-central-directory-observation-v1",
        "incoming": str(incoming), "archives_scanned": scanned,
        "matching_members": matches, "no_member_extracted_or_math_proof_paid": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    print("N23 core prerequisite names located:", len(matches), flush=True)


if __name__ == "__main__":
    main()
