# SPDX-License-Identifier: MIT
"""Read the public handoff index; check navigation hashes, never mathematical truth."""
import argparse
import json
from pathlib import Path
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    state = json.loads((root / "PROJECT_STATE.json").read_text(encoding="utf-8"))
    if args.check:
        manifest = {}
        for line in (root / "manifests/FILES.jsonl").read_text(encoding="utf-8").splitlines():
            item = json.loads(line)
            if item["path"] in manifest:
                raise ValueError("Duplicate delivery entry")
            manifest[item["path"]] = item
        seen = set()
        for order in state["orders"]:
            if order["n"] in seen:
                raise ValueError("Duplicate order")
            seen.add(order["n"])
            if not order["authorities"]:
                raise ValueError("Order has no authority")
            for authority in order["authorities"]:
                item = manifest.get(authority["path"])
                if item is None or (item["sha256"], item["bytes"]) != (authority["sha256"], authority["bytes"]):
                    raise ValueError("Authority differs from delivery manifest: " + authority["path"])
        if seen != {11, 12, 14, 21, 22, 23, 24, 25, 26}:
            raise ValueError("Incomplete order index")
        if state["complete_global_math_replay_available"] is not False:
            raise ValueError("Unexpected unrestricted replay claim")
        print("HANDOFF INDEX CHECK PASSED; manifest declarations only, not math or full file integrity.", file=sys.stderr if args.json else sys.stdout)
    if args.json:
        print(json.dumps(state, ensure_ascii=True, indent=2))
    else:
        print("DiskCoveringProofs: public handoff snapshot " + state["updated_at"])
        for order in state["orders"]:
            print(f"n={order['n']}: {order['current_scope']}")
            print("  Next: " + order["next_actions"][0])
        print("Asset locations and pinned hashes: PROJECT_STATE.json")
        print("Downloads and server export: docs/REPLAY_ASSET_PLAN.md")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        sys.exit("HANDOFF INDEX FAILED: " + str(error))
