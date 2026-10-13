import argparse
from pathlib import Path

import numpy as np


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--base", type=Path, required=True)
    parser.add_argument("--extra", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    base = np.load(args.base)
    extra = np.load(args.extra)
    merged = np.unique(np.vstack((base, extra)).round(14), axis=0)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    np.save(args.output, merged)
    print({"base": len(base), "extra": len(extra), "merged": len(merged)}, flush=True)


if __name__ == "__main__":
    main()
