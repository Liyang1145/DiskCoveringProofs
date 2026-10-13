import argparse
import math
from pathlib import Path

import numpy as np


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    rows = []
    boundary = np.linspace(0.0, 2.0 * math.pi, 4000, endpoint=False)
    rows.append(np.column_stack((np.cos(boundary), np.sin(boundary))))
    for j in range(1, 201):
        radius = j / 200.0
        angles = np.linspace(0.0, 2.0 * math.pi, 1000, endpoint=False)
        rows.append(np.column_stack((radius * np.cos(angles), radius * np.sin(angles))))
    points = np.concatenate(rows, axis=0)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    np.save(args.output, points)
    print(points.shape, flush=True)


if __name__ == "__main__":
    main()
