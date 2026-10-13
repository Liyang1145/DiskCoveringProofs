import argparse
import json
import math
from fractions import Fraction
from pathlib import Path

import numpy as np


def scalar(text: str) -> float:
    return float(Fraction(text))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--geometry", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    obj = json.loads(args.geometry.read_text(encoding="utf-8"))
    q = math.sqrt(2.0)
    a = math.sqrt(2.0 / 3.0 - q / 3.0)
    rows = []
    boundary = np.linspace(0.0, 2.0 * math.pi, 4000, endpoint=False)
    rows.append(np.column_stack((np.cos(boundary), np.sin(boundary))))
    for j in range(1, 201):
        radius = j / 200.0
        angles = np.linspace(0.0, 2.0 * math.pi, 1000, endpoint=False)
        rows.append(np.column_stack((radius * np.cos(angles), radius * np.sin(angles))))
    anchors = []
    for x, y in obj["anchors"]:
        anchors.append(
            (
                a * (scalar(x[0]) + scalar(x[1]) * q),
                a * (scalar(y[0]) + scalar(y[1]) * q),
            )
        )
    anchors = np.asarray(anchors, dtype=float)
    rows.append(anchors)
    for anchor in anchors:
        angle = math.atan2(anchor[1], anchor[0])
        local = np.linspace(angle - 0.003, angle + 0.003, 121)
        rows.append(np.column_stack((np.cos(local), np.sin(local))))
    points = np.concatenate(rows, axis=0)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    np.save(args.output, points)
    print({"shape": points.shape, "anchors": len(anchors)}, flush=True)


if __name__ == "__main__":
    main()
