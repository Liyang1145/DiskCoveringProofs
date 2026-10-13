"""Original B14 label, pure-inner-face and malformed-face functional controls."""
from pathlib import Path
from itertools import combinations
import argparse
import random
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import publish
from refine_collar_origin import exposed_mask
from partition_n23_B14_binary_origin import independent_mask, N, B

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    positive = sorted(3 | (1 << v) for v in range(B, N))
    hidden = sorted([3 | (1 << v) for v in range(B, N-1)]+[
        (1 << B) | (1 << (B+1)) | (1 << (N-1))])
    assert independent_mask(positive) == (1 << N)-1
    assert independent_mask(hidden).bit_count() == N-1
    assert independent_mask(hidden) == exposed_mask(N, B, hidden)
    rng = random.Random(23141005)
    for _ in range(200):
        faces = sorted({sum(1 << v for v in rng.sample(range(N), 3)) for _ in range(60)}
                       | {sum(1 << v for v in range(first, first+3)) for first in (14, 17, 20)})
        assert independent_mask(faces) == exposed_mask(N, B, faces)
    rejected = []
    for label, faces in (
        ("duplicate-face", positive[:1]+positive),
        ("unordered-face", list(reversed(positive))),
        ("non-triangle", sorted([3]+positive)),
        ("boolean-mask", [True]+positive),
        ("label-out-of-range", sorted(positive+[(1 << N) | 3])),
        ("missing-full-source-center-label", positive[:-1]),
        ("empty-source-faces", []),
    ):
        try:
            independent_mask(faces)
        except AssertionError:
            rejected.append(label)
        else:
            raise AssertionError(("bad binary source faces accepted", label))
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N23-B14-binary-origin-functional-face-controls-v1",
        "all_exposed_positive_and_pure_inner_hidden_label_retained": True,
        "independent_random_B14_actual_face_unions_compared": 200,
        "negative_controls_rejected": rejected,
        "source_sha256": sha(Path(__file__)),
        "partition_and_acceptor_source_sha256": sha(ROOT / "partition_n23_B14_binary_origin.py"),
        "functional_fixtures_not_full_planar_types_or_mathematical_payment": True,
        "global_optimality_proved": False,
    })
    print("N23/B14 binary origin functional face controls PASS:", len(rejected), "rejections", flush=True)


if __name__ == "__main__":
    main()
