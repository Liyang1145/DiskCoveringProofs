"""Independent rod injections, small region sets, and invalid disk controls."""
from pathlib import Path
from itertools import combinations
import argparse
import json
import subprocess
import sys
from positive_core_completion_synthesis import triangulations, disk_check
from stream_catalog import sha

ROOT = Path(__file__).resolve().parent
assert __debug__


def rejects(action):
    try:
        action()
    except (AssertionError, IndexError, KeyError):
        return
    raise AssertionError("invalid disk or injection accepted")


def check_rods(system, faces, injection):
    B, N = system["B"], system["N"]
    assert len(injection) == system["G"]//2+1
    assert len(set(injection)) == len(injection)
    assert all(type(v) is int and 0 <= v < B+N+len(faces) for v in injection)
    assert injection[:B] == list(range(B))
    image_rods = {frozenset((injection[a], injection[b])) for a, b in system["edges"]}
    actual_rods = {frozenset((j, B+j)) for j in range(B)}
    actual_rods |= {frozenset((j, B+(j+1) % B)) for j in range(B)}
    for i, face in enumerate(faces):
        actual_rods.update(frozenset((B+N+i, B+v)) for v in face)
    assert len(image_rods) == 90 and image_rods <= actual_rods


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    args.output.mkdir(parents=True)
    reportpath = ROOT / "evidence/positive-core-completion-synthesis-resume2.json"
    report = json.loads(reportpath.read_text())
    assert report["verified"] and report["source_sha256"] == sha(ROOT / "positive_core_completion_synthesis.py")
    repeat = args.output / "REPEAT.json"
    subprocess.run([sys.executable, str(ROOT / "positive_core_completion_synthesis.py"),
                    "--output", str(repeat)], cwd=ROOT, check=True, capture_output=True)
    assert sha(repeat) == sha(reportpath)
    region_controls = []
    for B, expected in ((3, 1), (4, 5), (5, 21)):
        sets = triangulations(tuple(range(B)), (B,))
        assert len(sets) == expected
        assert all(disk_check(B+1, B, faces) for faces in sets)
        region_controls.append({"B": B, "interior_vertices": 1, "simple_disk_sets": len(sets)})
    systempath = ROOT.parent / "evidence/n24/core-system.json"
    system = json.loads(systempath.read_text())
    completions = report["n24"]["completions"]
    injections = report["n24"]["core_point_to_full_auxiliary_point_injections"]
    assert len(completions) == len(injections) == 51
    active = {tuple(sorted(f)) for f in system["active_faces"]}
    for faces, injection in zip(completions, injections, strict=True):
        assert active <= {tuple(f) for f in faces}
        assert disk_check(24, 15, {tuple(f) for f in faces})
        check_rods(system, faces, injection)
    faces = completions[0]
    injection = injections[0]
    negatives = []
    rejects(lambda: disk_check(24, 15, {tuple(f) for f in faces[:-1]}))
    negatives.append("missing-face")
    rejects(lambda: disk_check(24, 14, {tuple(f) for f in faces}))
    negatives.append("wrong-boundary-size")
    badfaces = [list(f) for f in faces]
    badfaces[0] = [0, 0, 1]
    rejects(lambda: disk_check(24, 15, {tuple(f) for f in badfaces}))
    negatives.append("repeated-triangle-vertex")
    badmap = list(injection)
    badmap[0], badmap[1] = badmap[1], badmap[0]
    rejects(lambda: check_rods(system, faces, badmap))
    negatives.append("wrong-anchor-order")
    badmap = list(injection)
    badmap[-1] = badmap[-2]
    rejects(lambda: check_rods(system, faces, badmap))
    negatives.append("noninjective-witnesses")
    result = {"verified": True, "fresh_repeat_byte_identical": True,
              "region_complete_set_controls": region_controls,
              "all_51_full_disk_and_90_rod_injections_independently_checked": True,
              "negative_controls_rejected": negatives,
              "synthesis_report_sha256": sha(reportpath),
              "synthesis_source_sha256": sha(ROOT / "positive_core_completion_synthesis.py"),
              "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
              "scope": "constructive completion/rod-transport controls, not all competing families"}
    with (args.output / "VERIFIED.json").open("x", encoding="utf8") as stream:
        json.dump(result, stream, indent=2)
    print("Positive-core completion controls PASS: byte-identical repeat, 51 disk/rod injections;",
          len(negatives), "bad graphs/maps rejected", flush=True)


if __name__ == "__main__":
    main()
