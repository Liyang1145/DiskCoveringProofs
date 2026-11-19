# SPDX-License-Identifier: MIT
"""Fail-closed adapter from supported exact orders to freshly executed proofs."""
from fractions import Fraction
import hashlib
import json
from math import isqrt
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from urllib.error import URLError
from urllib.request import HTTPRedirectHandler, Request, build_opener

ROOT = Path(__file__).resolve().parents[1]
PIN = "089584973f41e6374ce110f6e5b5ee456df19352"
BASE = f"https://raw.githubusercontent.com/VonEquinox/DiskCoveringSolve/{PIN}"
MAX_INPUT = 64 * 1024 * 1024
MAX_RESULT = 32 * 1024 * 1024
COMMANDS = {
    13: ("tools/check_native_n13_global.py", "exact_global"),
    16: ("verification/n16/replay_global.py", "exact_global_proof_replayed"),
    17: ("verification/n17/check_global.py", "exact_global_optimality_native_checked"),
    18: ("verification/n18/replay_global.py", "exact_global_proof_replayed"),
    19: ("verification/n19/replay_global.py", "exact_global_proof_replayed"),
}
# Paths relative to the immutable source commit, plus expected SHA-256.
FILES = {
    16: (
        ("core/root16.json", "a89dfe7e356a670176622e0726a0e7d27f14136e5e1d79326f9afedac285ab9e"),
        ("core/candidate16_tree.json.gz", "3fa2a55f460b35678ad92f977e2c0bae52c0b1e8ad6fc27957835d87f362fb31"),
    ),
    17: (
        ("core/root17.json", "f520c34816aab807fd115933a1159151ec7e71e4b8fb3b9b9d85d7c554050ac2"),
        ("core/candidate17_tree.json.gz", "a0b2b799879f290898c6d3d15dcf745611f99cf1ff5e9f05e8ea147ec403e3e9"),
    ),
    18: (
        ("core/root18.json", "446d47409d67bd6d6d2af39813b6c4b974f29d896ea8b25f7ec15bf78dd13c34"),
        ("core/candidate18_tree.json.gz", "b0b5add76b82c2682e8447d7721860524fcaafe158de1181fc71ffa1472a3c2b"),
    ),
}
LOCAL_ROOT13 = (
    "verification/n13/candidate_midpoint.json",
    "00bd9e1b2ea0364ea586efe8c92b77f89f5f3664335cccc2b2a4b7b5433478e1",
)
ROOT_LAYOUT = {13: (10, 62, 119), 16: (12, 74, 140),
               17: (12, 82, 157), 18: (12, 90, 174)}

class ReplayError(RuntimeError):
    """The requested exact replay was unavailable or did not verify."""


class _NoRedirect(HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs):
        return None


def supports_replay(n):
    return type(n) is int and n in COMMANDS


def _status(message):
    print(message, file=sys.stderr, flush=True)


def _copy_pinned(src, dest, expected):
    """Check exact bytes in a fresh per-run destination while copying."""
    check = hashlib.sha256()
    size = 0
    while chunk := src.read(1 << 20):
        size += len(chunk)
        if size > MAX_INPUT:
            raise ReplayError("pinned input exceeds its size limit")
        dest.write(chunk)
        check.update(chunk)
    if check.hexdigest() != expected:
        raise ReplayError("pinned input SHA-256 mismatch")


def _download(url, expected, cache):
    stage = None
    try:
        req = Request(url, headers={"User-Agent": "DiskCoveringProofs exact replay"})
        opener = build_opener(_NoRedirect)
        _status(f"Downloading pinned proof input: {cache.name}")
        with opener.open(req, timeout=30) as source:
            with tempfile.NamedTemporaryFile(dir=cache.parent, prefix=".proof-data-", delete=False) as out:
                stage = Path(out.name)
                _copy_pinned(source, out, expected)
        stage.replace(cache)
    except (OSError, URLError, ReplayError) as exc:
        raise ReplayError(f"could not obtain verified proof input {cache.name}: {exc}") from exc
    finally:
        if stage is not None:
            stage.unlink(missing_ok=True)


def _stage_local(path, destination, expected):
    if path.is_symlink() or not path.is_file():
        raise ReplayError(f"missing regular proof input: {path}")
    try:
        with path.open("rb") as source, destination.open("wb") as dest:
            _copy_pinned(source, dest, expected)
    except (OSError, ReplayError) as exc:
        destination.unlink(missing_ok=True)
        raise ReplayError(f"invalid proof input {path}: {exc}") from exc


def _stage_inputs(n, data_dir, offline, stage):
    if n not in FILES:
        return []
    cache = Path(data_dir) if data_dir is not None else ROOT/"build"/"proof-data"
    if not offline:
        cache.mkdir(parents=True, exist_ok=True)
    results = []
    for rel, expected in FILES[n]:
        name = Path(rel).name
        local, dest = cache/name, stage/name
        try:
            _stage_local(local, dest, expected)
        except ReplayError:
            if offline:
                raise
            if local.is_symlink():
                raise ReplayError(f"refusing to replace symlink: {local}")
            _download(f"{BASE}/cover{n}/proof_bundle/{rel}", expected, local)
            _stage_local(local, dest, expected)
        results.append(dest)
    return results


def _execute(command):
    """Route progress from trusted local scripts to stderr; return final object."""
    env = dict(os.environ)
    env.pop("PYTHONOPTIMIZE", None)
    env.pop("PYTHONPATH", None)
    env["PYTHONPATH"] = str(ROOT/"tools")
    final = []
    size = 0
    # Top-level pretty-printed reports begin with an unindented '{'.
    # A new top-level JSON object replaces any earlier child report.
    with subprocess.Popen(command, cwd=ROOT, env=env, stdout=subprocess.PIPE,
                          text=True, encoding="utf-8", errors="strict") as process:
        try:
            for line in process.stdout:
                stripped = line.strip()
                if line.startswith("{"):
                    final = [line]
                    size = len(line)
                elif final and not final[-1].startswith("}"):
                    final.append(line)
                    size += len(line)
                elif stripped:
                    final = []
                    size = 0
                if size > MAX_RESULT:
                    raise ReplayError("verifier JSON exceeds its output limit")
                # Do not send large JSON metadata copies to the progress stream.
                if not final and stripped:
                    _status(line.rstrip("\n"))
        except BaseException:
            process.kill()
            raise
        if process.wait() != 0:
            raise ReplayError(f"verifier exited with status {process.returncode}: {command[3]}")
    try:
        report = json.loads("".join(final))
    except (TypeError, ValueError) as exc:
        raise ReplayError("verifier did not produce a final JSON report") from exc
    if not isinstance(report, dict):
        raise ReplayError("verifier report is not an object")
    return report


def _root_descriptor(n, path):
    B, radius_index, dimension = ROOT_LAYOUT[n]
    data = json.loads(path.read_text(encoding="utf-8"))
    scale = int(data["Qx"])
    x = [Fraction(int(t), scale) for t in data["xnum"]]
    if n == 13:
        width = Fraction(int(data["rho_num"]), int(data["rho_den"]))
    elif n == 16:
        width = Fraction(data["rho"])
    else:
        # These runners verify a contraction on this tighter root box.
        width = Fraction(1, 10**80)
    if scale <= 0 or len(x) != dimension or width <= 0:
        raise ReplayError("invalid verified root descriptor")
    t = x[radius_index]
    if t <= width:
        raise ReplayError("invalid verified squared radius isolation")
    indices = [[2*(B+i-1),2*(B+i-1)+1] for i in range(n)]
    return {
        "kind": "unique_real_root_in_rational_box",
        "variable_count": dimension,
        "radius_squared_coordinate": radius_index,
        "index_base": 0,
        "radius_squared_interval": [str(t-width), str(t+width)],
        "midpoint": [str(v) for v in x],
        "box_half_width": str(width),
        "equations": {
            13: "tools/check_native_n13_root.py:equations",
            16: "tools/verify_native_n16_attainment.py:equations",
            17: "tools/check_native_n17_root.py:equations",
            18: "tools/diskcover_n18_algebraic.py:equations",
        }[n],
        "center_coordinate_indices": indices,
    }


def _outward_radius(lo, hi, places=58):
    """Strict decimal bounds, enclosing the entire exact squared-root box."""
    s = 10**places
    a,b = (isqrt((t*s*s).numerator//(t*s*s).denominator) for t in (lo,hi))
    if Fraction(a*a,s*s)==lo:
        a-=1
    b+=1
    return [f"{k//s}.{k%s:0{places}d}" for k in (a,b)]


def _result(n, report, root):
    # Use a specific status for each bundled verifier, never an archived claim.
    if type(report.get("n")) is not int or report["n"] != n or report.get("status") != COMMANDS[n][1]:
        raise ReplayError(f"verifier report did not certify the requested n={n} order/status")
    if n == 19:
        if report.get("radius_exact") != "1/sqrt(13)" or report.get("radius_squared") != "1/13":
            raise ReplayError("verified n=19 exact radius differs")
        from diskcover_n19_upper import check_n19_upper
        disk = check_n19_upper()
        return {
            "n": n, "status": "exact_global", "radius_exact": "1/sqrt(13)",
            "radius_squared": "1/13",
            "centers": [[f"sqrt(3/13)*({x})",f"({y})/sqrt(13)"] for x,y in disk["weighted_centers"]],
            "replay": {"fresh": True,"verifier": COMMANDS[n][0],
                       "verifier_status": report["status"]},
        }
    d = _root_descriptor(n, root)
    lo,hi = map(Fraction,d["radius_squared_interval"])
    display = {
        13: report.get("radius_decimal_interval"),
        16: _outward_radius(lo,hi),
        17: report.get("strict_radius_bracket"),
        18: report.get("strict_radius_interval"),
    }[n]
    if (not isinstance(display, list) or len(display) != 2 or
            not all(isinstance(x,str) for x in display)):
        raise ReplayError("missing strict radius interval from proof")
    a,b = map(Fraction, display)
    if not (0 < a < b and a*a < lo <= hi < b*b):
        raise ReplayError("verified display interval does not enclose the exact root box")
    return {
        "n": n, "status": "exact_global",
        "radius_exact": f"sqrt(x[{d['radius_squared_coordinate']}])",
        "radius_decimal_interval": display,
        "root": d,
        "centers": [[f"x[{i}]",f"x[{j}]"] for i,j in d["center_coordinate_indices"]],
        "replay": {"fresh": True,"verifier": COMMANDS[n][0],
                   "verifier_status": report["status"]},
    }


def solve_replayed(n, data_dir=None, offline=False, workers=4):
    """Run a native exact verifier, or raise ReplayError without a verdict.

    Creates only SHA-256-checked numeric data under cache. Artifacts can
    also be provisioned in that directory beforehand for network-free use.
    Progress is stderr only; caller serializes the returned result.
    """
    if not supports_replay(n):
        raise ReplayError("fresh exact replay is supported only for n=13,16,17,18,19")
    if type(workers) is not int or not 1 <= workers <= 6:
        raise ReplayError("workers must be an integer in 1..6")
    try:
        with tempfile.TemporaryDirectory(prefix=f"diskcover-{n}-") as d:
            stage = Path(d)
            inputs = _stage_inputs(n, data_dir, offline, stage)
            root = inputs[0] if inputs else None
            if n == 13:
                rel, digest = LOCAL_ROOT13
                root = stage/"root13-midpoint.json"
                _stage_local(ROOT/rel, root, digest)
            command = [sys.executable, "-B", "-u", str(ROOT/COMMANDS[n][0]), *map(str,inputs)]
            if n in (18,19):
                command.extend(("--workers",str(workers)))
            _status(f"Replaying exact proof for n={n}")
            result = _result(n,_execute(command),root)
            result["replay"]["offline"] = bool(offline)
            result["replay"]["pinned_input_sha256"] = {
                Path(rel).name: sha for rel,sha in FILES.get(n,())
            }
            if n == 13:
                rel,digest = LOCAL_ROOT13
                result["replay"]["pinned_input_sha256"][Path(rel).name] = digest
            return result
    except (OSError, ValueError, TypeError, KeyError, ArithmeticError) as exc:
        raise ReplayError(f"exact replay failed for n={n}: {exc}") from exc
