"""Proposal: replace three weak contacts by exactly zero stress multipliers."""

import argparse
from copy import deepcopy
import hashlib
import json
from pathlib import Path

import mpmath as mp
import sympy as sp


WORK = Path(__file__).resolve().parent
WEAK = (0, 5, 7)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    folder = WORK.parent / "outputs/n26-same-root-cover-v2"
    old_path, old_root_path = folder / "SYSTEM.json", folder / "ROOT-CERTIFICATE.json"
    old = json.loads(old_path.read_text())
    old_root = json.loads(old_root_path.read_text())
    system = deepcopy(old)
    for i in WEAK:
        powers = [0] * 26
        powers[14 + i] = 1
        system["equations"][i] = [{"powers": powers, "coefficient": "1"}]
    system["schema"] = "N26-D2-zero-weak-stress-root-system-v1"
    system["original_system_sha256"] = sha(old_path)
    system["zero_stress_contact_indices"] = list(WEAK)
    system["local_optimality_proved"] = False
    variables = sp.symbols(" ".join(system["variables"]))
    expressions = sp.Matrix([
        sum(int(term["coefficient"]) * sp.prod(v**k for v, k in zip(variables, term["powers"]))
            for term in polynomial) for polynomial in system["equations"]])
    jacobian = expressions.jacobian(variables)
    func = sp.lambdify(variables, expressions, "mpmath", cse=True)
    jfunc = sp.lambdify(variables, jacobian, "mpmath", cse=True)
    mp.mp.dps = 140
    z = mp.matrix([mp.mpf(int(n)) / mp.mpf(int(old_root["Qx"])) for n in old_root["xnum"]])
    for iteration in range(12):
        residual = func(*z)
        if max(map(abs, residual)) < mp.mpf("1e-125"):
            break
        z -= mp.lu_solve(jfunc(*z), residual)
    if max(map(abs, func(*z))) > mp.mpf("1e-120"):
        raise ValueError("modified root proposal did not converge")
    inverse = jfunc(*z) ** -1
    qx, qy = 10**110, 10**100
    args.output.mkdir(parents=True)
    path = args.output / "SYSTEM.json"
    path.write_text(json.dumps(system, indent=2) + "\n", encoding="utf-8")
    certificate = {
        "schema": "N26-zero-weak-stress-root-proposal-v1",
        "system_sha256": sha(path), "Qx": str(qx), "Qy": str(qy),
        "xnum": [str(int(mp.nint(v * qx))) for v in z],
        "Ynum": [[str(int(mp.nint(inverse[i, j] * qy))) for j in range(26)] for i in range(26)],
        "original_system_sha256": sha(old_path),
        "original_root_certificate_sha256": sha(old_root_path),
        "builder_sha256": sha(__file__),
        "verified": False, "local_optimality_proved": False, "global_optimality_proved": False}
    (args.output / "ROOT-PROPOSAL.json").write_text(json.dumps(certificate, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"built": True, "verified": False, "zero_stress_indices": list(WEAK),
                      "proposed_radius": mp.nstr(mp.sqrt(z[13]), 70)}), flush=True)


if __name__ == "__main__":
    main()
