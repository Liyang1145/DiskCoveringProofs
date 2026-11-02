#!/usr/bin/env python3
"""Static import-closure audit for the restored C450 completion modules.

Deterministic, read-only, bounded.  Resolves every `import N11Formalization.X`
reachable from the three lane-A C450 targets to a real `.lean` file and reports
any missing module.  A missing import turns the CI target red even though the
proof text is fine, so this is the cheapest pre-CI dependency gate.

Scope: static N11Formalization import graph only.  NOT a kernel verdict.
"""
import hashlib, json, os, re

ROOT = os.path.join("n11-work", "lean", "N11Formalization")
ROOTS = ["C450ChainCompletion", "C450ChainCompletionMain", "C450ChainCompletionAudit"]
IMPORT_RE = re.compile(r"^import\s+N11Formalization\.([A-Za-z0-9_]+)\s*$")


def imports_of(name):
    path = os.path.join(ROOT, name + ".lean")
    if not os.path.exists(path):
        return None
    found = []
    with open(path, encoding="utf-8", errors="replace") as fh:
        for line in fh:
            m = IMPORT_RE.match(line.strip())
            if m:
                found.append(m.group(1))
    return found


def main():
    seen, missing, stack = {}, [], list(ROOTS)
    while stack:
        name = stack.pop()
        if name in seen:
            continue
        imp = imports_of(name)
        if imp is None:
            seen[name] = "MISSING"
            missing.append(name)
        else:
            seen[name] = "ok"
            stack.extend(imp)
    report = {
        "roots": ROOTS,
        "closure_size": len(seen),
        "missing": sorted(missing),
        "verdict": "PASS" if not missing else "FAIL",
        "scope": "static N11Formalization import closure; NOT a kernel verdict",
    }
    text = json.dumps(report, indent=2, sort_keys=True) + "\n"
    out = os.path.join("n11-work", "ops", "lanes", "A", "c450-import-closure.json")
    with open(out, "w") as fh:
        fh.write(text)
    print(text)
    print("report sha256", hashlib.sha256(text.encode()).hexdigest())


if __name__ == "__main__":
    main()
