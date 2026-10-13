"""Keep all recursion/guards/canonicalization; substitute a stronger angle gate."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    original = ROOT / "peel_sparse_outer_collar.cpp"
    target = ROOT / "peel_eight_rod_collar.cpp"
    reportpath = ROOT / "eight-rod-collar-source-derivation.json"
    assert not target.exists() and not reportpath.exists()
    old = original.read_text(encoding="utf8")
    changes = [
        ("#define visit frozen_degree_visit\n",
         "#define visit frozen_degree_visit\n#define possible frozen_three_cap_possible\n"),
        ('#undef main\n#include "../round3-high/paid_outer_matcher.inc"',
         '#undef main\n#undef possible\n#include "eight_rod_possible.inc"\n#include "../round3-high/paid_outer_matcher.inc"'),
        ('if(argc!=12)throw runtime_error("usage: sparse-collar N B output scale cap2 cap4 cap6 node-limit mode exact-table-or-minus sparse-table-or-minus");',
         'if(argc!=13)throw runtime_error("usage: eight-rod-collar N B output scale cap2 cap4 cap6 node-limit mode exact-table-or-minus sparse-table-or-minus cap8");'),
        ('string mode=argv[9];audit_order=',
         'cap8=stoll(argv[12]);string mode=argv[9];audit_order='),
        ('if(n>MAXN||b<3||n<b||scale<=0||scale>100000000||caps[0]<=0||caps[2]>=scale/2)',
         'if(n>MAXN||b<3||n<b||scale<=0||scale>100000000||caps[0]<=0||caps[2]>=cap8||cap8>=scale/2)'),
        ('COLLAR NATIVE PID=', 'EIGHT ROD NATIVE PID='),
        ('<<",\\"weak_graph_count\\":"<<collars.size();',
         '<<",\\"cap8\\":"<<cap8<<",\\"eight_rod_screen\\":"<<(screen?"true":"false")\n    <<",\\"weak_graph_count\\":"<<collars.size();'),
    ]
    new = old
    for before, after in changes:
        assert new.count(before) == 1
        new = new.replace(before, after, 1)
    reconstructed = new
    for before, after in reversed(changes):
        assert reconstructed.count(after) == 1
        reconstructed = reconstructed.replace(after, before, 1)
    assert reconstructed == old
    target.write_text(new, encoding="utf8", newline="\n")
    reportpath.write_text(json.dumps({
        "verified_mechanical_derivation": True, "original_source_sha256": sha(original),
        "derived_source_sha256": sha(target), "extra_angle_gate_sha256": sha(ROOT / "eight_rod_possible.inc"),
        "changes": changes, "recursive_body_and_omission_unchanged": True,
        "sparse_guard_and_canonicalization_unchanged": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")


if __name__ == "__main__":
    main()
