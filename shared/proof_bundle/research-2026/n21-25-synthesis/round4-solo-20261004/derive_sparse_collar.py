"""Mechanical new-source derivation; original collar and frozen kernels unchanged."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent
source = ROOT / "peel_outer_collar.cpp"
output = ROOT / "peel_sparse_outer_collar.cpp"
assert not output.exists()
text = source.read_text(encoding="utf8")
changes = [
    ('#include "../round3-high/paid_outer_matcher.inc"\n',
     '#include "../round3-high/paid_outer_matcher.inc"\n#include "sparse_outer_matcher.inc"\n'),
    (' if(already_paid(s))return;\n',
     ' if(already_sparse_paid(s))return;\n if(already_paid(s))return;\n'),
    (' if(argc!=11)throw runtime_error("usage: collar N B output scale cap2 cap4 cap6 node-limit mode paid-table-or-minus");',
     ' if(argc!=12)throw runtime_error("usage: sparse-collar N B output scale cap2 cap4 cap6 node-limit mode exact-table-or-minus sparse-table-or-minus");'),
    (' load_obstacles(argv[10]);\n',
     ' load_obstacles(argv[10]);\n load_sparse_obstacles(argv[11]);\n'),
    (' write_paid_summary(out);\n',
     ' write_paid_summary(out);\n write_sparse_summary(out);\n'),
    ('<<" proof_prunes="<<proof_prunes<<" seconds="',
     '<<" proof_prunes="<<proof_prunes<<" sparse_prunes="<<sparse_prunes<<" seconds="'),
    ('<<" proof_prunes="<<proof_prunes<<"\\n";',
     '<<" proof_prunes="<<proof_prunes<<" sparse_prunes="<<sparse_prunes<<"\\n";'),
]
for old, new in changes:
    assert text.count(old) == 1, old
    text = text.replace(old, new, 1)
output.write_text(text, encoding="utf8", newline="\n")
report = {
    "mechanical_derivation_only": True,
    "base_source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
    "derived_source_sha256": hashlib.sha256(output.read_bytes()).hexdigest(),
    "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    "changes": changes,
    "all_original_recursion_and_omission_code_unchanged": True,
    "new_guard_requires_independent_source_argument_and_controls": True,
    "global_optimality_proved": False,
}
(ROOT / "sparse-collar-source-derivation.json").write_text(json.dumps(report, indent=2), encoding="utf8")
print("New sparse collar mechanically derived; original source unchanged")
