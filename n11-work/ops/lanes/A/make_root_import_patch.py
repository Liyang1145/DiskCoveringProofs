#!/usr/bin/env python3
"""Lane A session 191/part4: emit + validate the supervisor's root-import patch.

Reads the frozen stage-1 root, replaces the two `-- HARK-MISSING` comment
lines with live imports, writes a unified diff beside this script, and
validates the diff with `git apply --check` (no tree mutation).

Scope: SOURCE / patch-applicability only -- NOT a kernel verdict.
"""
import difflib, hashlib, json, os, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..'))
REL = 'n11-work/lean/N11Formalization.lean'
ROOT = os.path.join(REPO, REL)


def sha(p):
    with open(p, 'rb') as f:
        return hashlib.sha256(f.read()).hexdigest()


with open(ROOT, encoding='utf-8', newline='') as f:
    lines = f.readlines()

report = {'scope': 'STATIC patch-applicability audit; NOT a kernel verdict',
          'root': REL, 'root_sha256': sha(ROOT)}

pairs = []
new = []
for i, ln in enumerate(lines):
    if ln.startswith('-- HARK-MISSING') and ': import ' in ln:
        mod = ln.split(': import ', 1)[1].strip()
        pairs.append((i + 1, mod))
        new.append('import ' + mod + '\n')
    else:
        new.append(ln)
report['hark_lines'] = pairs
report['expected'] = [(1952, 'N11Formalization.C450ChainCompletion'),
                      (1953, 'N11Formalization.C450ChainCompletionMain')]
report['hark_matches_expected'] = (pairs == report['expected'])

diff = difflib.unified_diff(lines, new, fromfile='a/' + REL, tofile='b/' + REL,
                            n=3)
patch = ''.join(diff)
patch_path = os.path.join(HERE, 'root-import-c450.patch')
with open(patch_path, 'w', encoding='utf-8', newline='') as f:
    f.write(patch)
report['patch'] = os.path.relpath(patch_path, REPO)
report['patch_sha256'] = sha(patch_path)

# Validate FORWARD applicability to the current (unpatched) root.  `--reverse`
# is the wrong direction: it checks the patch's *new* side against a tree that
# still holds the *old* side, so it can never succeed before the edit.
chk = subprocess.run(['git', 'apply', '--check', patch_path],
                     cwd=REPO, capture_output=True, text=True)
report['git_apply_check_forward_rc'] = chk.returncode
report['git_apply_check_forward_err'] = chk.stderr.strip()

# Resulting-content checks on the intended patched bytes (`new`).
report['patched_has_crlf'] = any('\r' in l for l in new)
report['patched_imports_live'] = (
    sum(1 for l in new if l == 'import N11Formalization.C450ChainCompletion\n') == 1
    and sum(1 for l in new if l == 'import N11Formalization.C450ChainCompletionMain\n') == 1)
report['patched_no_hark'] = not any('HARK-MISSING' in l for l in new)
report['import_count_before'] = sum(1 for l in lines if l.startswith('import '))
report['import_count_after'] = sum(1 for l in new if l.startswith('import '))
report['patched_matches_newline_style'] = (any(l.endswith('\r\n') for l in lines)
                                           == any(l.endswith('\r\n') for l in new))

ok = (report['hark_matches_expected'] and report['patched_no_hark']
      and chk.returncode == 0 and report['patched_imports_live']
      and not report['patched_has_crlf']
      and report['import_count_after'] == report['import_count_before'] + 2)
report['verdict'] = 'PASS_PATCH_READY' if ok else 'FAIL'
with open(os.path.join(HERE, 'c450-root-import-patch.json'), 'w', encoding='utf-8') as f:
    json.dump(report, f, indent=1, sort_keys=True)
print('VERDICT', report['verdict'])
print('git_apply_check_forward_rc', chk.returncode, chk.stderr.strip())
print('patch_sha256', report['patch_sha256'])
