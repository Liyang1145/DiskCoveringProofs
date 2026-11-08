"""Fail-closed diagnostic for the archived n=26 midarc interface.

This is NOT a mathematical verifier.  It never accepts a global theorem:
the geometric replay adapter is not implemented and its inputs are missing.
"""
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import argparse
import json
import sys

FINAL_SCHEMA = 'N26-independent-midarc-source-current-final-rehash-v1'
CURRENT_SCHEMA = 'N26-complete-current-with-midarc-source-geometry-audit-v1'
FINAL_SHA = '6099c25ff78f074c5a02dd90c33c2d3f481df350ea71b2e853ca9fc2deeabbbc'
CURRENT_SHA = 'ba52dbb56f9d273c30e1b356c55bdb0d3ff8fdaa36061248e5c8ec1e490a81a1'
SCOPE = 'at-most-same-root-Rstar-not-original-U'
INTERVAL = [
 '0.234700090400448239616790133776692127560495963654971391785924',
 '0.234700090400448239616790133776692127560495963654971391785925',
]


def digest(data):
    return sha256(data).hexdigest()


def read_json(path, expected, problems):
    if path is None:
        problems.append('missing input: '+expected)
        return None, None
    try:
        raw = path.read_bytes()
        data = json.loads(raw)
        if not isinstance(data, dict):
            raise ValueError('expected JSON object')
        return data, digest(raw)
    except (OSError, ValueError, UnicodeError) as exc:
        problems.append('unreadable input '+expected+': '+str(exc))
        return None, None


def check(final, current):
    """Return interface failures only; inputs are untrusted dictionaries."""
    issues = []
    if final is None:
        issues.append('formal final unavailable')
    else:
        if final.get('schema') != FINAL_SCHEMA:
            issues.append('wrong final schema')
        if final.get('current_audit_sha256') != CURRENT_SHA:
            issues.append('final does not bind native current SHA')
        if final.get('radius_scope') != SCOPE:
            issues.append('wrong radius scope: same-root cannot be promoted to original U')
        if final.get('r_strict_interval') != INTERVAL:
            issues.append('final radius interval differs from pinned native candidate')
        for key in ('candidate_angle_unresolved_closed_boxes',
                    'Rstar_conditional_frontier_pending_subtrees'):
            value = final.get(key)
            if type(value) is not int or value != 0:
                issues.append('nonzero or missing unresolved field: '+key)
        for key in ('unrestricted_reduction_final_joint_acceptance',
                    'full_catalog_complete', 'global_lower_bound_proved',
                    'global_optimality_proved'):
            if final.get(key) is not True:
                issues.append('missing global obligation: '+key)
        fam = final.get('Rstar_conditional_frontier_families')
        if not isinstance(fam, list) or not fam:
            issues.append('missing formal family accounting')
        else:
            for f in fam:
                if not isinstance(f, dict) or f.get('family_exhausted') is not True or f.get('pending_subtrees') != 0 or f.get('unresolved_terminal_subtrees') != 0:
                    issues.append('unclosed or malformed formal family')
                    break
    if current is None:
        issues.append('formal current unavailable')
    else:
        if current.get('schema') != CURRENT_SCHEMA:
            issues.append('wrong current schema')
        if current.get('r_strict_interval') != INTERVAL:
            issues.append('current radius interval differs from pinned native candidate')
        if current.get('radius_scope') != SCOPE:
            issues.append('current radius scope mismatch')
        if final is not None and current.get('r_strict_interval') != final.get('r_strict_interval'):
            issues.append('current and final radius intervals differ')
        if not isinstance(current.get('files'), dict) or not current['files']:
            issues.append('missing current files map')
    try:
        if not Fraction(INTERVAL[0]) < Fraction(INTERVAL[1]):
            issues.append('invalid pinned radius interval')
    except ValueError:
        issues.append('invalid pinned radius interval')
    # Intentionally unconditional until a mathematically meaningful adapter is implemented.
    issues.append('unimplemented fresh geometric/continuous-domain replay and global composition')
    return issues


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--formal-final', type=Path, required=True)
    parser.add_argument('--formal-current', type=Path, required=True)
    args = parser.parse_args()
    issues = []
    final, fhash = read_json(args.formal_final, 'formal final', issues)
    current, chash = read_json(args.formal_current, 'formal current', issues)
    if fhash is not None and fhash != FINAL_SHA:
        issues.append('formal final byte hash mismatch')
    if chash is not None and chash != CURRENT_SHA:
        issues.append('formal current byte hash mismatch')
    issues.extend(check(final, current))
    print(json.dumps({'accepted': False, 'math_replayed': False,
                      'final_sha256': fhash, 'current_sha256': chash,
                      'failures': issues}, indent=2))
    return 2


if __name__ == '__main__':
    sys.exit(main())
