"""cline2-coupled-factors R15: safe per-factor rerun interface for the 22 remaining
joint-patch factors under the CURRENT frozen coefficients.

WHAT THIS IS
  A thin driver that invokes the lead's OWN certifier
      lead/certify_joint_rest_tight.py            (interval kernel, dps=30, filter, budgets)
  but repoints its frozen-coefficient input from the INAPPLICABLE
      joint_patch_frozen_v2.json   (sha a856f2c12bcc24c428c2ac6044f81877...)
  to the CURRENT
      joint_nested_frozen.json     (sha 5671967c5a3df341b068975b161900c8b7...)
  and redirects its output records into a digest-keyed directory in THIS scope, so that
  records computed under different coefficients can never be mixed and the lead's
  directory is not written to.

HOW THE REPOINT IS DONE (no edits to lead files, no text-surgery on the kernel)
  `certify_joint_rest_tight.py` does two things we must respect:
     line 7:  frozen = P/'joint_patch_frozen_v2.json';  digest = sha256(frozen)
     line 8:  execs certify_q0_closure.py with the literal string
              "f'q0_closure_dual_{start}_{span}.json'" replaced by
              "'joint_patch_frozen_v2.json'"
  We therefore
     (1) temporarily create  <alias>/joint_patch_frozen_v2.json  with the EXACT BYTES of
         joint_nested_frozen.json (plus a copy of certify_q0_closure.py and
         q0_exact_closure_radius.py and the certified-object input), and
     (2) run the certifier unchanged with cwd = that alias directory.
  Both the digest and the embedded filename resolve to the new bytes, and the kernel,
  normalizations, indices and filters are the lead's originals, untouched.  The alias is
  removed afterwards (unless --keep-alias).

USAGE (run from the repo root)
  py -3 -B -X utf8 research-2026/team-current/cline2-coupled-factors/rerun_joint_22.py \
        --factors 0 3 4 ... 28 [--tolerance-scale 1.0] [--keep-alias] [--timeout 900]
  py -3 -B -X utf8 .../rerun_joint_22.py --preflight          # factors 11 + 14 only
  py -3 -B -X utf8 .../rerun_joint_22.py --aggregate          # sum existing records only

OUTPUT
  out/r15_<digest12>/joint_patch_bound_<i>.json   per-factor records (lead's own schema,
      each carrying coefficient_sha256 = the NEW digest)
  out/r15_<digest12>/summary.json                 per-factor table + explicit flags
  out/r15_<digest12>/summary.md                   human-readable, with the sum and the
      explicit statement of which factors are still missing
"""
import os, sys, json, math, shutil, hashlib, subprocess, argparse
from pathlib import Path

HERE = Path(__file__).parent
LEAD = HERE.parent / 'lead'
OUT = HERE / 'out'
CANONICAL = 'joint_nested_frozen.json'          # current frozen coefficients
STALE = 'joint_patch_frozen_v2.json'            # name the certifier hardcodes
CERT = 'certify_joint_rest_tight.py'
SKIP_IN_CERT = [1, 2, 12, 13, 21, 22, 23]       # covered by the C854 local Q0 ridge proof
# ALL 29 indices exactly as the kernel builds them (verified by audit_factor_list.py
# against lead/certify_q0_closure.py:  0..10 face0..face10,  11..19 switch0..switch8,
# 20..28 ring0..ring8):
ALL = list(range(29))
TO_PROCESS = [i for i in ALL if i not in SKIP_IN_CERT]
# The 22 targets are EXACTLY the complement of the C854 skip list: 29 - 7 = 22.  No factor
# may be dropped, and in particular factor 0 (face0) MUST be included.  An earlier revision
# of this file wrongly excluded factor 0 with an unsupported "has its own proof" note; that
# exclusion is withdrawn.
R15_22 = list(TO_PROCESS)
assert len(R15_22) == 22, (len(R15_22), R15_22)
assert 0 in R15_22 and not (set(R15_22) & set(SKIP_IN_CERT))

FACTOR_NAMES = {0: 'face0', 3: 'face3', 4: 'face4', 5: 'face5', 6: 'face6', 7: 'face7',
                8: 'face8', 9: 'face9', 10: 'face10', 11: 'switch0', 14: 'switch3',
                15: 'switch4', 16: 'switch5', 17: 'switch6', 18: 'switch7',
                19: 'switch8', 20: 'ring0', 24: 'ring4', 25: 'ring5', 26: 'ring6',
                27: 'ring7', 28: 'ring8'}


def digest_of(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def verify_exec_chain(canonical_path, alias_dir):
    """Pre-launch audit requested by the lead.  Proves, by construction and byte-hash, that
    the kernel executed inside the alias resolves its coefficient path to the NEW bytes.

    How the two exec layers set up paths (read off the sources, then checked here):
      * certify_joint_rest_tight.py:7  P = Path(__file__).parent  -> the alias dir, because
        the certifier is INVOKED with cwd=alias_dir and as ./certify_joint_rest_tight.py.
      * :8  ns={'__file__': str(P/'certify_q0_closure.py')}  -> also the alias dir.
      * the kernel line 7 then does P = Path(__file__).parent and reads
        P/'joint_patch_frozen_v2.json'   -> the alias copy, i.e. the NEW bytes.
      * the kernel additionally reads a sibling q0_graphs.json via the SAME __file__ parent
        (alias copy, byte-identical to the lead's) and 'n11/upper/certified_object.json'
        relative to cwd (alias copy, byte-identical to the repo-root original).
    So the audit is: every path in that chain must exist, and every copied file must be
    byte-identical to its source.
    """
    ok = True
    rows = []
    chain = [
        (alias_dir / CERT, LEAD / CERT, 'exec layer 1: certifier (__file__ parent = alias)'),
        (alias_dir / 'certify_q0_closure.py', LEAD / 'certify_q0_closure.py',
         'kernel source exec\'d by the certifier'),
        (alias_dir / STALE, Path(canonical_path), 'COEFFICIENTS the kernel line 7 reads'),
        (alias_dir / 'q0_graphs.json', LEAD / 'q0_graphs.json',
         'faces read by the kernel via its own __file__ parent'),
        (alias_dir / 'q0_exact_closure_radius.py', LEAD / 'q0_exact_closure_radius.py',
         'prep code exec\'d by the kernel'),
        (alias_dir / 'n11' / 'upper' / 'certified_object.json',
         Path.cwd() / 'n11' / 'upper' / 'certified_object.json',
         'repo-relative input read at kernel exec (cwd)'),
    ]
    for dst, src, what in chain:
        if not dst.exists():
            rows.append((what, 'MISSING', None, None)); ok = False; continue
        hd = hashlib.sha256(dst.read_bytes()).hexdigest()
        hs = hashlib.sha256(src.read_bytes()).hexdigest() if src.exists() else None
        same = (hs == hd)
        if not same and what.startswith('COEFFICIENTS'):
            # the coefficient file is INTENTIONALLY different in name/provenance: the alias
            # holds the canonical bytes under the stale name.  It must equal the canonical.
            same = (hd == hashlib.sha256(Path(canonical_path).read_bytes()).hexdigest())
        ok &= bool(same)
        rows.append((what, 'byte-identical' if same else 'DIFFERS', hd[:16], hs[:16] if hs else None))
    print('--- pre-launch exec-chain audit ---')
    for what, verdict, hd, hs in rows:
        print(f'   {verdict:15s} {hd}  {what}')
    # strongest single check: does the kernel line-7 path hold the canonical bytes?
    kpath = alias_dir / STALE
    kdigest = hashlib.sha256(kpath.read_bytes()).hexdigest()
    print(f'   kernel coefficient path : {kpath}')
    print(f'   its sha256              : {kdigest}')
    print(f'   canonical sha256        : {hashlib.sha256(Path(canonical_path).read_bytes()).hexdigest()}')
    if kdigest != hashlib.sha256(Path(canonical_path).read_bytes()).hexdigest():
        ok = False
    print(f'   exec-chain audit verdict: {"PASS" if ok else "FAIL"}')
    assert ok, 'pre-launch exec-chain audit failed; refusing to launch'
    return ok, rows


def source_hashes(canonical_path):
    """Lead-requested source-hash capture at start: the frozen coefficients, the certifier,
    and the kernel (plus the prep module), all as read from the LEAD directory."""
    files = {CANONICAL: LEAD / CANONICAL,
             STALE + ' (stale name, current bytes used)': LEAD / CANONICAL,
             CERT: LEAD / CERT,
             'certify_q0_closure.py': LEAD / 'certify_q0_closure.py',
             'q0_exact_closure_radius.py': LEAD / 'q0_exact_closure_radius.py',
             'q0_graphs.json': LEAD / 'q0_graphs.json',
             'n11/upper/certified_object.json': Path.cwd() / 'n11' / 'upper' / 'certified_object.json'}
    out = {}
    for name, p in files.items():
        out[name] = hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None
    return out


def make_alias(canonical_path, alias_dir):
    """alias dir holding the new coefficient bytes under the stale filename, plus the
    support files the certifier execs (kernel + certified object input)."""
    alias_dir.mkdir(parents=True, exist_ok=True)
    (alias_dir / STALE).write_bytes(Path(canonical_path).read_bytes())
    support = ['certify_q0_closure.py', 'q0_exact_closure_radius.py',
               'q0_closure_dual_0_3.json', 'q0_graphs.json']
    for s in support:
        src = LEAD / s
        if src.exists():
            shutil.copy2(src, alias_dir / s)
    # the lead's exec line resolves 'n11/upper/certified_object.json' relative to cwd;
    # mirror the repo path so the kernel loads the same inputs it did in the lead's runs
    for rel in ['n11/upper']:
        d = alias_dir / rel
        d.mkdir(parents=True, exist_ok=True)
        src = Path.cwd() / rel / 'certified_object.json'
        if src.exists():
            shutil.copy2(src, d / 'certified_object.json')
    shutil.copy2(LEAD / CERT, alias_dir / CERT)


def run_factor(i, alias_dir, out_dir, timeout, tol_override=None):
    """invoke the lead's certifier for one factor index, cwd = alias_dir, then move the
    produced record into out_dir.  Returns the record dict (or None)."""
    env = dict(os.environ)
    env['PYTHONHASHSEED'] = '0'
    env['PYTHONUTF8'] = '1'
    args = ['py', '-3', '-B', '-X', 'utf8', CERT, str(i), str(i+1)]
    if tol_override is not None:
        args += [str(tol_override)]          # accepted only by the patched variant
    t0 = __import__('time').time()
    try:
        p = subprocess.run(args, cwd=alias_dir, env=env, capture_output=True,
                           text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return {'factor_index': i, 'factor': FACTOR_NAMES.get(i, '?'), 'error': 'timeout',
                'seconds': timeout}
    dt = __import__('time').time()-t0
    prod = alias_dir / f'joint_patch_tight_bound_{i:02d}.json'
    if not prod.exists():
        return {'factor_index': i, 'factor': FACTOR_NAMES.get(i, '?'),
                'error': 'no record produced', 'stdout_tail': p.stdout[-500:],
                'stderr_tail': p.stderr[-500:], 'seconds': dt}
    rec = json.loads(prod.read_text())
    shutil.move(str(prod), str(out_dir / prod.name))
    rec['wall_seconds'] = dt
    return rec


def aggregate(out_dir, digest):
    """read all records in out_dir and produce the sum + explicit coverage statement."""
    recs = {}
    for p in sorted(out_dir.glob('joint_patch_*bound_*.json')):
        r = json.loads(p.read_text())
        recs[r['factor_index']] = r
    rows = []
    for i in sorted(recs):
        r = recs[i]
        ok_digest = r.get('coefficient_sha256') == digest
        rows.append({'factor_index': i, 'factor': r.get('factor'),
                     'upper': r.get('upper'), 'lower_probe': r.get('lower_probe'),
                     'evaluations': r.get('evaluations'),
                     'budget_ended': r.get('budget_ended'),
                     'digest_ok': ok_digest})
    bad = [r['factor_index'] for r in rows if not r['digest_ok']]
    have = [r['factor_index'] for r in rows]
    missing = [i for i in R15_22 if i not in have]
    s = sum(r['upper'] for r in rows if r['upper'] is not None and r['digest_ok'])
    summary = {
        'frozen_coefficients': CANONICAL,
        'coefficient_sha256': digest,
        'certifier': f'lead/{CERT} (interval kernel lead/certify_q0_closure.py)',
        'skipped_covered_by_C854': SKIP_IN_CERT,
        'r15_22_targets': R15_22,
        'records_present': have,
        'records_missing': missing,
        'digest_mismatch_records': bad,
        'sum_of_present_uppers': s,
        'sum_covers_all_22': len(missing) == 0 and not bad,
        'source_hashes': source_hashes(LEAD / CANONICAL),
        'record_hashes': {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in sorted(out_dir.glob('joint_patch_*bound_*.json'))},
        'rows': rows,
    }
    (out_dir/'summary.json').write_text(json.dumps(summary, indent=1))
    L = [f'# R15 joint-patch factor bounds ({CANONICAL})',
         f'coefficient sha256 = `{digest}`',
         f'certifier = lead/{CERT} (kernel lead/certify_q0_closure.py, dps=30, C844 filter,'
         f' per-factor budgets)', '',
         f'sum of present uppers = **{s:.12f}**',
         f'all 22 present and digest-clean: **{summary["sum_covers_all_22"]}**',
         f'missing: {missing}', f'digest mismatches: {bad}', '',
         f'source hashes captured at launch: see summary.json `source_hashes`', '',
         '| fi | factor | upper | lower_probe | evals | budget_ended | digest_ok |',
         '|---|---|---|---|---|---|---|']
    for r in rows:
        L.append(f'| {r["factor_index"]} | {r["factor"]} | {r["upper"]!r} | '
                 f'{r["lower_probe"]!r} | {r["evaluations"]} | {r["budget_ended"]} | '
                 f'{r["digest_ok"]} |')
    L += ['', 'SCOPE.  These are the 22 remaining patch factors under the CURRENT frozen',
          'coefficients.  They are NOT a bound on the patch or the global objective, and the',
          'Q0 complement is NOT claimed covered.  The two separate quantities are:',
          '  * LOCAL patch (Q0 ridge box only, conditional): 28.10439974622152  (C854)',
          '  * ENTIRE patch as currently loose:             28.315358592526042',
          'No sharp global bound and no flat-sector-2 exclusion is claimed.']
    (out_dir/'summary.md').write_text('\n'.join(L))
    return summary


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--factors', type=int, nargs='*', default=None)
    ap.add_argument('--preflight', action='store_true')
    ap.add_argument('--aggregate', action='store_true')
    ap.add_argument('--keep-alias', action='store_true')
    ap.add_argument('--timeout', type=float, default=1200.0)
    a = ap.parse_args()

    canonical = LEAD / CANONICAL
    if not canonical.exists():
        print('FATAL: canonical frozen coefficients not found:', canonical); return 2
    digest = digest_of(canonical)
    d12 = digest[:12]
    out_dir = OUT / f'r15_{d12}'
    out_dir.mkdir(parents=True, exist_ok=True)
    print(f'frozen coefficients : {canonical.name}')
    print(f'coefficient sha256  : {digest}')
    print(f'digest-keyed outdir : {out_dir}')

    if a.aggregate:
        s = aggregate(out_dir, digest)
        print(f'sum of present uppers = {s["sum_of_present_uppers"]:.12f}; '
              f'all22 = {s["sum_covers_all_22"]}; missing = {s["records_missing"]}')
        return 0

    if a.preflight:
        todo = [11, 14]                     # the two cheapest factors in the old run
    elif a.factors:
        todo = [i for i in a.factors if i not in SKIP_IN_CERT]
    else:
        todo = R15_22

    alias = HERE / f'_alias_r15_{d12}'
    if alias.exists():
        shutil.rmtree(alias, ignore_errors=True)
    make_alias(canonical, alias)
    src_hashes = source_hashes(canonical)
    print('--- source hashes captured at launch (lead files, as read) ---')
    for k, v in src_hashes.items():
        print(f'   {str(v):64s} {k}')
    verify_exec_chain(canonical, alias)
    # extra end-to-end check requested by the lead: read the coefficients exactly the way
    # the kernel will, and confirm the bytes are the NEW ones.
    consumed = json.loads((alias / STALE).read_text())
    consumed_digest = hashlib.sha256((alias / STALE).read_bytes()).hexdigest()
    print(f'   kernel will consume z[0:3] = {consumed["z"][:3]}  (canonical '
          f'{json.loads(canonical.read_text())["z"][:3]})')
    assert consumed_digest == digest, 'kernel would read different bytes'
    print('   kernel-consumed coefficients == canonical: OK')
    print(f'alias dir           : {alias}')

    done, failed = [], []
    for i in todo:
        rec = run_factor(i, alias, out_dir, a.timeout)
        if rec is None or 'error' in rec:
            failed.append((i, (rec or {}).get('error')))
            print(f'  factor {i:2d} ({FACTOR_NAMES.get(i)}): FAILED {rec.get("error") if rec else ""}')
            continue
        ok = rec.get('coefficient_sha256') == digest
        done.append(i)
        print(f'  factor {i:2d} ({rec.get("factor"):10s}) upper={rec.get("upper")!r} '
              f'evals={rec.get("evaluations")} budget={rec.get("budget_ended")} '
              f'digest_ok={ok}')

    s = aggregate(out_dir, digest)
    print(f'\nsum of present uppers = {s["sum_of_present_uppers"]:.12f}')
    print(f'all 22 present and digest-clean: {s["sum_covers_all_22"]}')
    print(f'missing: {s["records_missing"]}')
    if failed:
        print(f'failed: {failed}')
    if not a.keep_alias:
        shutil.rmtree(alias, ignore_errors=True)
        print('alias directory removed')
    return 0


if __name__ == '__main__':
    sys.exit(main())
