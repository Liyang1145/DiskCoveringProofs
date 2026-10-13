"""R16 audit prep: hash pins, z pins, certificate arithmetic, and the source modules."""
import hashlib, json, math, re
from pathlib import Path

L = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
HERE = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\cline2-closure-kernel')


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


print('=== hash pins declared in the two certificates vs actual files ===')
for cert_name in ['patch_outer_norm_boundary_certificate.json',
                  'norm_cartesian_control_certificate.json']:
    cert = json.loads((L / cert_name).read_text())
    print(f'\n{cert_name}: declared coefficient_sha256 = {cert["coefficient_sha256"][:16]}...')
    bad = []
    for name, h in cert.get('source_sha256', {}).items():
        p = L / name
        if not p.exists():
            bad.append((name, 'ABSENT')); continue
        if sha(p) != h:
            bad.append((name, 'HASH MISMATCH'))
    print('   source hash check:', 'ALL OK' if not bad else bad)
    print(f'   upper={cert.get("upper")}  liveboxes={cert.get("liveboxes")} '
          f'budget_ended={cert.get("budget_ended")}  evaluations={cert.get("evaluations")}')
    print(f'   domain={cert.get("domain")}')

fj = L / 'joint_nested_frozen.json'
print(f'\n=== joint_nested_frozen.json ===')
print('exists:', fj.exists())
if fj.exists():
    print('sha256:', sha(fj)[:32], ' size', fj.stat().st_size)
    j = json.loads(fj.read_text())
    z = j.get('z', [])
    print('len(z):', len(z))
    print('z[50:73] all zero:', all(abs(v) < 1e-12 for v in z[50:73]))
    print('first 12 z:', [round(v, 9) for v in z[:12]])
    print('z[112:121]:', [round(v, 9) for v in z[112:121]])
    print('numeric_total in file:', j.get('numeric_total'))
    print('scope in file:', j.get('scope'))

print('\n=== current z pin mentioned by lead: 5671967... ===')
print('declared coefficient_sha256 in patch certificate:',
      json.loads((L / 'patch_outer_norm_boundary_certificate.json').read_text())['coefficient_sha256'])

print('\n=== current22_manifest.json ===')
p = L / 'current22_manifest.json'
if p.exists():
    m = json.loads(p.read_text())
    print('keys:', list(m.keys())[:8])
    print(json.dumps(m, indent=1)[:1500])

print('\n=== 22 complement bound files present? ===')
folder = L.parent / 'cline2-coupled-factors' / 'out'
print('coupled-factors dir exists:', folder.exists())
if folder.exists():
    subs = sorted([d for d in folder.iterdir() if d.is_dir()])
    print('subdirs:', [d.name for d in subs][:8])
