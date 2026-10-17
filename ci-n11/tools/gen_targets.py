#!/usr/bin/env python3
"""Generate tools/targets/*.txt (lake build target lists per stage/group) and tools/audit/*.txt.
Run from repo root: python3 tools/gen_targets.py   (uses tools/plan.json + drafts/)."""
import json, os, glob, re
R = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
plan = json.load(open(f'{R}/tools/plan.json'))
T = f'{R}/tools/targets'; A = f'{R}/tools/audit'
os.makedirs(T, exist_ok=True); os.makedirs(A, exist_ok=True)

def w(path, mods):
    open(path, 'w').write('\n'.join(mods) + '\n')

def drafts(sub):
    return sorted('N11Formalization.' + os.path.basename(f)[:-5]
                  for f in glob.glob(f'{R}/drafts/{sub}/N11Formalization/*.lean'))

# Stage A: the accepted A25 root (pre-c450pilot root file), as its import list
a25root = [l.split()[1] for l in open(f'{R}/lean/N11Formalization.lean.pre-c450pilot-20261014')
           if l.startswith('import ')]
w(f'{T}/A.txt', a25root)
w(f'{T}/B.txt', plan['pilot12_13'])
w(f'{T}/C.txt', plan['src14_36'])
w(f'{T}/D.txt', ['N11Formalization.C450FullTelescope'])
en = drafts('energy')
w(f'{T}/energy-matrix.txt', ['N11Formalization.Paid16MatrixCellCertificate'])
w(f'{T}/energy-paid16.txt', [m for m in en if 'Paid16General' in m] + ['N11Formalization.EnergyTerminalBatchB12'])
w(f'{T}/energy-refine.txt', [m for m in en if 'EnergyRefine' in m] + ['N11Formalization.EnergyTerminalBatchB13'])
cl = drafts('class33')
core = ['Class33Labels', 'Class33RepData', 'Class33SwitchFields', 'Class33SwitchBridge']
w(f'{T}/class-core.txt', ['N11Formalization.' + c for c in core])
w(f'{T}/class-switch.txt', [m for m in cl if 'SwitchTree' in m])
w(f'{T}/class-face.txt', [m for m in cl if 'FaceTree' in m])
w(f'{T}/class-asm.txt', [m for m in cl if 'Assembly' in m])
other = [m for m in cl if not any(k in m for k in ['SwitchTree', 'FaceTree', 'Assembly']) and m.split('.')[-1] not in core]
if other:
    w(f'{T}/class-other.txt', other)

# audit lists: lines "MODULE" (= every top-level theorem in that module) or "MODULE CONST"
segs = [f'N11Formalization.C450Source{k}Segment' for k in range(12, 37)]
w(f'{A}/A.txt', ['N11Formalization.ActualMainRoute N11Formalization.ActualMainRoute.main_of_remaining',
                 'N11Formalization.CanonicalSharedMomentFiniteCertificate N11Formalization.CanonicalSharedMomentFiniteCertificate.full_disk_bound_of_finite_class_tables',
                 'N11Formalization.SourceExactRoot N11Formalization.SourceExactRoot.source_attainment'])
w(f'{A}/BC.txt', [f'{s} {s}.source{re.search(r"Source(\d+)Segment", s).group(1)}_paid' for s in segs])
w(f'{A}/D.txt', ['N11Formalization.C450FullTelescope'])
w(f'{A}/energy.txt', ['N11Formalization.EnergyTerminalBatchB12', 'N11Formalization.EnergyTerminalBatchB13',
                      'N11Formalization.Paid16GeneralHAll', 'N11Formalization.EnergyRefineAll',
                      'N11Formalization.Paid16MatrixCellCertificate']
  + [m for m in en if 'HAgg' in m or 'RefineAgg' in m])
w(f'{A}/class.txt', [m for m in cl if 'Assembly' in m] + ['N11Formalization.' + c for c in core])
print('ok', {os.path.basename(f): len(open(f).read().split('\n')) - 1 for f in sorted(glob.glob(T + '/*.txt'))})
