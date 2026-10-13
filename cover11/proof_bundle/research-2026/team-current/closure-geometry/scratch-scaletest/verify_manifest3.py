import json, os
from fractions import Fraction as F

base = r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\solo-20260922'
load = lambda f: json.load(open(os.path.join(base, f)))

A = load('directional_low_cover.json')['runs'] + load('directional_e_cover.json')['runs']
B = load('directional_fixed_low.json')['runs'] + load('directional_fixed_all.json')['runs']
print('kernel A runs:', len(A), ' boxes:', sum(r['boxes'] for r in A))
print('kernel B runs:', len(B), ' boxes:', sum(r['boxes'] for r in B))
print('manifest declared: A', load('DUAL-MANIFEST.json')['kernel_A_boxes'],
      'B', load('DUAL-MANIFEST.json')['kernel_B_boxes'])
print()
print('kernel A run keys:', sorted(A[0].keys()))
print('kernel B run keys:', sorted(B[0].keys()))
print()
print('segment lengths: A', [ (r['e_interval'][0][:6], r['e_interval'][1][:6]) for r in A[:3]], '...')
print('segment lengths: B', [ (r['e_interval'][0][:6], r['e_interval'][1][:6]) for r in B[:3]], '...')
print()
print('e-segments identical between kernels:',
      [r['e_interval'] for r in sorted(A, key=lambda r: F(r['e_interval'][0]))] ==
      [r['e_interval'] for r in sorted(B, key=lambda r: F(r['e_interval'][0]))])
print('weights identical between kernels:',
      [r['weights'] for r in sorted(A, key=lambda r: F(r['e_interval'][0]))] ==
      [r['weights'] for r in sorted(B, key=lambda r: F(r['e_interval'][0]))])
print()
print('all pass flags true:', all(r['pass'] for r in A) and all(r['pass'] for r in B))
print()
print('=== the two domain components per run ===')
r = A[0]
print('kernel A run[0]: e_interval', r['e_interval'], 'dual_source_e', r.get('dual_source_e'), 'keys', sorted(r.keys()))
print('weights keys:', list(r['weights'].keys()))
print('weights content:', json.dumps(r['weights'])[:220])
