import json, hashlib, pathlib
ROOT = pathlib.Path('n11-work/lean/N11Formalization')
LEAVES = ['EnergyRefineN0003Restored','EnergyRefineN0023Restored','EnergyRefineN0038','EnergyRefineN3432','EnergyRefineN3490','EnergyRefineN3517','EnergyRefineN3550','EnergyRefineN3564','EnergyRefineN3569','EnergyRefineN3578','EnergyRefineN3738','EnergyRefineN3781','EnergyRefineN3825','EnergyRefineN3854']
GREEN = ['EnergyRefineN3783','EnergyRefineN3841','EnergyRefineN3851','EnergyRefineN3522','EnergyRefineN4162','EnergyRefineN4244','EnergyRefineN3807','EnergyRefineN3802','EnergyRefineN3821']
def scan(name):
    p = ROOT/(name+'.lean')
    b = p.read_bytes()
    t = b.decode('utf-8')
    lines = t.split('\n')
    return {
      'file': str(p),
      'sha256': hashlib.sha256(b).hexdigest().upper(),
      'bytes': len(b),
      'maxRecDepth': t.count('maxRecDepth'),
      'maxHeartbeats0': t.count('maxHeartbeats 0'),
      'decideKernel': t.count('decide +kernel'),
      'nativeDecide': t.count('native_decide'),
      'maxLine': max((len(l) for l in lines), default=0),
    }
def classify(r):
    if r['maxHeartbeats0'] > 0: return 'blowup(maxHeartbeats 0)'
    if r['maxRecDepth'] > 0 and r['maxLine'] > 10000: return 'green-shape(maxRecDepth,giant-line)'
    if r['maxRecDepth'] > 0: return 'recDepth-raise'
    return 'plain'
rep = {'leaves':[], 'green_reference':[]}
for n in LEAVES:
    r = scan(n); r['shape'] = classify(r); rep['leaves'].append(r)
for n in GREEN:
    r = scan(n); r['shape'] = classify(r); rep['green_reference'].append(r)
rep['leaves_all_green_shape'] = all(x['shape']=='green-shape(maxRecDepth,giant-line)' for x in rep['leaves'])
rep['green_reference_all_green_shape'] = all(x['shape']=='green-shape(maxRecDepth,giant-line)' for x in rep['green_reference'])
print(json.dumps(rep, indent=1))
