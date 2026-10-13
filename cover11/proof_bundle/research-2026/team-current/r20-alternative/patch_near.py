from pathlib import Path

p = Path(__file__).with_name('near_attack.py')
s = p.read_text(encoding='utf-8')

# (1) clamp the critical-direction index to the 8 free y-coordinates
old = "    k_low = int(np.argmax(ycand))                      # lowest critical direction proxy: max deficit"
new = "    k_low = min(int(np.argmax(ycand)), 7)              # lowest critical direction proxy: max deficit"
assert old in s
s = s.replace(old, new, 1)

# (2) robust adversary extraction: scan the nodes list for deepest open entries with a point-like key
old2 = """    d = json.loads(CUTS.read_text(encoding='utf-8'))
    found = []

    def walk(obj, depth=0):"""
new2 = """    d = json.loads(CUTS.read_text(encoding='utf-8'))
    found = []
    PKEYS = ('y', 'y9', 'y8', 'widths', 'w', 'point', 'rep', 'vertex', 'u', 'x', 'adversary',
             'centroid', 'center')

    def first_point(obj):
        for k in PKEYS:
            if k in obj:
                v = obj[k]
                if isinstance(v, (list, tuple)) and len(v) >= 9:
                    y = to_y(v)
                    if y is not None:
                        return y
        return None
    # direct pass over 'nodes' / 'proposals' lists first
    for lk in ('nodes', 'proposals', 'fields'):
        seq = d.get(lk)
        if isinstance(seq, list):
            for rec in seq:
                if isinstance(rec, dict):
                    y = first_point(rec)
                    if y is not None and not rec.get('closed', False):
                        found.append({'depth': rec.get('depth'), 'y9': y, 'where': lk,
                                      'keys': sorted(rec.keys())[:14]})
                    elif isinstance(rec.get('nodes'), list):
                        for sub in rec['nodes']:
                            if isinstance(sub, dict):
                                y2 = first_point(sub)
                                if y2 is not None and not sub.get('closed', False):
                                    found.append({'depth': sub.get('depth', rec.get('depth')),
                                                  'y9': y2, 'where': lk + '.nodes',
                                                  'keys': sorted(sub.keys())[:14]})

    def walk(obj, depth=0):"""
assert old2 in s
s = s.replace(old2, new2, 1)
p.write_text(s, encoding='utf-8')
print('patched: clamped k_low, robust adversary extraction')
