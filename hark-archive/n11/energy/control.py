import json, os, time, copy
from fractions import Fraction as F
from checker import *
d = load_parsed(); ctx = Ctx(d)
rows = []; t0 = time.time()
pk = [(g, p) for g in sorted(d['G']) for p in d['G'][g]] + [('B22', p) for p in d['B22']]
for g, p in pk:
    ok, res, low = check(ctx, p)
    rows.append(dict(group=g, node=p['nodeID'], ok=ok, numeric_margin=float(res['numeric']),
                     min_field={k: float(v) for k, v in res.items()}))
print('positive', sum(r['ok'] for r in rows), '/', len(rows), 'time', round(time.time()-t0,1))
bad = [r for r in rows if not r['ok']]; print(bad[:3])
nm = sorted(r['numeric_margin'] for r in rows); print('numeric margin min/median', nm[0], nm[len(nm)//2])
# negative controls
neg = []
p0 = d['G']['G01'][0]
def mut(name, f):
    q = copy.deepcopy(p0); f(q); ok, res, _ = check(ctx, q); neg.append(dict(name=name, rejected=not ok,
        failing=[k for k, v in res.items() if (v < 0 if k != 'numeric' else v <= 0)]))
mut('beta_sum_2', lambda q: q['beta'].__setitem__(12, q['beta'][12] + 1))
mut('beta_neg', lambda q: (q['beta'].__setitem__(12, q['beta'][12] + F(1,10)), q['beta'].__setitem__(next(i for i,b in enumerate(q['beta']) if b==0), F(-1,10))))
mut('lam_neg', lambda q: q['lam'].__setitem__(0, F(-1, 1000)))
mut('rmin_up', lambda q: q.__setitem__('rmin', q['rmin'] + F(1, 10)))
mut('line_c_up', lambda q: q['line'][0].__setitem__('c', q['line'][0]['c'] + F(1, 10**6)))
mut('line_shift', lambda q: q['line'][0].__setitem__('shift', q['line'][0]['shift'] + 1))
mut('endpoint_a_up', lambda q: q['line'][3].__setitem__('a', q['line'][3]['a'] + F(1, 10)))
mut('wrong_node', lambda q: q.__setitem__('nodeID', d['G']['G01'][1]['nodeID']))
mut('nonterminal_node', lambda q: q.__setitem__('nodeID', 0))
mut('zero_dual', lambda q: (q.__setitem__('lam', [F(0)]*7)))
for r in neg: print(r)
out = dict(positive=rows, negative=neg, positive_pass=sum(r['ok'] for r in rows), positive_total=len(rows))
json.dump(out, open('control-results.json.tmp','w'), indent=0); os.replace('control-results.json.tmp','control-results.json')
