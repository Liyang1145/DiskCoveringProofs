# Re-parse the EMITTED Lean text and re-run the exact checker on it (text == checked data).
import sys, os, json, re
sys.path.insert(0, '.')
import parse, checker
from checker import *
parse.W = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'lean-wip', 'N11Formalization')
d = load_parsed(); ctx = Ctx(d)
tot = ok = 0; bad = []
for f in sorted(os.listdir(parse.W)):
    if not re.match(r'Paid16GeneralH\d{3}\.lean$', f): continue
    for p in parse.parse_G(f):
        tot += 1; good, res, _ = check(ctx, p); ok += good
        if not good: bad.append(p['nodeID'])
print('roundtrip', ok, '/', tot, 'bad', bad[:10])
json.dump(dict(ok=ok, total=tot, bad=bad), open('roundtrip-results.json', 'w'))
