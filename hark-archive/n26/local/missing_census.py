import json,collections
m=json.load(open('lleaf_boxes_missing.json'))['missing']
c=collections.Counter(v['top'] for v in m.values())
out={'n':len(m),'by_top':dict(c.most_common())}
json.dump(out,open('missing_census.json','w'),indent=1)
print(out['n'],list(c.most_common(8)),len(c))
