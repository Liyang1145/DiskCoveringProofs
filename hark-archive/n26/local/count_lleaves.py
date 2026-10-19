import os,json
r='/workspace/work/dcp-n26/v3replay/lleaves'
out={d:len([f for f in os.listdir(os.path.join(r,d)) if f.startswith('s') and f.endswith('.json')]) for d in sorted(os.listdir(r)) if os.path.isdir(os.path.join(r,d))}
json.dump(out,open('/workspace/work/dcp-n26/local/count_lleaves.json','w'),indent=0)
print(sum(out.values()),len(out))
