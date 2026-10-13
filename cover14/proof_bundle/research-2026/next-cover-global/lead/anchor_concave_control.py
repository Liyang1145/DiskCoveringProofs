from anchor_robust_flow_probe import solve,P,json
out=[]
for file,casename,q in [('anchor-robust-q10-proposals.json','q10-843',10),('anchor-simplex-probe.json','q11-58',11),('anchor-robust-q10-proposals.json','q10-878',10)]:
 row=next(r for r in json.loads((P/file).read_text())['runs']if r['case']==casename);r=solve(row,q,'concave');out.append(r);(P/'anchor-concave-controls.json').write_text(json.dumps({'status':'numeric_concave_flow_controls','runs':out},indent=2))
