from anchor_robust_flow_probe import solve,P,json
row=next(r for r in json.loads((P/'anchor-simplex-probe.json').read_text())['runs']if r['case']=='q11-58');out=solve(row,11);(P/'anchor-robust-q11-control.json').write_text(json.dumps(out,indent=2))
