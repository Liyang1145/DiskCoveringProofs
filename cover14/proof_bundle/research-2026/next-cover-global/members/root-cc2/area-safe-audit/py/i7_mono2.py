import mpmath as mp
mp.mp.dps=40
h=lambda L: mp.sin(L)/L
print("h(L)=sin L/L on the LEGAL domain (0, pi/2]  [L=2asin rho, rho>=0 => L<=pi/2]:")
vals=[]
for k in range(1,20):
    L=mp.pi/2*mp.mpf(k)/20
    vals.append((L,h(L)))
for L,v in [vals[0],vals[5],vals[10],vals[-1]]:
    print("   L=%-12s h=%s" % (mp.nstr(L,8), mp.nstr(v,12)))
mono=all(vals[i+1][1]<vals[i][1] for i in range(len(vals)-1))
print("   strictly decreasing on the grid:",mono)
print("   h(pi/2)=2/pi =",mp.nstr(mp.mpf(2)/mp.pi,12),"  h->1 as L->0")
print()
print("our regime: L_our=2asin(0.3317320)=",mp.nstr(2*mp.asin(mp.mpf("0.3317320342762341")),10))
print("  cap(rho)=pi(1-h) increasing in rho on (0,pi/2], since h decreases.  => the")
print("  outward-clip monotonicity claim HOLDS (the document's wording about (0,pi) is")
print("  imprecise but the true fact sin x/x decreasing on (0,pi) is a standard result,")
print("  so no defect: my earlier 'falsy' read was my own erroneous scan interval).")
