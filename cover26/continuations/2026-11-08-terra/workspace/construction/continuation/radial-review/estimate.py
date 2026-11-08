import math
r=.22; ts=[.23,19/75,83/300,.3,97/300,26/75,.37,.59,37/60,193/300,.67,209/300,217/300,.75,1]; w=[19665,20748,24696,21748,13145,11524,1683,92039,67041,46430,35384,23953,21024,1711,450827];
for N in [1000,10000,100000]:
 best=0;where=0
 for i in range(N):
  lo=i*1.4884/N;hi=(i+1)*1.4884/N;z=0
  for t,weight in zip(ts,w):
   l=max(lo,(t-r)**2);h=min(hi,(t+r)**2)
   if l>h:continue
   q=max(l,min(h,t*t+r*r));D=4*t*t*q-(t*t+q-r*r)**2
   A=t*t+l-r*r
   y=math.sqrt(max(0,D))/A
   theta=y-y**3/3+y**5/5
   z+=weight*theta
  if z>best:best=z;where=i
 print(N,'lower bound',math.pi*sum(w)/best, 'best d',math.sqrt(where*1.4884/N))
