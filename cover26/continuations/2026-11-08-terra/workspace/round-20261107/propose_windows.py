"""Find rational window endpoints; proposals only."""
import math
U=.229001
for b,e,shift in [(16,.08,.02),(17,.06,0),(18,.044,0)]:
    d=math.pi/b-shift
    def G(t):
        s=math.sin(t)
        return t-s*math.cos(t)+s*math.sqrt(max(0,U*U-s*s))
    s=math.sin(d)
    p=2*s*s+math.cos(d)*(U*U-2*s*s)/math.sqrt(U*U-s*s)
    J=lambda t:G(d)+p*(t-d)-G(t)
    for name,budget in [('single',2*(e-.0387)*U*U),('ear',2*(2*e-.097)*U*U)]:
        if budget<0:continue
        lo=next((i for i in range(1,100000) if J(d-i/1000000)>budget),None)
        hi=next((i for i in range(1,100000) if d+i/1000000<math.asin(U) and J(d+i/1000000)>budget),None)
        print(b,name,'budget',budget,'offsets',-lo if lo else None,hi)
