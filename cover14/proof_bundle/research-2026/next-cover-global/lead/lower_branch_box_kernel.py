"""Safe additional lowerbranch loss on boxes wholly in B<pi,B+min beta>=pi."""
from shared_radius_corner_kernel import *
previous_boxbound=boxbound

def lower_loss(box):
 lo=[l for l,h in box];hi=[h for l,h in box]
 if sum(hi)>=1 or sum(lo)+min(lo)<1 or min(lo)<=0:return I(0)
 # L_i=2 sin(beta_i)sin(beta_i/2)sin(d)/cos(beta_i/2-d).
 # Denominator <=1 and positive on certified simplex region. Independentpositive factors give safe lower bound.
 dmin=(1-sum(hi))/2
 vals=[]
 for l,h in box:
  sb=min(sinpoint(l).lo,sinpoint(h).lo);sh=sinpoint(l/2).lo;sd=sinpoint(dmin).lo
  vals.append((I(2*U*U)*I(max(0,sb),S,True)*I(max(0,sh),S,True)*I(max(0,sd),S,True)).lo)
 return I(min(vals),S,True)

def boxbound(box,p,opts):
 old=previous_boxbound(box,p,opts);loss=lower_loss(box)
 if loss.lo==0:return old
 base=I(0)
 for (lo,hi),pot in zip(box,p):
  aa=U*U;pf=float(pot);af=float(aa);opt=0 if pf>=af else(math.pi if pf<=-af else math.acos(pf/af));tf=max(float(lo)*math.pi,min(float(hi)*math.pi,opt));t=max(Q(0),min(Q('3.141592653589'),Q(format(tf,'.12f'))));sn,cs=sc(t);slope=I(aa)*cs-pot;vv=[PI*I(lo)*slope,PI*I(hi)*slope];base+=I(aa)*(sn-I(t)*cs)+I(max(v.lo for v in vv),max(v.hi for v in vv),True)
 return I(min(old.lo,base.lo-loss.hi),min(old.hi,base.hi-loss.lo),True)
