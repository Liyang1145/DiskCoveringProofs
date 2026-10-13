import mpmath as mp
mp.mp.dps=40
U=mp.mpf("0.33173203427623414")
a0=mp.mpf("2.42")
f=lambda a: 2*mp.asin(U*mp.sin(a/2))
fp=lambda a: U*mp.cos(a/2)/mp.sqrt(1-U*U*mp.sin(a/2)**2)
A=2*mp.asin(U/2)
k=mp.mpf("31")/250
print("U  =",mp.nstr(U,18))
print("A  = 2asin(U/2)      =",mp.nstr(A,12),"  167/500 =",mp.nstr(mp.mpf(167)/500,12))
print("f(alpha0=2.42)       =",mp.nstr(f(a0),12))
print("f'(alpha0)           =",mp.nstr(fp(a0),12),"  31/250 =",mp.nstr(k,12))
print("f'(alpha0) < 31/250 ? ", fp(a0)<k)
print("f(alpha0)-alpha0 f'  =",mp.nstr(f(a0)-a0*fp(a0),12))
print("A + k*alpha0         =",mp.nstr(A+k*a0,12))
print("envelope max(A,f) <= A+k*alpha at alpha0 ? ", max(A,f(a0)) <= A+k*a0)
print()
print("check the envelope  max(A,f(a)) <= 167/500 + (31/250) a  on a grid:")
worst=None
N=20000
for i in range(0,N+1):
    a=mp.pi*mp.mpf(i)/N
    lhs=max(A,f(a)); rhs=mp.mpf(167)/500+k*a
    d=lhs-rhs
    if worst is None or d>worst[0]: worst=(d,a,lhs,rhs)
print("   worst excess =",mp.nstr(worst[0],10)," at alpha =",mp.nstr(worst[1],10))
print("   lhs=",mp.nstr(worst[2],12)," rhs=",mp.nstr(worst[3],12))
print("   envelope VALID:", worst[0]<=0)
