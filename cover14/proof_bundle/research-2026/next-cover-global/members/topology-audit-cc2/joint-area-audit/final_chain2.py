from mpmath import mp, mpf, sin, cos, sqrt, asin, diff, pi
mp.dps=40
U=mpf('0.33173203427623414')
def Fc(al,r,mu=0):
    b=2*asin(r*sin(al/2))
    return r*r*sin(al)/2 + (b-sin(b))/2 + mu*b
def Fpp_closed(al,r,mu=0):
    """F'' wrt alpha, closed form from the lead's chain."""
    t=al/2; w=sqrt(1-(r*sin(t))**2); z=r*sin(t)
    b_aa=-r*(1-r*r)*sin(t)/(2*w**3)          # lead's b''
    return -r*r*sin(t)*cos(t) + r**3*sin(t)*cos(t)**2/w + (z*z+mu)*b_aa
print('alpha,  numeric F\'\'(alpha),  closed form,  difference   (r=U)')
bad=0
for i in range(0,41):
    al=pi*mpf(i)/40
    num=diff(lambda a: Fc(a,U,mpf(0)), al, 2) if 0<al<pi else mpf(0)
    cf=Fpp_closed(al,U,0)
    d=num-cf
    if abs(d)>1e-9 and 0<al<pi: bad+=1
    print('  alpha=%-8s num=%-16s closed=%-16s diff=%s'%(mp.nstr(al,5),mp.nstr(num,10),mp.nstr(cf,10),mp.nstr(d,4)))
print('mismatches:',bad)
print()
print('sanity: is the closed form ever positive on (0,pi)?')
mx=max((Fpp_closed(pi*mpf(i)/2000,U,0), pi*mpf(i)/2000) for i in range(1,2000))
print('  max closed-form F\'\' =',mp.nstr(mx[0],8),'at alpha=',mp.nstr(mx[1],6))
