from mpmath import mp, mpf, sin, cos, sqrt, asin, diff, pi
mp.dps=50
U=mpf('0.33173203427623414')
# LEAD's variable: alpha.  b(alpha)=2asin(r sin(alpha/2));  t=alpha/2 in [0,pi/2] for alpha in [0,pi]
def b_alpha(al,r): return 2*asin(r*sin(al/2))
def Fc(al,r,mu=0):
    b=b_alpha(al,r)
    return r*r*sin(al)/2 + (b-sin(b))/2 + mu*b
def b_aa_lead(al,r):
    t=al/2; w=sqrt(1-(r*sin(t))**2)
    return -r*(1-r*r)*sin(t)/(2*w**3)
# verify lead's b'' against adaptive differentiation wrt alpha
print('check b_aa: alpha, numeric wrt alpha, lead formula, my t-formula divide by 4')
for (r,al) in ((U,mpf('1.0')),(mpf('0.3'),mpf('2.0')),(mpf('0.9'),mpf('1.6'))):
    num=diff(lambda a: b_alpha(a,r), al, 2)
    t=al/2; w=sqrt(1-(r*sin(t))**2)
    my_t=2*(r*r*cos(t)**2/w**3 - r*sin(t)/w)   # my previously reported d2/dt2
    print('  r=%s al=%s  num_d2/dal2=%s  lead=%s  my_t/4=%s'%(mp.nstr(r,6),mp.nstr(al,5),
          mp.nstr(num,12), mp.nstr(b_aa_lead(al,r),12), mp.nstr(my_t/4,12)))
# F'' wrt alpha over the LEGAL domain alpha in [0,pi]
print()
print('max F\'\' (wrt alpha) over alpha in [0,pi], mu=0:')
for r in (U,mpf('0.5'),mpf('0.9'),mpf('0.99')):
    worst=(mpf('-1e9'),None)
    for i in range(0,1001):
        al=pi*mpf(i)/1000
        v=diff(lambda a: Fc(a,r,mpf(0)), al, 2)
        if v>worst[0]: worst=(v,al)
    print('  r=%-10s max=%s at alpha=%s   concave=%s'%(mp.nstr(r,6),mp.nstr(worst[0],10),mp.nstr(worst[1],5),worst[0]<=0))
