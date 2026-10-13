from mpmath import mp, mpf, sin, cos, sqrt
mp.dps=40
def bt2(t,r):
    w=sqrt(1-(r*sin(t))**2)
    # b = 2 asin(r sin t); b' = 2 r cos t / w
    # b'' = d/dt (2 r cos t / w)
    return 2*( -r*sin(t)/w + r**3*sin(t)*cos(t)**2/w**3 )   # = 2r(-sin t/w + r^2 sin t cos^2 t/w^3)
def lead_form(t,r):
    w=sqrt(1-(r*sin(t))**2)
    return -r*(1-r*r)*sin(t)/(2*w**3)
def numeric(t,r):
    h=mpf('1e-8')
    f=lambda s: 2*r*cos(s)/sqrt(1-(r*sin(s))**2)
    return (f(t+h)-2*f(t)+f(t-h))/h**2
for (r0,t0) in ((mpf('0.33173203427623414'),mpf('0.5')),(mpf('0.3'),mpf('1.0')),(mpf('0.9'),mpf('0.8')),(mpf('0.5'),mpf('0.3'))):
    print('r',mp.nstr(r0,8),'t',mp.nstr(t0,4),' numeric',mp.nstr(numeric(t0,r0),10),
          ' mychain',mp.nstr(bt2(t0,r0),10),' lead',mp.nstr(lead_form(t0,r0),10))
