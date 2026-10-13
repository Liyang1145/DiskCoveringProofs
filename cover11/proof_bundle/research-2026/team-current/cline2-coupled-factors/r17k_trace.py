"""cline2-coupled-factors R17k: trace g' numerically step by step."""
from mpmath import mp
mp.dps = 50
r = mp.mpf('0.379'); b = mp.mpf('1.10')
x0 = 2*b-mp.pi/2+mp.asin(r)


def vals(w):
    x = -mp.sin(w)+r*mp.sin(x0+w)
    p = mp.cos(w)-r*mp.cos(x0+w)
    x1 = -mp.cos(w)+r*mp.cos(x0+w)
    x2 = mp.sin(w)-r*mp.sin(x0+w)
    Y = 1-p
    Yp = -x
    Ypp = -x1
    g = x1*Y-x*Yp
    return dict(x=x, p=p, x1=x1, x2=x2, Y=Y, Yp=Yp, Ypp=Ypp, g=g)


w0 = mp.mpf('0.1914')
v = vals(w0)
print('at w0:')
for k in ('x', 'p', 'x1', 'x2', 'Y', 'Yp', 'Ypp', 'g'):
    print(f'   {k:4s} = {mp.nstr(v[k],18)}')
print()
print("check Y' = derivative of (1-p):")
print(f"   Y' = -x gives {mp.nstr(-v['x'],18)}")
h = mp.mpf('1e-6')
p_p = vals(w0+h)['p']; p_m = vals(w0-h)['p']
print(f"   FD of (1-p) = {mp.nstr(-(p_p-p_m)/(2*h),18)}")
print()
print("check Y'' :")
print(f"   Y'' = -x' gives {mp.nstr(-v['x1'],18)}")
Yp_p = vals(w0+h)['Yp']; Yp_m = vals(w0-h)['Yp']
print(f"   FD of Y' = {mp.nstr((Yp_p-Yp_m)/(2*h),18)}")
print()
print("g = x'Y - xY' :")
print(f"   value = {mp.nstr(v['g'],18)}")
print("g' by parts: g' = x''Y + x'Y' - x'Y' - xY'' = x''Y - xY''")
print(f"   x''Y - xY'' = {mp.nstr(v['x2']*v['Y']-v['x']*v['Ypp'],18)}")
print("g' by the equivalent form with Y'=-x, Y''=-x':")
print(f"   g = x'Y + x^2  =>  g' = x''Y + x'Y' + 2xx' = x''Y - x'x + 2xx'")
print(f"   = {mp.nstr(v['x2']*v['Y']-v['x1']*v['x']+2*v['x']*v['x1'],18)}")
print("   but ALSO g = x'Y + x^2 with Y = 1-p and p' = x:")
print(f"   g' = x''Y + x'*(-p') + 2x*p' = x''Y - x' x + 2 x x   "
      f"= {mp.nstr(v['x2']*v['Y']-v['x1']*v['x']+2*v['x']*v['x'],18)}")
print()
print("   FD of g:")
for hh in ['1e-4', '1e-5', '1e-6']:
    hh = mp.mpf(hh)
    gp = (vals(w0+hh)['g']-vals(w0-hh)['g'])/(2*hh)
    print(f"      h={hh}: g' = {mp.nstr(gp,20)}")
print()
print("RESOLUTION: x'' in the tuple above is d^2x/dw^2 = +cos w - r cos(x0+w)?")
print(f"   x'' computed as sin w - r sin(x0+w) = {mp.nstr(v['x2'],18)}")
print(f"   d/dw x' where x' = -cos w + r cos(x0+w) gives sin w - r sin(x0+w) = "
      f"{mp.nstr(mp.sin(w0)-r*mp.sin(x0+w0),18)}  -- consistent")
print(f"   d/dw x  where x = -sin w + r sin(x0+w) gives -cos w + r cos(x0+w) = x' = "
      f"{mp.nstr(v['x1'],18)}")
print()
print("   So x' = -cos w + r cos(x0+w) and x'' = +sin w - r sin(x0+w) = -x !")
print(f"   check: -x = {mp.nstr(-v['x'],18)}  vs x'' = {mp.nstr(v['x2'],18)}   "
      f"equal: {abs(-v['x']-v['x2']) < mp.mpf('1e-30')}")
print()
print("   => x'' = -x  (not the value used earlier).  Redo g':")
print(f"   g' = x''Y - xY'' = (-x)Y - x(-x') = -xY + xx' = "
      f"{mp.nstr(-v['x']*v['Y']+v['x']*v['x1'],18)}")
