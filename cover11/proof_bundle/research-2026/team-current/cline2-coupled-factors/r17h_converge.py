"""cline2-coupled-factors R17h: convergence check at tight steps, then the rigorous sup."""
import math, json, sys
from pathlib import Path
from mpmath import mp, iv

mp.dps = 40
iv.dps = 30
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']
Z = {i: mp.mpf(f'{zJ[i]:.9f}') for i in range(len(zJ))}
R = mp.mpf(19)/50


def consts(j):
    return ((Z[1], Z[112], Z[34], Z[96]) if j == 0 else (Z[3], Z[115], Z[39], Z[101]))


def data(r, b, w):
    s = mp.sqrt(1-r*r); ph = mp.asin(r)
    x0 = 2*b-mp.pi/2+ph
    p = mp.cos(w)-r*mp.cos(x0+w)
    x = -mp.sin(w)+r*mp.sin(x0+w)
    p1 = -mp.sin(w)+r*mp.sin(x0+w)
    p2 = -mp.cos(w)+r*mp.cos(x0+w)
    x1 = -mp.cos(w)+r*mp.cos(x0+w)
    x2 = mp.sin(w)-r*mp.sin(x0+w)
    return dict(s=s, x0=x0, p=p, x=x, p1=p1, p2=p2, x1=x1, x2=x2,
                Y=1-p, Yp=-p1, Ypp=-p2)


def W_val(r, b, w, j):
    mu, h, d, l = consts(j)
    dd = data(r, b, w)
    q = dd['x']**2+dd['Y']**2
    return (-r*dd['s']*mp.sin(b)**2+(mp.mpf(1)/2-mu)*w+dd['x']/2
            + (mu+h)*mp.atan2(dd['x'], dd['Y'])-d*(q/R**2)/(R**0)-l*mp.sqrt(q)/R)


def W2_closed(r, b, w, j):
    mu, h, d, l = consts(j)
    dd = data(r, b, w)
    x, Y = dd['x'], dd['Y']
    rho = x*x+Y*Y
    g = dd['x1']*Y-x*dd['Yp']
    gp = dd['x2']*Y-x*dd['Ypp']
    rho1 = 2*(x*dd['x1']+Y*dd['Yp'])
    a2 = gp/rho-g*rho1/(rho*rho)
    sq = mp.sqrt(rho)
    u = sq/R
    u1 = -dd['p1']/(R*sq)
    u2 = -dd['p2']/(R*sq)+dd['p1']*dd['p1']/(R*rho*sq)
    return dd['x2']/2+(mu+h)*a2-2*d*(u1*u1+u*u2)-l*u2


print('=== tight-step convergence of the FD against the closed form ===')
for (j, r, b, w0) in [(0, mp.mpf('0.379'), mp.mpf('1.10'), mp.mpf('0.1914')),
                      (0, mp.mpf('0.379'), mp.mpf('0.95'), mp.mpf('0.1679')),
                      (1, mp.mpf('0.37999'), mp.mpf('1.19'), mp.mpf('0.35'))]:
    cl = W2_closed(r, b, w0, j)
    print(f'  j={j} r={float(r)} b={float(b)} w={float(w0)}  closed = {mp.nstr(cl,18)}')
    prev = None
    for hh in ['1e-3', '5e-4', '2.5e-4', '1.25e-4', '6.25e-5']:
        h = mp.mpf(hh)
        fd = (W_val(r, b, w0+h, j)-2*W_val(r, b, w0, j)+W_val(r, b, w0-h, j))/(h*h)
        tag = '' if prev is None else f'  (rel change {mp.nstr(abs(fd-prev)/abs(fd),3)})'
        print(f'     h={hh:8s} FD = {mp.nstr(fd,18)}{tag}')
        prev = fd
    print(f'     closed-form match: rel diff = '
          f'{mp.nstr(abs(prev-cl)/abs(prev),4)}')

print()
print('=== rigorous sup of W\'\' over the box (interval arithmetic) ===')


def interval_W2(r, b, w, j):
    mu, h, d, l = [iv.mpf(mp.nstr(mp.mpf(f'{zJ[i]:.9f}'), 14)) for i in
                   ((1, 112, 34, 96) if j == 0 else (3, 115, 39, 101))]
    s = iv.sqrt(1-r*r)
    ph = iv.mpf([float(mp.asin(mp.mpf(str(float(r.a))))),
                 float(mp.asin(mp.mpf(str(float(r.b)))))] )
    x0 = 2*b-iv.pi/2+ph
    # use interval sin/cos through the argument interval
    p = iv.cos(w)-r*iv.cos(x0+w)
    x = -iv.sin(w)+r*iv.sin(x0+w)
    p1 = -iv.sin(w)+r*iv.sin(x0+w)
    p2 = -iv.cos(w)+r*iv.cos(x0+w)
    x1 = -iv.cos(w)+r*iv.cos(x0+w)
    x2 = iv.sin(w)-r*iv.sin(x0+w)
    Y = 1-p; Yp = -p1; Ypp = -p2
    rho = x*x+Y*Y
    if rho.a <= 0:
        return None
    g = x1*Y-x*Yp
    gp = x2*Y-x*Ypp
    rho1 = 2*(x*x1+Y*Yp)
    a2 = gp/rho-g*rho1/(rho*rho)
    sq = iv.sqrt(rho)
    u = sq/R
    u1 = -p1/(R*sq)
    u2 = -p2/(R*sq)+p1*p1/(R*rho*sq)
    return x2/2+(mu+h)*a2-2*d*(u1*u1+u*u2)-l*u2


rlo = iv.mpf('0.379'); rhi = iv.mpf('0.37999')
blo = iv.mpf(str(mp.acos(mp.mpf('0.37999'))/2)); bhi = iv.mpf('1.19')
print(f'  box: r=[0.379,0.37999] b=[{float(blo):.6f},1.19]')
sup_overall = None
for (wlo, whi) in [('0.0', '0.1'), ('0.1', '0.2'), ('0.2', '0.3'), ('0.3', '0.4'),
                   ('0.4', '0.5'), ('0.5', '0.6'), ('0.6', '0.7')]:
    w = iv.mpf([wlo, whi])
    for j in (0, 1):
        try:
            W2b = interval_W2(rlo, blo, w, j)
        except Exception as e:
            print(f'  w=[{wlo},{whi}] j={j}: exception {e}')
            continue
        if W2b is None:
            print(f'  w=[{wlo},{whi}] j={j}: rho not positive')
            continue
        print(f'  w=[{wlo},{whi}] j={j}: W\'\' in [{float(W2b.a):.4f}, {float(W2b.b):.4f}]')
        if sup_overall is None or W2b.b > sup_overall:
            sup_overall = W2b.b
print(f'\n  sup enclosure upper bound over the box = {float(sup_overall):.6f}')
