"""cline2-coupled-factors R16Z: decisive piecewise FD of V itself."""
import sys, math
R = 19/50
r, b1, b2, d0 = 0.375, 1.05, 1.05, 0.0
B1c, G1c = 0.405431351, -0.870277865
B2c, G2c = 0.400827103, -0.86525597
A1c, A2c = 0.012841585, 0.013306528
C0 = 0.000464943


def parts(d):
    A = b1-d; B = b2+d
    H = 2*r*math.sin(2*b1-d)
    k = r*(math.sin(b1)*math.sin(A)+math.sin(b2)*math.sin(B))
    hub = H*k
    e1 = r*math.sin(A)/R
    on = B1c*e1*e1+G1c*e1
    Y = 2*r*math.sin(b2)*math.sin(B)
    X = H-2*r*math.sin(b2)*math.cos(B)
    Q = X*X+Y*Y
    e2 = math.sqrt(Q)/(2*R)
    off = B2c*e2*e2+G2c*e2+A2c*math.atan2(Y, X)
    V = C0*d+hub+on+off
    return V, hub, on, off


h = 1e-4
for name, idx in [('V', 0), ('hub', 1), ('on', 2), ('off', 3)]:
    fp = parts(d0+h)[idx]; f0 = parts(d0)[idx]; fm = parts(d0-h)[idx]
    print(f'{name:4s} second difference = {(fp-2*f0+fm)/(h*h):+.9f}')
print()
# first derivatives
gp = (parts(d0+h)[0]-parts(d0-h)[0])/(2*h)
gm = (parts(d0+2*h)[0]-parts(d0)[0])/(2*h)
print('first deriv at d0 and d0+h:', gp, gm)
print('second deriv from those   :', (gm-gp)/h)
