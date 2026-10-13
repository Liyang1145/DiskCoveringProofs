"""R21: exact verification of the angle Hessian, superseding my r20 numerics.

theta(x,y) = atan2(y,x):
  grad   = (-y, x)/(x^2+y^2)            -> |grad| = 1/L        (degree 0)
  Hess   = [[2xy, y^2-x^2],[y^2-x^2, -2xy]] / (x^2+y^2)^2
  H^2    = I / (x^2+y^2)^2              -> eigenvalues +-1/L^2, operator norm EXACTLY 1/L^2
  u^T H u = 0 for the radial unit u     -> radial second derivative of theta vanishes
"""
import math, sys
sys.stdout.reconfigure(encoding='utf-8', errors='replace')

def theta(x, y):
    return math.atan2(y, x)

def grad(x, y):
    q = x*x + y*y
    return (-y/q, x/q)

def hess(x, y):
    q = x*x + y*y
    return [[2*x*y/q**2, (y*y - x*x)/q**2],
            [(y*y - x*x)/q**2, -2*x*y/q**2]]

print('=== exact Hessian identity at sample points ===')
for (x, y) in [(0.3, 0.12), (-0.2, 0.4), (0.5, -0.3), (0.01, 0.7)]:
    L = math.hypot(x, y)
    H = hess(x, y)
    # H^2
    H2 = [[sum(H[i][k]*H[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
    target = 1.0 / (x*x + y*y)**2
    err = max(abs(H2[i][j] - (target if i == j else 0.0)) for i in range(2) for j in range(2))
    # eigenvalues
    tr = H[0][0] + H[1][1]
    det = H[0][0]*H[1][1] - H[0][1]*H[1][0]
    disc = math.sqrt(max(0.0, (tr/2)**2 - det))
    ev = (tr/2 + disc, tr/2 - disc)
    # radial quadratic form
    u = (x/L, y/L)
    uhu = sum(u[i]*H[i][j]*u[j] for i in range(2) for j in range(2))
    print(f'  (x,y)=({x:+.2f},{y:+.2f}) L={L:.6f}: |H^2 - I/L^4| = {err:.2e}  '
          f'eig=({ev[0]:+.6f},{ev[1]:+.6f}) 1/L^2={1/L**2:.6f}  u^T H u = {uhu:+.2e}')

print('\n=== is the angle 2-homogeneous? (my r20 claim) ===')
x, y = 0.3, 0.12
for s in (0.5, 1.0, 2.0):
    print(f'  theta({s}x,{s}y) - theta(x,y) = {theta(s*x, s*y) - theta(x, y):+.3e}   '
          f'(0 => degree 0, NOT degree 2)')

print('\n=== radial second derivative of the angle, done directly ===')
# alpha(t) = theta(X0 + t*u) with u a fixed unit direction: alpha'' = u^T H u = 0
x0, y0 = 0.3, 0.12
u = (math.cos(0.7), math.sin(0.7))
for t in (0.2, 0.45):
    for h in (1e-3, 1e-4):
        fp = theta(x0 + (t+h)*u[0], y0 + (t+h)*u[1])
        f0 = theta(x0 + t*u[0], y0 + t*u[1])
        fm = theta(x0 + (t-h)*u[0], y0 + (t-h)*u[1])
        d2 = (fp - 2*f0 + fm)/h**2
        print(f'  t={t} h={h}: numeric d2(alpha)/dt2 = {d2:+.6e}  (exact 0)')
    H = hess(x0 + t*u[0], y0 + t*u[1])
    uhu = sum(u[i]*H[i][j]*u[j] for i in range(2) for j in range(2))
    print(f'    u^T H u = {uhu:+.3e}')

print('\n=> CORRECT: Hess norm is exactly 1/L^2 (my 2/L^2 was wrong); the radial second')
print('   derivative of theta is exactly 0 (my 2*alpha/L^2 was wrong). The radial lower bound')
print('   2(beta1+beta2) - c2/L2 - a2/L2^2 therefore needs NO angular correction: along the')
print('   radial ray the angle term contributes exactly 0 to the second derivative.')
print()
print('=== the inequality direction: |y -+ d/2| <= L_j (not =) ===')
print('  L1^2 = x^2 + (y-d/2)^2 and L2^2 = x^2 + (y+d/2)^2 are identities; the CONSTRAINTS are')
print('  |y - d/2| <= L1 <= .76 and |y + d/2| <= L2 <= .76, giving |y| + d/2 <= .76.')
