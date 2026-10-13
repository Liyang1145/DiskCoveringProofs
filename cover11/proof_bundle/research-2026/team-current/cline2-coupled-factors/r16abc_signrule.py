"""cline2-coupled-factors R16abc: decisive numeric test of the residual sign rule.

The lead now states: positive residual = OUTSIDE the disk = ILLEGAL  (reversing their
earlier "positive-distance residual must be ILLEGAL" phrasing is not the same statement --
one is about the residual's SIGN, the other about the distance being POSITIVE).

This script settles it with numbers that admit no interpretation:
  * take the exact identity |x-D1|^2 - r^2 = H(H - cap1);
  * choose H > cap1 and H < cap1 and report, for each, the ACTUAL distance |x-D1| vs r;
  * report what the lead's filter does with each point (accept vs reject).
"""
import math
from mpmath import mp
mp.dps = 30

r = mp.mpf('0.377')
b1 = mp.mpf('1.008')
b2 = mp.mpf('1.001')
delta = mp.mpf('-0.32')

D1 = (r*mp.sin(2*b1), -r*mp.cos(2*b1))
D2 = (r*mp.sin(2*b2), r*mp.cos(2*b2))
s = mp.sqrt(1-r*r)
cap1 = 2*r*mp.sin(2*b1-delta)
cap2 = 2*r*mp.sin(2*b2+delta)
print(f'r={float(r)} b1={float(b1)} b2={float(b2)} delta={float(delta)}')
print(f'D1=({float(D1[0]):+.9f},{float(D1[1]):+.9f})   |D1|={float(mp.sqrt(D1[0]**2+D1[1]**2)):.9f} (r)')
print(f'D2=({float(D2[0]):+.9f},{float(D2[1]):+.9f})   |D2|={float(mp.sqrt(D2[0]**2+D2[1]**2)):.9f} (r)')
print(f'cap1 = 2r sin(2b1-delta) = {float(cap1):.9f}')
print(f'cap2 = 2r sin(2b2+delta) = {float(cap2):.9f}')
print()
print(f'{"H":>10s} {"H-cap1":>12s} {"H(H-cap1)":>14s} {"|x-D1|":>12s} {"|x-D1|-r":>12s} '
      f'{"INSIDE disk1?":>14s} {"lead filter":>12s}')
for H in (cap1-mp.mpf('0.05'), cap1-mp.mpf('0.01'), cap1,
          cap1+mp.mpf('0.01'), cap1+mp.mpf('0.05')):
    x = (H*mp.cos(delta), H*mp.sin(delta))
    d1 = mp.sqrt((x[0]-D1[0])**2+(x[1]-D1[1])**2)
    resid = H*(H-cap1)
    inside = d1 < r
    # the lead's filter: accept iff H <= cap1 and H <= cap2 and norm ok
    norm = H*H-2*s*mp.cos(delta)*H+2*r*(1-r)
    accept = (H <= cap1) and (H <= cap2) and (norm <= 0) and H > 0
    print(f'{float(H):10.6f} {float(H-cap1):12.6f} {float(resid):14.9f} {float(d1):12.9f} '
          f'{float(d1-r):12.9f} {str(inside):>14s} '
          f'{("ACCEPT (legal)" if accept else "REJECT (illegal)"):>12s}')

print()
print('CONCLUSION from the numbers above:')
for H in (cap1-mp.mpf('0.01'), cap1+mp.mpf('0.01')):
    x = (H*mp.cos(delta), H*mp.sin(delta))
    d1 = mp.sqrt((x[0]-D1[0])**2+(x[1]-D1[1])**2)
    resid = H*(H-cap1)
    print(f'  H={float(H):.6f}: residual {float(resid):+.9f};  |x-D1| = {float(d1):.9f} '
          f'vs r = {float(r):.9f}  ->  the hub is '
          f'{"INSIDE" if d1 < r else "OUTSIDE"} disk1;  '
          f'sign(residual) = {"+" if resid > 0 else "-"}')
print()
print('i.e.  positive residual  <=>  OUTSIDE disk1  <=>  |x-D1| > r.')
print('The identity |x-D1|^2 - r^2 = H(H-cap1) is verified to 1e-41 elsewhere, and the')
print('sign of the LEFT side is by definition the sign of |x-D1| - r, so this is not a')
print('convention question: a positive disk residual means the point is outside the disk.')
