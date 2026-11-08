from pathlib import Path
p=Path(__file__).resolve().parent
for name in ['independent_atan.py','independent_atan_2_9.py']:
 f=p/name;s=f.read_text(encoding='utf8')
 s=s.replace("if not __debug__: raise RuntimeError('Assertions must be enabled')", """if not __debug__: raise RuntimeError('Assertions must be enabled')
# Machin formula and alternating series, proving the only pi bounds used below.
def arctan_inverse_interval(q, n=30):
 s=sum((F((-1)**j,(2*j+1)*q**(2*j+1)) for j in range(n)),F(0))
 e=F(1,(2*n+1)*q**(2*n+1))
 return (s,s+e) if n%2==0 else (s-e,s)
a,b=arctan_inverse_interval(5),arctan_inverse_interval(239)
pi_lo,pi_hi=16*a[0]-4*b[1],16*a[1]-4*b[0]
assert F(333,106)<pi_lo<pi_hi<F(355,113)
""")
 s=s.replace("print('max score <',float(maximum),'margin >',float(margin))", "print('Exact rational checks: weighted maximum < 100269 and margin > 24700')\nassert maximum < 100269 and margin > 24700" if '2_9' in name else "print('Exact rational checks: weighted maximum < 100301 and margin > 67500')\nassert maximum < 100301 and margin > 67500")
 f.write_text(s,encoding='utf8')
