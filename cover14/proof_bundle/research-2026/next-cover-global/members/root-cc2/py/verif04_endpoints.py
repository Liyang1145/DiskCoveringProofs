"""root-cc2: are the certificate endpoints exact rationals, and what are they exactly?"""
import sys
from pathlib import Path
import mpmath as mp
from mpmath import iv

mp.mp.dps = 60
iv.dps = 60

for lit in ('0.326813068949914', '0.326823068949914', '0.331732034276234'):
    a = mp.mpf(lit)
    print('literal', lit)
    print('   mp.mpf(lit)  =', mp.nstr(a, 45))
    print('   == mp.mpf(lit)?', a == mp.mpf(lit))
    print('   == mp.mpf(mp.nstr(a,60))?', a == mp.mpf(mp.nstr(a, 60)))
    # is it a dyadic rational? mpf = man * 2^exp with 53-bit man
    man, exp = a._mpf_[1], a._mpf_[2]
    print('   dyadic: man=%d exp=%d  value=man*2^exp' % (man, exp))
    print('   exact decimal of the dyadic =', mp.nstr(mp.mpf(man) * mp.mpf(2)**exp, 45))
    # interval built from the decimal STRING
    try:
        b = iv.mpf(lit)
        print('   iv.mpf(lit) = [%s, %s]' % (b.a.a, b.b.b))
        print('   contains mp.mpf(lit)?', b.a.a <= a <= b.b.b)
    except Exception as ex:
        print('   iv.mpf(lit) failed:', ex)
    # interval built from two mpf endpoints
    b2 = iv.mpf([mp.mpf(lit), mp.mpf(lit)])
    print('   iv.mpf([mpf,mpf]) = [%s, %s]' % (b2.a.a, b2.b.b))
