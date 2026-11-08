from fractions import Fraction as F
U=F(234700091,10**9);lo=F(3141592653589793,10**15*14);hi=F(3141592653589794,10**15*14)
s=lo-lo**3/6+lo**5/120-lo**7/5040; c=1-hi**2/2+hi**4/24-hi**6/720; h=F(7463,100000); root3=F(1732051,1000000)
assert s>0 and c>0 and h*h>=U*U-s*s and root3*root3>3
cross=2*(14*s*c-14*(hi-hi**3/6+hi**5/120)*h-36*3*root3*U*U/4)
print(float(cross),cross>F(9,20)); print('h',float(h),'s',float(s))



