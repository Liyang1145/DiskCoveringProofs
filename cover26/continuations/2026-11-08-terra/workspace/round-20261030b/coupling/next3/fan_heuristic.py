import math
r=.23; b=17; d=math.pi/b; s=math.sin(d);c=math.cos(d);h=math.sqrt(r*r-s*s);L=2*(c-h)*s;x=L/r;f=x/2+x*math.sqrt(1-x*x/4);M=.5+3*math.sqrt(3)/4
print('equal angles, both fan-max ideal centers:', 'delta',d,'x',x,'joint_deficit_ratio',M-f,'total_if_distinct_per_b',b*(M-f)*r*r)
print('Only exploratory; face multiplicity can halve debit and choosing slacks may lower')
