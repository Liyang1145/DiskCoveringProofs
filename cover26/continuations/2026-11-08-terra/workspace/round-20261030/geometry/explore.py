import math
u=.234700091
a=math.asin(u);d0=math.pi-13*a;t=math.pi/14
h=math.sqrt(u*u-math.sin(t)**2)
print(a,d0,t,h)
print('required switch area',math.pi-(36*3*math.sqrt(3)/4*u*u+14*(math.sin(t)*h+t-math.sin(t)*math.cos(t))))
print('generic switch bound',14*u*u/2)
