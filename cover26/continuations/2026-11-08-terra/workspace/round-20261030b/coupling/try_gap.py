import math
for b in range(14,27):
 r=.23;t=math.pi/b;g=t-math.sin(t)*math.cos(t)+math.sin(t)*math.sqrt(r*r-math.sin(t)**2);v=(50-b)*3*math.sqrt(3)/4*r*r+b*r*r/2+b*g;print(b,'gap',round(math.pi-v,6),'defect',round(b/2*.0388*r*r,6))
