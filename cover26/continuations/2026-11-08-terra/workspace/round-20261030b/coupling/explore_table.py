import math
r=.225; a=math.asin(r)
for d in [.8,.8125,.825,.8375,.85,.875,.9,.925]:
 t=math.acos((1+d*d-r*r)/(2*d))
 out=[]
 for B in [15,16]:
  k=math.floor((math.pi-B*t)/(a-t))+1
  out.append(max(0,k))
 print(d,'theta',t,'B15,16',out,'middle',d-r)
