import json, io, math
D=json.load(io.open(r'C:\Users\袁力阳\Desktop\ai4math2\n11\upper\certified_object.json',encoding='utf-8-sig'))
C=[[int(a)/1e17,int(b)/1e17] for a,b in D['centers_scaled_1e17']]
R=0.3799838531198387090485181795734298538115979028573
rings=[1,3,4,5,6,7,8,9,10]
order=[1,7,3,8,5,4,6,9,10]   # angular order from earlier
print("ring angular order & geometry")
def ang(c): return math.atan2(c[1],c[0])
for i in order:
    c=C[i]; s=math.hypot(*c)
    # arc half-width of bd(D) covered
    cosw=(1+s*s-R*R)/(2*s)
    w=math.acos(max(-1,min(1,cosw)))
    print('disk %2d  s=%.15f  arg=%+.12f  halfwidth w=%.12f (deg %.9f)  sqrt(1-R^2)=%.15f'%(i,s,ang(c),w,math.degrees(w),math.sqrt(1-R*R)))
print()
print("gap between consecutive ring angles (deg), and w_i+w_{i+1}")
tot=0
for a in range(9):
    i=order[a]; j=order[(a+1)%9]
    da=(ang(C[j])-ang(C[i]))%(2*math.pi)
    si=math.hypot(*C[i]); sj=math.hypot(*C[j])
    wi=math.acos(max(-1,min(1,(1+si*si-R*R)/(2*si)))); wj=math.acos(max(-1,min(1,(1+sj*sj-R*R)/(2*sj))))
    print('(%2d,%2d) gap=%.12f deg  w_i+w_j=%.12f  w_i+w_j-gap=%+.3e'%(i,j,math.degrees(da),wi+wj,wi+wj-da))
print()
print("hub 0 radius", math.hypot(*C[0]), " hub 2 radius", math.hypot(*C[2]), " |h0-h2|", math.hypot(C[0][0]-C[2][0],C[0][1]-C[2][1]))
print("1-2R =",1-2*R)
