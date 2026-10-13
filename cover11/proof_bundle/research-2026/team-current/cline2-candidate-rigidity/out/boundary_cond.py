import json, io, math
D=json.load(io.open(r'C:\Users\袁力阳\Desktop\ai4math2\n11\upper\certified_object.json',encoding='utf-8-sig'))
C=[[int(a)/1e17,int(b)/1e17] for a,b in D['centers_scaled_1e17']]
R=0.3799838531198387090485181795734298538115979028573
rings=[1,3,4,5,6,7,8,9,10]
A=[(math.atan2(C[i][1],C[i][0])%(2*math.pi),i) for i in rings]
A.sort()
print('=== boundary condition: w_i + w_{i+1} - gap_i  (should be 0 iff both spokes tight) ===')
print('idx  i     j     gap(rad)   w_i        w_j        sum-gap')
for k in range(9):
    a=A[k][0]; i=A[k][1]; j=A[(k+1)%9][1]
    b=(A[(k+1)%9][0]-a)
    if b<0: b+=2*math.pi
    si=math.hypot(*C[i]); sj=math.hypot(*C[j])
    wi=math.acos(max(-1,min(1,(1+si*si-R*R)/(2*si)))); wj=math.acos(max(-1,min(1,(1+sj*sj-R*R)/(2*sj))))
    print('%d  %2d   %2d   %.15f  %.15f  %.15f  %+.6e'%(k,i,j,b,wi,wj,wi+wj-b))
print()
print('sum of gaps', sum([(A[(k+1)%9][0]-A[k][0])%(2*math.pi) for k in range(9)]), 2*math.pi)
print('sum of w', sum([math.acos(max(-1,min(1,(1+math.hypot(*C[i])**2-R*R)/(2*math.hypot(*C[i]))))) for a,i in A]))
