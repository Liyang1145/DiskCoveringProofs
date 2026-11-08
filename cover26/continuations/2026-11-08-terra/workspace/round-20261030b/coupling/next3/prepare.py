from pathlib import Path
p=Path('research-2026/n26-terra/round-20261030b/coupling');s=(p/'next2/verify_ear_area.py').read_text(encoding='utf8')
s=s.replace('R = F(228081, 1000000)','R = F(228151, 1000000)').replace('TARGET = F(2851, 12500)','TARGET = F(4563, 20000)').replace('F(27,1000)*owners','F(59,2000)*owners')
a=s.index('# Two-edge ear bound');b=s.index('SQRT3_HI =',a)
s=s[:a]+'''# Two-edge ear: Young with w=3/8 bounds two cases at s=8/5.
w3=F(3,8); s0=F(8,5)
first=1/(2*w3)+(F(1,2)+w3/2-1/(8*w3))*s0*s0
second=3/(4*w3)+s0/2+F(3,4)*(w3-1/(4*w3))*s0*s0
assert first==second==F(56,25)
assert F(1,2)+F(3,4)*(w3-1/(4*w3))*2*s0 < 0
assert F(3,4)*F(433,250)+1-F(56,25) == F(59,1000)
''' + s[b:]
s=s.replace('two-edge defect > 54/1000','two-edge defect > 59/1000').replace('r0=2851/12500, U=228081/1000000','r0=4563/20000, U=228151/1000000')
(p/'next3/verify_coupled_ear.py').write_text(s,encoding='ascii')
