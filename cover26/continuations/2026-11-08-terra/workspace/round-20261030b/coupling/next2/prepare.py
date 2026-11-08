from pathlib import Path
p=Path('research-2026/n26-terra/round-20261030b/coupling');s=(p/'next/verify_joint_area.py').read_text(encoding='utf8');s=s.replace('R = F(22781, 100000)','R = F(45611, 200000)').replace('TARGET = F(1139, 5000)','TARGET = F(4561, 20000)').replace('F(19,1000)*owners','F(53,2000)*owners')
a=s.index('SQRT3_HI =');s=s[:a]+"# Two-edge ear bound via averaging the two pairwise inequalities.\nw2=F(2,5); a2=1/(4*w2)-w2; K=F(3,4)/w2+1/(12*a2)\nassert K==F(485,216)\nassert F(3,4)*F(433,250)+1-K > F(53,1000)\n"+s[a:]
s=s.replace("print('PASS: edge-face constant C=147325/83694; per-edge defect > 19/500 U^2')","print('PASS: single-edge defect > 19/500 U^2; two-edge defect > 53/1000 U^2')").replace("print('PASS: r0=1139/5000, U=22781/100000; all b=14,...,26')","print('PASS: r0=4561/20000, U=45611/200000; all b=14,...,26')")
(p/'next2/verify_ear_area.py').write_text(s,encoding='utf8')
